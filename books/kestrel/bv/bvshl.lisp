; Bit-vector Left shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "slice-def")
(include-book "bvshl-def")
(local (include-book "bvcat"))
(local (include-book "unsigned-byte-p"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(defthm bvshl-of-0-arg1
  (implies (natp amt)
           (equal (bvshl 0 x amt)
                  0))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshl-of-0-arg2
  (equal (bvshl width 0 amt)
         0)
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshl-of-0-arg3
  (equal (bvshl width x 0)
         (bvchop width x))
  :hints (("Goal" :in-theory (enable bvshl))))

;; TODO: allow the widths to differ
(defthm bvshl-of-bvchop
  (equal (bvshl width (bvchop width x) k)
         (bvshl width x k))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm integerp-of-bvshl
  (integerp (bvshl width x shift-amount)))

(defthm natp-of-bvshl
  (natp (bvshl width x shift-amount))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm unsigned-byte-p-of-bvshl
  (implies (natp size)
           (unsigned-byte-p size (bvshl size x amt)))
  :hints (("Goal" :cases ((<= amt size))
           :in-theory (enable bvshl))))

(defthm unsigned-byte-p-of-bvshl-gen
  (implies (and (<= size size2)
                (integerp size2)
                (natp size))
           (unsigned-byte-p size2 (bvshl size x amt)))
  :hints (("Goal" :use unsigned-byte-p-of-bvshl
           :in-theory (disable unsigned-byte-p-of-bvshl))))

;also consider n > size (easy)
(defthm unsigned-byte-p-of-bvshl-other
  (implies (and ;(< n size)
                (<= amt size)
                (natp amt)
                (unsigned-byte-p (- n amt) x)
                (natp n)
                (natp size))
           (unsigned-byte-p n (bvshl size x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshl-upper-bound-linear-strong
  (implies (natp size)
           (<= (bvshl size x amt) (+ -1 (expt 2 size))))
  :rule-classes :linear
  :hints (("Goal" :use unsigned-byte-p-of-bvshl
           :in-theory (e/d (unsigned-byte-p)
                           (unsigned-byte-p-of-bvshl
                            unsigned-byte-p-of-bvshl-gen)))))

; a version that puts a bvchop around x to help us simplify stuff
(defthmd bvshl-rewrite-with-bvchop
  (implies (and (<= shift-amount width)
                (natp shift-amount)
                (integerp width))
           (equal (bvshl width x shift-amount)
                  (bvcat (- width shift-amount) (bvchop (- width shift-amount) x) shift-amount 0)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthmd bvshl-rewrite-for-constant-shift-amount
  (implies (and (syntaxp (quotep shift-amount))
                (syntaxp (quotep width))
                (<= shift-amount width)
                (natp shift-amount)
                (integerp width))
           (equal (bvshl width x shift-amount)
                  (bvcat (- width shift-amount)
                         x
                         shift-amount 0)))
  :hints (("Goal" :in-theory (enable bvshl-rewrite-with-bvchop))))

;i don't think I like the bvchop here... trim rules should take care of that...
(defthmd bvshl-rewrite-with-bvchop-for-constant-shift-amount
  (implies (and (syntaxp (quotep shift-amount))
                (syntaxp (quotep width)) ; will usually be true
                (<= shift-amount width)
                (natp shift-amount)
                (integerp width))
           (equal (bvshl width x shift-amount)
                  (bvcat (- width shift-amount)
                         (bvchop (- width shift-amount) x)
                         shift-amount
                         0)))
  :hints (("Goal" :by bvshl-rewrite-with-bvchop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvshl-cases-term-fn-aux (i width)
  (declare (xargs :guard (integerp width)
                  :measure (nfix (+ 1 i))))
  (if (not (posp i))
      `((otherwise (bvshl ,width x 0))) ; covers 0 and all other cases: ensures that a number is always returned
    (cons `(,i (bvshl ,width x ,i))
          (bvshl-cases-term-fn-aux (+ -1 i) width))))

;; TODO: Consider making a BVIF nest instead of using CASE
(defund bvshl-cases-term-fn (width)
  (declare (xargs :guard (natp width)))
  `(case shift-amount
     ,@(bvshl-cases-term-fn-aux width width)))

(defmacro bvshl-cases-term (width)
  (bvshl-cases-term-fn width))

;pretty gross
(defthmd bvshl-16-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 16))
           (equal (bvshl 16 x shift-amount)
                  (bvshl-cases-term 16)))
  :hints (("Goal" :in-theory (enable bvshl))))

;pretty gross
(defthmd bvshl-32-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 32))
           (equal (bvshl 32 x shift-amount)
                  (bvshl-cases-term 32)))
  :hints (("Goal" :in-theory (enable bvshl))))

;pretty gross
(defthmd bvshl-64-cases
  (implies (and (syntaxp (not (quotep shift-amount)))
                (natp shift-amount)
                (<= shift-amount 64))
           (equal (bvshl 64 x shift-amount)
                  (bvshl-cases-term 64)))
  :hints (("Goal" :in-theory (enable bvshl))))

;gen the size
(defthm equal-of-bvshl-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (natp amt)
                (< amt 32))
           (equal (equal k (bvshl 32 k2 amt))
                  (and (unsigned-byte-p 32 k)
                       (equal 0 (bvchop amt k))
                       (equal (slice 31 amt k)
                              (bvchop (- 32 amt) k2)))))
  :hints (("Goal" :in-theory (e/d (bvshl)
                                  (;bvcat-of-minus-becomes-bvshl
                                   )))))

;todo: gen, or change bvshl to always return a bv, or change the bvchop-identity rule to know about bvshl
;; subsumed by the rule below, but that one can change the size of the bvshl
(defthmd bvchop-of-bvshl-same
  (implies (and (natp size)
                (< amt size)
                (natp amt))
           (equal (bvchop size (bvshl size x amt))
                  (bvshl size x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

;new!
(defthm bvchop-of-bvshl
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2)
                ;(natp amt)
                )
           (equal (bvchop size1 (bvshl size2 x amt))
                  (bvshl size1 x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvchop-of-bvshl-does-nothing
  (implies (and (<= size2 size1)
                (natp amt)
                (integerp size1))
           (equal (bvchop size1 (bvshl size2 x amt))
                  (bvshl size2 x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshl-when-amount-too-big
  (implies (and (<= size shift-amount)
                (integerp shift-amount))
           (equal (bvshl size x shift-amount)
                  0))
  :hints (("Goal" :in-theory (enable bvshl))))
