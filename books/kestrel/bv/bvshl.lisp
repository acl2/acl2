; Left shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(local (include-book "bvcat"))

;often we will let this open to bvcat
;we expect (<= shift-amount width)
;left shift within a fixed range
;see bvshl-rewrite-with-bvchop for a version that puts a bvchop around x to help us simplify stuff
;; TODO: Consider chopping the shift amount (but what if the width is not a power of 2)?
(defund bvshl (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type (integer 0 *) width)
           (type integer x)
           (xargs :guard (<= shift-amount width)))
  (bvcat (- width shift-amount) x shift-amount 0))

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
  (implies (natp k)
           (equal (bvshl width (bvchop width x) k)
                  (bvshl width x k)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm integerp-of-bvshl
  (integerp (bvshl width x shift-amount)))

(defthm natp-of-bvshl
  (natp (bvshl width x shift-amount))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bvshl))))


;bozo shouldn't need the first 2 hyps?
(defthm unsigned-byte-p-of-bvshl
  (implies (and (natp amt)
                (<= amt size)
                (natp size))
           (unsigned-byte-p size (bvshl size x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))

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

;todo: make this like the ones for bvshr and bvashr
(defund bvshl-cases-term-fn-aux (i width)
  (declare (xargs :guard (integerp width)
                  :measure (nfix (+ 1 i))))
  (if (not (posp i))
      `((otherwise (bvshl ,width x 0))) ; covers 0 and all other cases: ensures that a number is always returned
    (cons ;`(,i (bvcat ,(- width i) x ,i 0)) ; or we could just put in a call of bvshl where the shift-amount is a constant, but then we'd need support for bvshl in the STP translation, or an opener rule
     `(,i (bvshl ,width x ,i))
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
