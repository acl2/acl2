; BV Library: slice
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "logtail")
(include-book "slice-def")
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/floor-mod-expt"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/integerp"))
(local (include-book "../bv/unsigned-byte-p"))

;move
(defthm +-of---and-0
  (equal (< (+ (- x) y) 0)
         (< y x))
  :hints (("Goal" :cases ((< (+ (- x) y) 0)))))

(defthm slice-of-0
  (equal (slice high low 0)
         0)
  :hints (("Goal" :in-theory (enable slice))))

(defthm integerp-of-slice
  (integerp (slice high low x)))

(defthm natp-of-slice
  (natp (slice high low x)))

;disable?
(defthm slice-when-val-is-not-an-integer
  (implies (not (integerp val))
           (equal (slice high low val)
                  0))
  :hints (("Goal" :in-theory (enable slice logtail))))

(defthm slice-when-val-is-not-an-integer-cheap
  (implies (not (integerp val))
           (equal (slice high low val)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :use (:instance slice-when-val-is-not-an-integer)
           :in-theory (disable slice-when-val-is-not-an-integer))))

(defthm slice-too-high-is-0
  (implies (unsigned-byte-p low x)
           (equal (slice high low x)
                  0))
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-becomes-bvchop
  (equal (slice n 0 x)
         (bvchop (+ 1 (ifix n)) x))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable slice))))

(defthm slice-out-of-order
  (implies (and (< high low)
                (integerp low)
                (integerp high))
           (equal (slice high low x)
                  0))
  :hints (("Goal" :in-theory (enable slice))))

(defthm bvchop-of-slice
  (implies (and (<= n (+ 1 (- high low)))
                (integerp n)
                (integerp high)
                (integerp low)
                )
           (equal (bvchop n (slice high low x))
                  (slice (+ -1 n low) low x)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm logtail-of-bvchop
  (implies (and (natp low)
                (natp n))
           (equal (logtail low (bvchop n x))
                  (bvchop (- n low) (logtail low x))))
  :hints (("Goal" :cases ((< n low)
                          (equal low n))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable logtail bvchop))))

(defthm slice-of-bvchop-low
  (implies (and (< high n)
                (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (bvchop n x))
                  (slice high low x)))
  :hints (("Goal" :cases ((and (<= low high) (integerp x))
                          (and (<= low high) (not (integerp x)))
                          (and (not (<= low high)) (not (integerp x))))
           :in-theory (enable slice))))

(defthm slice-of-bvchop-tighten
  (implies (and (<= n high)
                ;; (<= low high)
                (<= low n)
                (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (bvchop n x))
                  (slice (+ -1 n) low x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable slice))))

(defthm slice-of-bvchop-too-high
  (implies (and (<= n n2)
                (natp n)
                (natp n2)
                (natp m))
           (equal (slice m n2 (bvchop n x))
                  0))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable slice))))

(defthm slice-of-bvchop-low-gen
  (implies (and (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (bvchop n x))
                  (if (< high n)
                      (slice high low x)
                    (if (and (<= n high)
                             (<= low n))
                        (slice (+ -1 n) low x)
                      0)))))

(defthm unsigned-byte-p-of-slice-gen
  (implies (and (>= n (+ 1 high (- low)))
                (integerp n)
                (integerp high)
                (integerp low))
           (equal (unsigned-byte-p n (slice high low x))
                  (<= 0 n)))
  :hints
  (("Goal" :cases ((<= low high))
    :in-theory (e/d (slice) (slice-becomes-bvchop)))))

(defthm slice-when-low-is-negative
  (implies (and (< low 0)
                (integerp low)
                (integerp high)
                )
           (equal (slice high low x)
                  (bvchop (+ 1 high (- low)) x)))
  :hints (("Goal" :in-theory (enable slice bvchop))))

(defthmd unsigned-byte-p-of-slice-helper
  (implies (and (equal n (+ 1 high (- low)))
                (<= low high) ;todo
                (natp high)
                (natp low))
           (UNSIGNED-BYTE-P n (SLICE high low x)))
  :hints (("Goal" ;:cases ( (< high low))
           :in-theory (e/d (SLICE) (SLICE-BECOMES-BVCHOP)))))

(defthmd unsigned-byte-p-of-slice
  (implies (and (equal n (+ 1 high (- low)))
                (integerp high)
                (integerp low))
           (equal (unsigned-byte-p n (slice high low x))
                  (natp n)))
  :hints (("Goal" :use (SLICE-OUT-OF-ORDER
                        (:instance unsigned-byte-p-of-slice-helper))
           :in-theory (e/d (natp) (unsigned-byte-p-of-slice-helper SLICE-OUT-OF-ORDER)))))

(defthm bvchop-of-slice-both
  (implies (and (integerp high)
                (integerp low))
           (equal (bvchop n (slice high low x))
                  (if (natp n)
                      (if (<= n (+ 1 (- high low)))
                          (slice (+ -1 n low) low x)
                        (slice high low x))
                    0)))
  :hints (("Goal" :use (:instance bvchop-of-slice)
           :in-theory (disable bvchop-of-slice))))

(in-theory (disable logtail-of-bvchop))

;; (defthmd logtail-of-bvchop
;;   (implies (and (natp size1)
;;                 (natp size))
;;            (equal (logtail size1 (bvchop size i))
;;                   (bvchop (- size size1)
;;                            (logtail size1 i))))
;;   :hints (("Goal" :use (:instance ;logtail-bvchop
;;                         ))))

;newly disabled..
(defthmd logtail-of-bvchop-becomes-slice
  (implies (and (integerp n)
                (natp m))
           (equal (logtail m (bvchop n x))
                  (slice (+ -1 n) m x)))
  :hints (("Goal"
           :cases ((<= 0 n))
           :in-theory (e/d (slice natp logtail-of-bvchop)
                           (slice-becomes-bvchop)))))

(theory-invariant (incompatible (:definition slice) (:rewrite logtail-of-bvchop-becomes-slice)))

(defthm slice-of-logtail
  (implies (and (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (logtail n x))
                  (slice (+ high n) (+ low n) x)))
  :hints (("Goal" ; :expand (slice highbit lowbit x)
           :in-theory (e/d (slice) (slice-becomes-bvchop
                                    )))))

(defthmd bvchop-of-logtail
  (equal (bvchop n (logtail m x))
         (if (natp m)
             (if (natp n)
                 (logtail m (bvchop (+ m n) x))
               0)
           (bvchop n x)))
  :hints (("Goal"
           :cases ((integerp x))
           :in-theory (e/d (logtail-of-bvchop) (LOGTAIL-OF-BVCHOP-BECOMES-SLICE)))))

(theory-invariant (incompatible (:rewrite logtail-of-bvchop) (:rewrite bvchop-of-logtail)))

(defthm bvchop-of-logtail-becomes-slice
  (implies (and (natp size1)
                (natp size2))
           (equal (bvchop size1 (logtail size2 x))
                  (slice (+ -1 size1 size2) size2 x)))
  :hints(("Goal" :in-theory (e/d (slice) (slice-becomes-bvchop)))))

(theory-invariant (incompatible (:definition slice) (:rewrite bvchop-of-logtail-becomes-slice)))

(defthm slice-of-slice
  (implies (and (natp n)
                (natp m)
                (natp low)
                (<= (+ low2 -1 low) m) ;todo?
                (<= low2 n)
                (natp low2)
                )
           (equal (slice n low2 (slice m low x))
                  (slice (min (+ low n) m) (+ low2 low) x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (slice bvchop-of-logtail)
                           (logtail-of-bvchop-becomes-slice
                            bvchop-of-logtail-becomes-slice)))))

(defthmd slice-too-high-helper
  (implies (and (< x (expt 2 low))
                (natp low)
                (natp x))
           (equal (slice high low x)
                  0))
  :hints (("Goal"
           :use (:instance slice-too-high-is-0)
           :in-theory (e/d (unsigned-byte-p slice-too-high-is-0) (slice-too-high-is-0)))))

;also a version for <= ?
(defthm slice-too-high-lemma
  (implies (and (< x free)
                (syntaxp (quotep free))
                (<= free (expt 2 low))
                (natp low)
                (natp x))
           (equal (slice high low x)
                  0))
  :hints (("Goal" :use (:instance slice-too-high-helper)
           :in-theory (disable slice-too-high-helper))))

(defthm slice-upper-bound-linear
  (implies (and (syntaxp (and (quotep high)
                              (quotep low)))
                (integerp high)
                (integerp low)
                (<= low high))
           (<= (slice high low x) (+ -1 (expt 2 (+ 1 high (- low))))))
  :rule-classes (:linear)
  :hints (("Goal" :use (:instance unsigned-byte-p-of-slice-gen (n (+ 1 high (- low))))
           :cases ((integerp (expt 2 (+ 1 high (- low))))) ;yuck!
           :in-theory (e/d (unsigned-byte-p)
                           (unsigned-byte-p-of-slice-gen)))))

(defthmd logtail-becomes-slice
  (implies (and (unsigned-byte-p m x) ;m is a free var
                (< n m)
                (integerp m);could drop
                (natp n))
           (equal (logtail n x)
                  (slice (+ -1 m) n x)))
  :hints (("Goal"
           :in-theory (e/d (slice) (slice-becomes-bvchop bvchop-of-logtail-becomes-slice)))))

;enable?
(defthmd slice-monotone
  (implies (and (<= x y) ;expensive?
                (unsigned-byte-p (+ 1 high) x)
                (unsigned-byte-p (+ 1 high) y)
                (natp high)
                (natp low))
           ;rephrase?
           (<= (slice high low x) (slice high low y)))
  :hints (("Goal" :cases ((<= low high))
           :in-theory (e/d (slice ;bvchop
                            ) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm slice-of-expt
  (implies (and (< high size) ;gen?
                (integerp high)
                (natp low)
                (integerp size))
           (equal (slice high low (expt 2 size))
                  0))
  :hints (("Goal" :in-theory (e/d (slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;; (DEFTHM SLICE-OF-SLICE-gen
;;   (IMPLIES (AND (NATP N)
;;                 (NATP M)
;;                 (NATP LOW)
;;                 (<= (+ LOW2 -1 LOW) M)
;; ;                (<= LOW2 N)
;;                 (NATP LOW2))
;;            (EQUAL (SLICE N LOW2 (SLICE M LOW X))
;;                   (if (<= LOW2 N)
;;                       (SLICE (MIN (+ LOW N) M)
;;                              (+ LOW2 LOW)
;;                              X)
;;                     0)))
;;   :hints (("Goal" :cases ((and (equal 0 m) (< 0 low2))
;;                           (and (equal 0 m) (<= low2 0))
;;                           ))))

;fixme get rid of slice-of-slice?
(defthm slice-of-slice-gen-better
  (implies (and (natp n)
                (natp m)
                (natp low)
                (natp low2))
           (equal (slice n low2 (slice m low x))
                  (if (or (< m (+ low2 -1 low))
                          (< n low2))
                      0
                    (slice (min (+ low n) m) (+ low2 low) x))))
  :hints (("Goal" :in-theory (enable slice-too-high-is-0))))

(in-theory (disable slice-of-slice))

(defthm slice-when-bvchop-known
  (implies (and (syntaxp (not (quotep x)))
                (equal free (bvchop freesize x))
                (syntaxp (quotep free))
                (< high freesize)
                (integerp high)
                (natp low)
                (integerp freesize)
                )
           (equal (slice high low x)
                  (slice high low free)))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail)
                                  (bvchop-of-logtail-becomes-slice logtail-of-bvchop-becomes-slice)))))

(defthm slice-subst-in-constant
  (implies (and (syntaxp (not (quotep x)))
                (equal k (slice high2 low2 x)) ;flipped this since constants now come first (TODO: but now it's a binding hyp)
                (syntaxp (quotep k)) ;relax this?  might then loop?
                (<= high high2)
                (<= low2 low)
                (natp low)
                (natp high)
                (natp low2)
                (natp high2))
           (equal (slice high low x)
                  (slice (- high low2) (- low low2) k)))
  :hints (("Goal" :cases ((<= low high)))))

;gross to need both!
(defthm slice-subst-in-constant-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal (slice high2 low2 x) k)
                (syntaxp (quotep k)) ;relax this?  might then loop?
                (<= high high2)
                (<= low2 low)
                (natp low)
                (natp high)
                (natp low2)
                (natp high2))
           (equal (slice high low x)
                  (slice (- high low2) (- low low2) k)))
  :hints (("Goal" :use (:instance slice-subst-in-constant)
           :in-theory (disable slice-subst-in-constant))))

(defthm <-of-slice-same
  (implies (and (integerp x)
                (<= low high)
                (posp low) ;gen?
                (integerp high))
           (equal (< (slice high low x) x)
                  (< 0 x)))
  :hints (("Goal" :cases ((< 0 X))
           :in-theory (e/d (slice)
                           (bvchop-of-logtail-becomes-slice)))))

(defthm slice-when-indices-are-negative
  (implies (< n 0)
           (equal (slice n n x)
                  (slice 0 0 x)))
  :hints (("Goal" :in-theory (e/d (slice)
                                  (bvchop-of-logtail-becomes-slice)))))

;; In case we don't turn slice into getbit
(defthm slice-same-type
  (or (equal 0 (slice n n val))
      (equal 1 (slice n n val)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (slice)
                                  (bvchop-of-logtail-becomes-slice)))))

(defthm slice-of-mod-of-expt
  (implies (and (< high j)
                (integerp j)
                (natp high)
                ;;(natp low)
                (<= 0 low))
           (equal (slice high low (mod i (expt 2 j)))
                  (slice high low i)))
  :hints (("Goal" :in-theory (e/d (slice bvchop-of-logtail)
                                  (bvchop-of-logtail-becomes-slice)))))

(defthm equal-of-logtail-and-slice
  (implies (and (unsigned-byte-p (+ 1 high) x)
                (natp high)
                (natp low))
           (equal (equal (logtail low x) (slice high low x))
                  t))
  :hints (("Goal" :in-theory (e/d (slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

(defthm slice-of-+-of--1-and-expt-same
  (implies (and (natp low)
                (natp high))
           (equal (slice high low (+ -1 (expt 2 low)))
                  0))
  :hints (("Goal" :in-theory (e/d (slice) (acl2::bvchop-of-logtail-becomes-slice)))))

;some way to automate this kind of reasoning?
(defthmd slice-leibniz
  (implies (and (equal high1 high2)
                (equal low1 low2)
                (equal x1 x2))
           (equal (equal (slice high1 low1 x1) (slice high2 low2 x2))
                  t)))
