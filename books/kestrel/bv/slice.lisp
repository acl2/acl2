; BV Library: slice
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "logtail")
(include-book "slice-def")
(include-book "kestrel/arithmetic-light/lg-def" :dir :system)
(local (include-book "../arithmetic-light/lg"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/floor-mod-expt"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/integerp"))
(local (include-book "../arithmetic-light/times-and-divide"))
(local (include-book "../arithmetic-light/divide"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "kestrel/arithmetic-light/plus-and-times" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
(local (include-book "unsigned-byte-p"))

;move
(defthm +-of---and-0
  (equal (< (+ (- x) y) 0)
         (< y x))
  :hints (("Goal" :cases ((< (+ (- x) y) 0)))))

;move?  mixes a logop and a bvop
;not clear which form is better
(defthmd logtail-of-bvchop
  (implies (and (natp low)
                (natp n))
           (equal (logtail low (bvchop n x))
                  (bvchop (- n low) (logtail low x))))
  :hints (("Goal" :cases ((< n low)
                          (equal low n))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable logtail bvchop))))

;; (defthmd logtail-of-bvchop
;;   (implies (and (natp size1)
;;                 (natp size))
;;            (equal (logtail size1 (bvchop size i))
;;                   (bvchop (- size size1)
;;                            (logtail size1 i))))
;;   :hints (("Goal" :use (:instance ;logtail-bvchop
;;                         ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm slice-of-0
  (equal (slice high low 0)
         0)
  :hints (("Goal" :in-theory (enable slice))))

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
  :hints (("Goal" :use slice-when-val-is-not-an-integer
           :in-theory (disable slice-when-val-is-not-an-integer))))

(defthmd slice-when-low-is-not-an-integer
  (implies (not (integerp low))
           (equal (slice high low val)
                  (slice high 0 val)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-when-low-is-negative
  (implies (and (< low 0)
                (integerp low)
                (integerp high)
                )
           (equal (slice high low x)
                  (bvchop (+ 1 high (- low)) x)))
  :hints (("Goal" :in-theory (enable slice bvchop))))

(defthm slice-when-indices-are-negative
  (implies (< n 0)
           (equal (slice n n x)
                  (slice 0 0 x)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-too-high-is-0
  (implies (unsigned-byte-p low x)
           (equal (slice high low x)
                  0))
  :hints (("Goal" :in-theory (enable slice))))

;; May be cheaper, as it only fires when we have an unsigned-byte-p hyp about X.
(defthm slice-too-high-when-unsigned-byte-p
  (implies (and (unsigned-byte-p free x)
                (<= free low)
                (integerp low))
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

;rename
(defthm unsigned-byte-p-of-slice-gen
  (implies (and (<= (+ 1 high (- low)) n)
                (integerp high)
                (integerp low))
           (equal (unsigned-byte-p n (slice high low x))
                  (natp n)))
  :hints (("Goal" :cases ((<= low high))
           :in-theory (e/d (slice) (slice-becomes-bvchop)))))

;drop?
(defthm bvchop-of-slice
  (implies (and (<= n (+ 1 (- high low)))
                (integerp n)
                (integerp high)
                (integerp low)
                )
           (equal (bvchop n (slice high low x))
                  (slice (+ -1 n low) low x)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm bvchop-of-slice-both
  (implies (and (integerp high)
                (integerp low))
           (equal (bvchop n (slice high low x))
                  (if (natp n)
                      (if (<= n (+ 1 (- high low)))
                          (slice (+ -1 n low) low x)
                        (slice high low x))
                    0)))
  :hints (("Goal" :use bvchop-of-slice
           :in-theory (disable bvchop-of-slice))))


(defthm slice-of-bvchop-low
  (implies (and (< high n)
                (natp high)
                (natp low)
                (integerp n))
           (equal (slice high low (bvchop n x))
                  (slice high low x)))
  :hints (("Goal" :cases ((and (<= low high) (integerp x))
                          (and (<= low high) (not (integerp x)))
                          (and (not (<= low high)) (not (integerp x))))
           :in-theory (enable slice logtail-of-bvchop))))

(defthm slice-of-bvchop-tighten
  (implies (and (<= n high)
                ;; (<= low high)
                ;; (<= low n)
                (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (bvchop n x))
                  (slice (+ -1 n) low x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable slice logtail-of-bvchop))))

;maybe just use slice-of-bvchop-tighten?
(defthm slice-of-bvchop-too-high
  (implies (and (<= n low)
                ;; (natp n)
                (natp low)
                ;;(natp high)
                )
           (equal (slice high low (bvchop n x))
                  0))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable slice))))

(defthm slice-of-bvchop-low-gen
  (implies (and (natp high)
                (natp low)
                (integerp n))
           (equal (slice high low (bvchop n x))
                  (if (< high n)
                      (slice high low x)
                    (if (and ;(<= n high)
                             (<= low n))
                        (slice (+ -1 n) low x)
                      0)))))

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

;; Puts the bvchop inside the logtail
(defthmd slice-alt-def
  (implies (and (natp low)
                (natp high))
           (equal (slice high low x)
                  (logtail low (bvchop (+ 1 high) x))))
  :hints (("Goal" :in-theory (enable logtail-of-bvchop-becomes-slice))))

(defthm slice-of-logtail
  (implies (and (natp high)
                (natp low)
                (natp n))
           (equal (slice high low (logtail n x))
                  (slice (+ high n) (+ low n) x)))
  :hints (("Goal" ; :expand (slice highbit lowbit x)
           :in-theory (e/d (slice) (slice-becomes-bvchop)))))

(defthmd bvchop-of-logtail
  (equal (bvchop n (logtail m x))
         (if (natp m)
             (if (natp n)
                 (logtail m (bvchop (+ m n) x))
               0)
           (bvchop n x)))
  :hints (("Goal"
           :cases ((integerp x))
           :in-theory (enable logtail-of-bvchop))))

(theory-invariant (incompatible (:rewrite logtail-of-bvchop) (:rewrite bvchop-of-logtail)))

(defthmd bvchop-of-logtail-becomes-slice
  (implies (natp size1)
           (equal (bvchop size1 (logtail size2 x))
                  (slice (+ -1 size1 (nfix size2)) (nfix size2) x)))
  :hints(("Goal" :in-theory (e/d (slice) (slice-becomes-bvchop)))))

(theory-invariant (incompatible (:definition slice) (:rewrite bvchop-of-logtail-becomes-slice)))

(defthm slice-of-slice
  (implies (and (integerp high1)
                (natp high2)
                (natp low2)
                (natp low1))
           (equal (slice high1 low1 (slice high2 low2 x))
                  (slice (min (+ low2 high1) high2) (+ low1 low2) x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable slice bvchop-of-logtail))))

(defthmd slice-too-high-helper
  (implies (and (< x (expt 2 low))
                (natp low)
                (natp x))
           (equal (slice high low x)
                  0))
  :hints (("Goal"
           :use slice-too-high-is-0
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
  :hints (("Goal" :use slice-too-high-helper
           :in-theory (disable slice-too-high-helper))))

(defthm slice-upper-bound-linear
  (implies (and (<= low high)
                (integerp high)
                (integerp low))
           (<= (slice high low x) (+ -1 (expt 2 (+ 1 high (- low))))))
  :rule-classes :linear
  :hints (("Goal" :use (:instance unsigned-byte-p-of-slice-gen (n (+ 1 high (- low))))
           :cases ((integerp (expt 2 (+ 1 high (- low))))) ;yuck!
           :in-theory (e/d (unsigned-byte-p)
                           (unsigned-byte-p-of-slice-gen)))))

;; Disabled since we have the other
(defthmd slice-upper-bound-linear-constant-version
  (implies (and (syntaxp (and (quotep high)
                              (quotep low)))
                (<= low high)
                (integerp high)
                (integerp low))
           (<= (slice high low x) (+ -1 (expt 2 (+ 1 high (- low))))))
  :rule-classes :linear)

(defthm <-of-slice-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep high)
                              (quotep low)))
                (< (+ -1 (expt 2 (+ 1 high (- low)))) k)
                (integerp high)
                (integerp low)
                (<= low high))
           (< (slice high low x) k))
  :hints (("Goal" :use slice-upper-bound-linear
           :in-theory (disable slice-upper-bound-linear))))

(defthmd logtail-becomes-slice
  (implies (and (unsigned-byte-p m x) ;m is a free var
                (< n m)
                ;; (integerp m);could drop
                (natp n))
           (equal (logtail n x)
                  (slice (+ -1 m) n x)))
  :hints (("Goal"
           :in-theory (e/d (slice) (slice-becomes-bvchop)))))

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
                            ) (<-of-logtail-arg2)))))

(defthm slice-of-expt
  (implies (and (< high size) ;gen?
                (integerp high)
                (natp low)
                (integerp size))
           (equal (slice high low (expt 2 size))
                  0))
  :hints (("Goal" :in-theory (enable slice))))


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
  :hints (("Goal" :in-theory (enable slice bvchop-of-logtail))))

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
  :hints (("Goal" :use slice-subst-in-constant
           :in-theory (disable slice-subst-in-constant))))

(defthm <-of-slice-same
  (implies (and (integerp x)
                (<= low high)
                (posp low) ;gen?
                (integerp high))
           (equal (< (slice high low x) x)
                  (< 0 x)))
  :hints (("Goal" :cases ((< 0 X))
           :in-theory (enable slice))))



;; In case we don't turn slice into getbit
(defthm bitp-of-slice-same-type
  (bitp (slice n n x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-of-mod-of-expt
  (implies (and (< high j)
                (integerp j)
                (natp high)
                ;;(natp low)
                (<= 0 low))
           (equal (slice high low (mod i (expt 2 j)))
                  (slice high low i)))
  :hints (("Goal" :in-theory (enable slice bvchop-of-logtail))))

(defthm equal-of-logtail-and-slice
  (implies (and (unsigned-byte-p (+ 1 high) x)
                (natp high)
                (natp low))
           (equal (equal (logtail low x) (slice high low x))
                  t))
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-of-+-of--1-and-expt-same
  (implies (and (natp low)
                (natp high))
           (equal (slice high low (+ -1 (expt 2 low)))
                  0))
  :hints (("Goal" :in-theory (enable slice))))

;some way to automate this kind of reasoning?
(defthmd slice-leibniz
  (implies (and (equal high1 high2)
                (equal low1 low2)
                (equal x1 x2))
           (equal (equal (slice high1 low1 x1) (slice high2 low2 x2))
                  t)))

(defthmd bvchop-of-floor-of-expt-of-2
  (implies (and (integerp x) ;would like to drop this..
                (integerp n)
                (natp m))
           (equal (bvchop n (floor x (expt 2 m)))
                  (slice (+ m -1 n) m x)))
  :hints (("Goal" :in-theory (e/d (slice logtail) (;anti-slice
                                                   )))))

(theory-invariant (incompatible (:rewrite bvchop-of-floor-of-expt-of-2) (:definition slice)))

(defthmd bvchop-of-floor-of-expt-of-2-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (integerp x)
                (integerp n)
                (power-of-2p k))
           (equal (bvchop n (floor x k))
                  (slice (+ (lg k) -1 n) (lg k) x)))
  :hints (("Goal" :use (:instance bvchop-of-floor-of-expt-of-2 (m (lg k)))
           :in-theory (e/d (power-of-2p) (bvchop-of-floor-of-expt-of-2)))))


(theory-invariant (incompatible (:rewrite bvchop-of-floor-of-expt-of-2-constant-version) (:definition slice)))

(defthmd slice-same-when-not-0
  (implies (not (equal 0 (slice n n x)))
           (equal (slice n n x) 1))
  :hints (("Goal" :use (:instance usb1-cases (x (slice n n x)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthmd slice-bound-3
  (implies (and (<= (+ -1 (expt 2 (+ 1 high (- low)))) k)
            ;    (<= low high)
                (integerp k)
                (natp high)
                (natp low))
           (not (< k (slice high low x))))
  :hints (("Goal" :cases ((<= low high))
           :use (:instance bound-when-usb (x (slice high low x))
                                  (n (+ 1 high (- low))))
           :in-theory (disable bound-when-usb))))

(defthmd slice-bound-3-constant-version
  (implies (and (syntaxp (quotep k))
                (<= (+ -1 (expt 2 (+ 1 high (- low)))) k)
;    (<= low high)
                (integerp k)
                (natp high)
                (natp low))
           (not (< k (slice high low x))))
  :hints (("Goal" :by slice-bound-3)))

(defthm slice-of-times-of-expt
  (implies (and (<= j n)     ;drop?
                (integerp x) ;drop?
                (natp n)
                (natp j)
                (natp m))
           (equal (slice m n (* (expt 2 j) x))
                  (slice (- m j) (- n j) x)))
  :hints (("Goal" :in-theory (e/d (slice logtail EXPT-OF-+ FLOOR-NORMALIZE-DENOMINATOR)
                                  (FLOOR-OF-*-OF-/-AND-1)))))

(defthm slice-of-times-of-expt-alt
  (implies (and (<= j n)     ;drop?
                (integerp x) ;drop?
                (natp n)
                (natp j)
                (natp m))
           (equal (slice m n (* x (expt 2 j)))
                  (slice (- m j) (- n j) x)))
  :hints (("Goal" :use slice-of-times-of-expt
           :in-theory (disable slice-of-times-of-expt))))


(defthm slices-same-when-bvchops-same
  (implies (and (equal (bvchop free x) (bvchop free y))
                (< high free)
                (natp free)
                (natp high)
                (natp low))
           (equal (equal (slice high low x) (slice high low y))
                  t))
  :hints (("Goal" :use ((:instance slice-of-bvchop-low (n free) (x x))
                        (:instance slice-of-bvchop-low (n free) (x y))))))

;move
(defthm slice-of-+-of--1-and-expt
  (implies (and (< high i)
                (posp n)
                (natp low)
                (integerp high)
                (<= low high)
                (natp i)
                )
           (equal (slice high low (+ -1 (expt 2 i)))
                  (+ -1 (expt 2 (+ 1 high (- low))))))
  :hints (("Goal" :in-theory (enable SLICE-ALT-DEF))))

;bozo drop any special cases
(defthm slice-bound
  (implies (and (syntaxp (and (quotep k)
                              (quotep high)
                              (quotep low)))
                (<= (expt 2 (+ 1 high (- low))) k)
                (<= low high) ;bozo
                (natp high)
                (natp low)
                )
           (< (slice high low x) k))
  :hints (("Goal" :use (:instance UNSIGNED-BYTE-P-OF-SLICE-gen (n (+ 1 high (- low))))
           :in-theory (e/d (UNSIGNED-BYTE-P) (UNSIGNED-BYTE-P-OF-SLICE-GEN)))))

(defthm slice-of-+-of-expt-gen
  (implies (and (< high i)
                (integerp x)
                (integerp high)
                (natp low)
                (natp i))
           (equal (slice high low (+ x (expt 2 i)))
                  (slice high low x)))
  :hints (("Goal" :cases ((<= low high))
           :in-theory (enable slice bvchop-of-logtail))))

(defthm *-of-expt-and-slice-same-linear
  (implies (and (<= low high)
                (natp low)
                (natp high)
                (rationalp x))
           (<= (* (expt 2 low) (slice high low x))
               (+ (expt 2 (+ 1 high)) (- (expt 2 low)))))
  :rule-classes ((:linear :trigger-terms ((* (expt 2 low) (slice high low x)))))
  :hints (("Goal" :use slice-upper-bound-linear
           :in-theory (enable expt-of-+))))

;move or make local
(defthm floor-bound-lemma100
  (implies (and (rationalp i)
                (posp j))
           (not (equal (* j (floor i j))
                       (+ i (- j)))))
  :hints (("Goal"
           :use my-floor-lower-bound
           :in-theory (e/d (posp) ( ;FLOOR-BOUNDED-BY-/
                                   )))))


(local
 (defthmd equal-of-slice-helper
   (implies (and (unsigned-byte-p (+ 1 high) x)
                 (natp high)
                 (natp low)
                 (<= low high))
            (equal (equal k (slice high low x))
                   (and (unsigned-byte-p (+ 1 high (- low)) k)
                        (<= (bvchop (+ 1 high) x) (+ -1 (* (+ 1 k) (expt 2 low))))
                        (<= (* k (expt 2 low)) (bvchop (+ 1 high) x)))))
   :hints (("Goal" :in-theory (enable slice logtail)))))

(defthmd equal-of-slice
  (implies (and (<= low high)
                (natp high)
                (natp low))
           (equal (equal k (slice high low x))
                  (and (unsigned-byte-p (+ 1 high (- low)) k)
                       (<= (bvchop (+ 1 high) x) (+ -1 (* (+ 1 k) (expt 2 low))))
                       (<= (* k (expt 2 low)) (bvchop (+ 1 high) x)))))
  :hints (("Goal" :use (:instance equal-of-slice-helper (x (bvchop (+ 1 high) x))))))

(defthm slice-of--1
  (implies (and (<= low high)
                (natp low)
                (natp high))
           (equal (slice high low -1)
                  (+ -1 (expt 2 (+ 1 high (- low))))))
  :hints (("Goal" :in-theory (enable slice))))

(defthm unsigned-byte-p-of-slice-lemma
  (implies (and (unsigned-byte-p (+ n low) x)
                (natp n)
                (natp low)
                (natp high))
           (unsigned-byte-p n (slice high low x)))
  :hints (("Goal" :in-theory (enable slice))))

; todo: replace the other?
(defthm slice-of-logtail-gen
  (implies (and (integerp high)
                (natp low)
                (natp n))
           (equal (slice high low (logtail n x))
                  (if (natp high)
                      (slice (+ high n)
                             (+ low n)
                             x)
                    0))))

(defthm slice-of-expt-same-as-low
  (implies (and (natp low)
                (natp high))
           (equal (slice high low (expt 2 low))
                  (if (<= low high)
                      1
                    0)))
  :hints (("Goal" :in-theory (enable slice))))

;similar to UNSIGNED-BYTE-P-OF-BVCHOP-BIGGER2?
(defthmd slice-too-high-is-0-new
  (implies (and (unsigned-byte-p low (bvchop (+ 1 high) x))
                (integerp high))
           (equal (slice high low x) 0))
  :hints (("Goal" :in-theory (enable slice bvchop-of-logtail))))

(defthm slice-of-ifix
  (equal (slice high low (ifix x))
         (slice high low x))
  :hints (("Goal" :in-theory (enable ifix))))

(defthm not-<-of-slice-and-slice-same-low-and-val
  (implies (and (<= high1 high2)
                (natp high1)
                (natp high2))
           (not (< (slice high2 low x)
                   (slice high1 low x))))
  :hints (("Goal" :cases ((<= low high1))
           :in-theory (enable slice))))

(defthm slice-of-expt-high
  (implies (and (< size low)
                (integerp high)
                (natp low)
                (integerp size))
           (equal (slice high low (expt 2 size))
                  0))
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-of-floor-of-expt
  (implies (and (integerp x)
                (natp low)
                (natp high)
                (natp n))
           (equal (slice high low (floor x (expt 2 n)))
                  (slice (+ high n) (+ low n) x)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm slice-of-floor-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp x)
                (natp low)
                (natp high)
                (natp (lg k)))
           (equal (slice high low (floor x k))
                  (slice (+ high (lg k)) (+ low (lg k)) x)))
  :hints (("Goal" :use (:instance slice-of-floor-of-expt (n (lg k)))
           :in-theory (disable slice-of-floor-of-expt))))

(defthm slice-of-all-ones-too-high
  (implies (and (natp low)
                (natp high)
                ;(<= low high)
                )
           (equal (slice high low (+ -1 (expt 2 low)))
                  0))
  :hints (("Goal" :in-theory (enable slice))))

;; restrict?
(defthmd slice-of-if-arg3
  (equal (slice high low (if test v1 v2))
         (if test
             (slice high low v1)
           (slice high low v2))))
