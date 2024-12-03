; BV Library: Theorems about bvchop.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop-def")
(include-book "../arithmetic-light/power-of-2p")
(local (include-book "unsigned-byte-p"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/times-and-divide"))
(local (include-book "../arithmetic-light/divide"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/mod-and-expt"))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))

;drop?
(in-theory (disable unsigned-byte-p))

;(in-theory (disable BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P)) ;slow
;drop?
(in-theory (disable mod floor))

;for Axe
(defthmd integerp-of-bvchop
  (integerp (bvchop size x))
  :hints (("Goal" :in-theory (enable bvchop))))

;for Axe
(defthmd natp-of-bvchop
  (natp (bvchop n x)))

(defthm bvchop-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (bvchop n x) 0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-when-not-natp-arg1-cheap
  (implies (not (natp n))
           (equal (bvchop n x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-when-i-is-not-an-integer
  (implies (not (integerp i))
           (equal (bvchop size i)
                  0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-with-n-negative
  (implies (<= n 0)
           (equal (bvchop n x)
                  0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-size-0-better
  (equal (bvchop size 0)
         0)
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-upper-bound
  (< (bvchop n x) (expt 2 n))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthmd bvchop-upper-bound-strong
  (implies (natp n)
           (<= (bvchop n x) (+ -1 (expt 2 n))))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-upper-bound-linear
  (< (bvchop n x) (expt 2 n))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-upper-bound-linear-strong
  (implies (natp n)
           (<= (bvchop n x) (+ -1 (expt 2 n))))
  :rule-classes :linear)

(local
 (defthm bvchop-of-bvchop2
   (implies (and (<= 0 size1)
                 (integerp size1)
                 (integerp size)
                 (<= 0 size))
            (equal (bvchop size1 (bvchop size i))
                   (if (< size1 size)
                       (bvchop size1 i)
                     (bvchop size i))))
   :hints (("Goal" :cases ((integerp i))
            :in-theory (enable bvchop mod-of-mod-when-mult)))))

;this one has the advantage of being a "simple" rule
(defthm bvchop-of-bvchop-same
  (equal (bvchop n (bvchop n x))
         (bvchop n x))
  :hints (("Goal" :cases ((natp n) (not (integerp n))))))

(local
 (defthm bvchop-bvchop-better-helper
   (implies (and (>= size1 0)
                 (integerp size1)
                 (>= size 0)
                 (integerp size)
                 )
            (equal (bvchop size1 (bvchop size i))
                   (if (< size1 size)
                       (bvchop size1 i)
                     (bvchop size i))))
   :hints (("Goal" :cases ((integerp i))))))

(defthm bvchop-of-bvchop
  (equal (bvchop size1 (bvchop size i))
         (if (< (ifix size1) (ifix size))
             (bvchop size1 i)
           (bvchop size i)))
  :hints (("Goal" :use (:instance bvchop-bvchop-better-helper (size (ifix size)) (size1 (ifix size1)))
           :in-theory (disable bvchop-bvchop-better-helper))))

;allow the sizes to differ?
;or just use the meta rule...
(defthm bvchop-of-*-of-bvchop
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (* (bvchop size x) y))
                  (bvchop size (* x y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable bvchop))))

(defthm bvchop-of-*-of-bvchop-arg2
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (* x (bvchop size y)))
                  (bvchop size (* x y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable bvchop))))

;rename
(defthm bvchop-+-bvchop-better
  (implies (and (integerp i)
                (integerp j))
           (equal (bvchop size (+ i (bvchop size j)))
                  (bvchop size (+ i j))))
  :hints (("Goal" :in-theory (enable bvchop))))

;might help if natp is not enabled
(defthm bvchop-when-size-is-not-natp
  (implies (not (natp size))
           (equal (bvchop size i)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (bvchop) (;FLOOR-MINUS-ERIC-BETTER ;drop the disable once this is fixed
                                            )))))

(defthm <=-of-bvchop-same-linear
  (implies (<= 0 x)
           (<= (bvchop n x) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable bvchop))))

;; this is listed first so that it is tried after the main rule
(defthm unsigned-byte-p-of-bvchop-when-already
  (implies (unsigned-byte-p size x)
           (unsigned-byte-p size (bvchop size2 x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-bvchop
  (implies (<= size size1)
           (equal (unsigned-byte-p size1 (bvchop size i))
                  (and (>= size1 0)
                       (integerp size1))))
  :hints (("Goal" :in-theory (enable bvchop unsigned-byte-p))))

(defthm bitp-of-bvchop-of-1-type
  (bitp (bvchop 1 x))
  :rule-classes :type-prescription)

;bozo drop any special cases
;rename
(defthm bvchop-bound
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (<= (expt 2 n) k))
           (< (bvchop n x) k))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-bvchop (i x) (size n) (size1 n))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (zip bvchop)
                           (unsigned-byte-p-of-bvchop)))))

;rename
(defthm bvchop-bound-2
  (implies (and (<= (expt 2 size) k)
                (natp size))
           (< (bvchop size x) k)))

;rename
(defthm bvchop-bound-other
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (integerp k)
                (<= (+ -1 (expt 2 n)) k))
           (not (< k (bvchop n x)))))

;rename
(defthm bvchop-bound-lemma
  (implies (posp size)
           (not (< (expt 2 size) (bvchop (+ -1 size) x))))
  :hints (("Goal" :use (:instance bvchop-upper-bound (n (+ -1 size)) (x x))
           :in-theory (disable bvchop-upper-bound bvchop-bound-2))))

;; Do not remove: helps justify the correctness of some operations done by Axe.
(defthm bvchop-of-ifix
  (equal (bvchop size (ifix x))
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer))))

(defthm bvchop-of-0-arg1
  (equal (bvchop 0 i)
         0))

(defthm bvchop-does-nothing-rewrite
  (equal (equal x (bvchop n x))
         (if (natp n)
             (unsigned-byte-p n x)
           (equal 0 x)))
  :hints (("Goal" :in-theory (enable bvchop unsigned-byte-p))))

;rename
(defthm bvchop-shift
  (implies (integerp x)
           (equal (bvchop n (* 2 x))
                  (if (posp n)
                      (* 2 (bvchop (+ -1 n) x))
                    0)))
  :hints (("Goal" :in-theory (enable bvchop mod-expt-split))))

(defthm bvchop-when-i-is-not-an-integer-cheap
  (implies (not (integerp i))
           (equal (bvchop size i)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer))))

;allow the n's to differ
(defthm bvchop-of-expt-2-n
  (equal (bvchop n (expt 2 n))
         0)
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm equal-constant-when-bvchop-equal-constant-false
  (implies (and (syntaxp (quotep const))
                (equal free (bvchop freesize x))
                (syntaxp (quotep free))
                (syntaxp (quotep freesize))
                ;;gets computed:
                (not (equal free (bvchop freesize const))))
           (not (equal const x))))

(defthm bvchop-of-1
  (equal (bvchop n 1)
         (if (zp n)
             0
           1))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthmd bvchop-of-sum-cases
  (implies (and (integerp i2)
                (integerp i1))
           (equal (bvchop size (+ i1 i2))
                  (if (not (natp size))
                      0
                    (if (< (+ (bvchop size i1) (bvchop size i2)) (expt 2 size))
                        (+ (bvchop size i1) (bvchop size i2))
                      (+ (- (expt 2 size)) (bvchop size i1) (bvchop size i2))))))
  :hints (("Goal" :in-theory (enable bvchop mod-sum-cases))))

(defthm bvchop-of-minus-of-bvchop
  (equal (bvchop size (- (bvchop size x)))
         (bvchop size (- x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (bvchop) (mod-cancel)))))

;hope this split is okay
(defthmd bvchop-of-minus-helper
  (equal (bvchop size (- x))
         (if (equal 0 (bvchop size x))
             0
           (- (expt 2 size) (bvchop size x))))
  :hints (("Goal" :in-theory (e/d (bvchop) (mod-cancel)))))

(defthm bvchop-when-size-is-not-posp
  (implies (not (posp size))
           (equal (bvchop size i) 0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-of-minus
  (equal (bvchop size (- x))
         (if (or (not (natp size))
                 (equal 0 (bvchop size x)))
             0
           (- (expt 2 size) (bvchop size x))))
  :hints (("Goal" :use ((:instance bvchop-when-size-is-not-natp (i (- x)))
                        bvchop-of-minus-helper)
           :in-theory (disable bvchop-when-size-is-not-posp
                               bvchop-when-size-is-not-posp
                               expt))))

;i guess this one is an abbreviation rule
(defthm unsigned-byte-p-bvchop-same
  (equal (unsigned-byte-p size (bvchop size i))
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;rename
(defthm bvchop-shift-gen
  (implies (and (integerp x)
                (integerp n)
                (natp m))
           (equal (bvchop n (* (expt 2 m) x))
                  (if (<= m n)
                      (* (expt 2 m) (bvchop (- n m) x))
                    0)))
  :hints (("Goal"
           :use (:instance integerp-of-expt-when-natp (i (+ m (- n))) (r 2))
           :in-theory (e/d (bvchop mod-cancel
                                   expt-of-+)
                           (integerp-of-expt-when-natp)))))

(defthm bvchop-shift-gen-alt
  (implies (and (integerp x)
                (integerp n)
                (natp m))
           (equal (bvchop n (* x (expt 2 m)))
                  (if (<= m n)
                      (* (expt 2 m) (bvchop (- n m) x))
                    0)))
  :hints (("Goal"
           :use (:instance integerp-of-expt-when-natp (i (+ m (- n))) (r 2))
           :in-theory (e/d (bvchop mod-cancel
                                   expt-of-+)
                           (integerp-of-expt-when-natp)))))

(defthm bvchop-sum-drop-bvchop
  (implies (and (<= m n)
                (integerp n)
                (integerp z))
           (equal (bvchop m (+ (bvchop n y) z))
                  (bvchop m (+ (ifix y) z))))
  :hints (("Goal"
           :in-theory (e/d (bvchop mod-of-mod-when-mult) (mod-cancel)))))

(defthm bvchop-sum-drop-bvchop-alt
  (implies (and (<= m n)
                (integerp n)
                (integerp z))
           (equal (bvchop m (+ z (bvchop n y)))
                  (bvchop m (+ (ifix y) z))))
  :hints (("Goal" :use bvchop-sum-drop-bvchop :in-theory (disable bvchop-sum-drop-bvchop))))

(defthm bvchop-of-expt-hack
  (equal (bvchop (+ -1 n) (expt 2 n))
         0)
  :hints (("Goal" :in-theory (enable bvchop equal-of-0-and-mod))))

;gen
(defthm bvchop-of-expt-hack2
  (implies (posp n)
           (equal (bvchop 1 (expt 2 n))
                  0))
  :hints (("Goal" :in-theory (enable bvchop floor-when-multiple))))

(defthm bvchop-of-minus-1
  (implies (natp n)
           (equal (bvchop n -1)
                  (+ -1 (expt 2 n))))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-of-mask
  (implies (and (<= size1 size2)
                (natp size1)
                (integerp size2))
           (equal (bvchop size2 (+ -1 (expt 2 size1)))
                  (+ -1 (expt 2 size1))))
  :hints (("Goal" :in-theory (enable zip unsigned-byte-p))))

;combine with the other
(defthm bvchop-of-mask-other
  (implies (and (<= size2 size1)
                (natp size2)
                (integerp size1))
           (equal (bvchop size2 (+ -1 (expt 2 size1)))
                  (+ -1 (expt 2 size2))))
  :hints (("Goal" :induct t ;for speed
           :in-theory (enable (:i expt)
                              bvchop ;mod-cancel
                              mod-of-mod-when-mult
                              unsigned-byte-p
                              mod-sum-cases))))

;make a constant version? maybe not for this one?
(defthm bvchop-of-mask-gen
  (implies (and (natp size1)
                (natp size2))
           (equal (bvchop size2 (+ -1 (expt 2 size1)))
                  (if (<= size1 size2)
                      (+ -1 (expt 2 size1))
                    (+ -1 (expt 2 size2))))))


(defthm bvchop-impossible-value
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p size k))
                (natp size))
           (not (equal k (bvchop size x)))))

(defthm bvchop-of-expt-0
  (implies (and (<= size1 size2)
                (integerp size1)
                (integerp size2))
           (equal (bvchop size1 (expt 2 size2))
                  0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-sum-subst-const
  (implies (and (equal (bvchop n x) k)
                (syntaxp (and (quotep k)
                              (not (quotep x))))
                (integerp x)
                (integerp y))
           (equal (bvchop n (+ x y))
                  (bvchop n (+ k y)))))

(defthm bvchop-sum-subst-const-arg2
  (implies (and (equal (bvchop n x) k)
                (syntaxp (and (quotep k)
                              (not (quotep x))))
                (integerp x)
                (integerp y))
           (equal (bvchop n (+ y x))
                  (bvchop n (+ y k)))))

;gen
;strength reduction
(defthmd mod-by-4-becomes-bvchop
  (implies (integerp i)
           (equal (mod i 4)
                  (bvchop 2 i)))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-+-cancel-better
  (implies (and (integerp i)
                (integerp j)
                (integerp k))
           (equal (equal (bvchop size (+ i j))
                         (bvchop size (+ i k)))
                  (equal (bvchop size j)
                         (bvchop size k))))
  :hints (("Goal" :in-theory (enable bvchop))))

;(in-theory (disable BVCHOP-+-CANCEL))

(defthm bvchop-of-+-cancel-1-2
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp z2))
           (equal (equal (bvchop size (+ x y)) (bvchop size (+ z x z2)))
                  (equal (bvchop size y) (bvchop size (+ z z2))))))

(defthm bvchop-of-+-cancel-2-2-alt
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp z2))
           (equal (equal (bvchop size (+ y x z)) (bvchop size (+ z2 x)))
                  (equal (bvchop size (+ y z)) (bvchop size z2)))))

(defthm bvchop-of-+-cancel-1-1
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (equal (bvchop size (+ x y)) (bvchop size (+ x z)))
                  (equal (bvchop size y) (bvchop size z)))))

(defthmd bvchop-plus-minus-1-split-gen
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 size)))
                (integerp x)
                (posp size))
           (equal (bvchop size (+ k x))
                  (if (equal 0 (bvchop size x))
                      (+ -1 (expt 2 size))
                    (+ -1 (bvchop size x)))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

;rename
(defthm bvchop-chop-leading-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (not (unsigned-byte-p size k))
                (integerp k)
                (integerp x)
                ;; (natp size)
                )
           (equal (bvchop size (+ k x))
                  (bvchop size (+ (bvchop size k) x))))
  :hints (("Goal" :cases ((natp size)))))

;rename
(defthm bvchop-times-cancel-better
  (implies (and  (<= m n)
                 (integerp x)
                 (integerp y)
                 (natp n))
           (equal (bvchop m (* (bvchop n x) y))
                  (bvchop m (* x y))))
  :hints (("Goal" :in-theory (e/d (bvchop) (mod-of-*-of-mod))
           :use ((:instance mod-of-*-of-mod (z (expt 2 m)) (x y) (x1 x))
                 (:instance mod-of-*-of-mod (z (expt 2 m)) (x y) (x1 (mod x (expt 2 n))))))))

;rename
(defthm bvchop-times-cancel-better-alt
  (implies (and  (<= m n)
                 (integerp x)
                 (integerp y)
                 (natp n))
           (equal (bvchop m (* y (bvchop n x)))
                  (bvchop m (* y x))))
  :hints (("Goal" :use bvchop-times-cancel-better
           :in-theory (disable bvchop-times-cancel-better))))

(defthm bvchop-of-+-of-expt
  (implies (integerp x)
           (equal (bvchop size (+ x (expt 2 size)))
                  (bvchop size x)))
  :hints (("Goal":in-theory (enable bvchop))))

(defthm bvchop-of-+-of-expt-gen
  (implies (and (<= size size2)
                (integerp x)
                (integerp size)
                (integerp size2))
           (equal (bvchop size (+ x (expt 2 size2)))
                  (bvchop size x)))
  :hints (("Goal":in-theory (enable bvchop))))

(defthm bvchop-of-+-of-expt-alt
  (implies (integerp x)
           (equal (bvchop size (+ (expt 2 size) x))
                  (bvchop size x)))
  :hints (("Goal" :cases ((natp size)))))

;rename?
;see also <-lemma-for-known-operators-axe2 but that one probably requires a constant for the width
(defthm bvchop-numeric-bound
  (implies (and (syntaxp (quotep k))
                (<= k 0))
           (not (< (bvchop size x) k))))

(defthm bvchop-subst-constant
  (implies (and (syntaxp (not (quotep x)))
                (equal k (bvchop free x))
                (syntaxp (quotep k))
                (<= size free)
                ;;(natp size)
                (integerp free))
           (equal (bvchop size x)
                  (bvchop size k))))

;subsumes the -0 version
(defthm bvchop-of-expt
  (implies (and (integerp size1)
                (natp size2))
           (equal (bvchop size1 (expt 2 size2))
                  (if (<= size1 size2)
                      0
                    (expt 2 size2))))
  :hints (("Goal" :in-theory (e/d (bvchop) (;mod-of-expt-of-2-constant-version mod-of-expt-of-2
                                            )))))

;can this be expensive?
;rename?
(defthm bvchop-bound-rw
  (implies (<= 0 x)
           (not (< x (bvchop size x))))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm <-of-bvchop-and-bvchop-same
  (implies (and (<= s1 s2)
                (natp s1)
                (integerp s2))
           (not (< (bvchop s2 x) (bvchop s1 x))))
  :hints (("Goal"
           :use (:instance bvchop-bound-rw (x (bvchop s2 x)) (size s1))
           :in-theory (disable bvchop-bound-rw))))


;Not sure this will fire if SMALL and BIG are constants, due to the free var.
(defthm <=-of-bvchop-same-linear-2
  (implies (and (<= small big)
                (natp small)
                (integerp big))
           (<= (bvchop small x) (bvchop big x)))
  :rule-classes ((:linear))
  :hints (("Goal" :in-theory (enable natp))))

;; Do not remove: helps justify the correctness of some operations done by Axe.
(defthm bvchop-of-nfix
  (equal (bvchop (nfix n) x)
         (bvchop n x)))

(defthm not-<-of-expt-and-bvchop
  (not (< (expt 2 size) (bvchop size x))))

(defthm bvchop-identity
  (implies (unsigned-byte-p size i)
           (equal (bvchop size i)
                  i))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm bvchop-of-mod-of-expt
  (implies (and (<= size j)
                (integerp j)
                (natp size))
           (equal (bvchop size (mod i (expt 2 j)))
                  (bvchop size i)))
  :hints (("Goal" :cases ((rationalp i))
           :in-theory (enable bvchop))))

(defthm bvchop-of-+-of-*-of-expt
  (implies (and (integerp x)
                (natp size))
           (equal (bvchop size (+ (* x (expt 2 size)) y))
                  (bvchop size y)))
  :hints (("Goal" :in-theory (enable bvchop equal-of-0-and-mod
                                     mod-sum-cases))))

(defthm bvchop-of-+-of-minus-of-expt
  (implies (and (integerp x)
                (natp size))
           (equal (bvchop size (+ x (- (expt 2 size))))
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvchop
                                     mod-sum-cases))))

(defthm bvchop-of-mod-of-expt-2
  (implies (and (< j size)
                (integerp size)
                (integerp x)
                (natp j))
           (equal (bvchop size (mod x (expt 2 j)))
                  (bvchop j x)))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-+-cancel-0
  (implies (and (force (integerp j))
                (integerp i)
                (natp size)
                )
           (equal (equal (bvchop size (+ i j))
                         (bvchop size i))
                  (equal (bvchop size j) 0)))
  :hints (("Goal" :use (:instance bvchop-+-cancel-better (k 0))
           :in-theory (disable bvchop-+-cancel-better))))

(defthm bvchop-+-cancel-0-alt
  (implies (and (force (integerp j))
                (integerp i)
                (natp size)
                )
           (equal (equal (bvchop size (+ j i))
                         (bvchop size i))
                  (equal (bvchop size j) 0)))
  :hints (("Goal" :use (:instance bvchop-+-cancel-better (k 0))
           :in-theory (disable bvchop-+-cancel-better))))

(defthmd mod-of-expt-of-2
  (implies (and (integerp x)
                (natp m))
           (equal (mod x (expt 2 m))
                  (bvchop m x)))
  :hints (("Goal" :in-theory (enable bvchop))))

(theory-invariant (incompatible (:definition bvchop)
                                (:rewrite mod-of-expt-of-2)))



;; Replaces mod with bvchop
;; rename
;kill the version with 4 hard-coded
(defthmd mod-of-expt-of-2-constant-version
  (implies (and (syntaxp (quotep k)) ;new..
                (power-of-2p k) ;(equal k (expt 2 (+ -1 (integer-length k))))
                (integerp x)
                ;;(natp k)
                )
           (equal (mod x k)
                  (bvchop (+ -1 (integer-length k)) x)))
  :hints (("Goal" :in-theory (e/d (power-of-2p) (mod-of-expt-of-2))
           :use (:instance mod-of-expt-of-2
                           (m (+ -1 (integer-length k)))))))

(theory-invariant (incompatible (:definition bvchop) (:rewrite mod-of-expt-of-2-constant-version)))

(defthm bitp-of-bvchop-of-1
  (bitp (bvchop 1 x)))

(defthm bvchop-+-cancel-cross
  (implies (and (force (integerp i))
                (force (integerp j))
                (force (integerp k)))
           (equal (equal (bvchop size (+ j i))
                         (bvchop size (+ i k)))
                  (equal (bvchop size j)
                         (bvchop size k)))))

(defthm bvchop-+-cancel-cross2
  (implies (and (force (integerp i))
                (force (integerp j))
                (force (integerp k)))
           (equal (equal (bvchop size (+ i j))
                         (bvchop size (+ k i)))
                  (equal (bvchop size j)
                         (bvchop size k)))))

(defthm bvchop-of-*-of-expt-when-<=
  (implies (and (<= size n)
                (integerp x)
                (natp n)
                ;;(natp size)
                )
           (equal (bvchop size (* x (expt 2 n)))
                  0))
  :hints (("Goal" :cases ((natp size)))))

(defthm bvchop-identity-cheap
  (implies (and (unsigned-byte-p freesize i)
                (<= freesize size)
                (integerp size))
           (equal (bvchop size i)
                  i))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm bvchop-of-both-sides
  (implies (equal x y)
           (equal (bvchop size x)
                  (bvchop size y)))
  :rule-classes nil)

(defthmd bvchop-upper-bound-3
  (implies (and (<= (+ -1 (expt 2 n)) k)
                (natp n))
           (not (< k (bvchop n x))))
  :hints (("Goal" :cases ((<= low high))
           :use (:instance bound-when-usb (x (bvchop n x)))
           :in-theory (disable bound-when-usb))))

;bozo more like this?
(defthmd bvchop-upper-bound-3-constant-version
  (implies (and (syntaxp (quotep k))
                (<= (+ -1 (expt 2 n)) k)
                (natp n))
           (not (< k (bvchop n x))))
  :hints (("Goal" :cases ((<= low high))
           :use (:instance bound-when-usb (x (bvchop n x)))
           :in-theory (disable bound-when-usb))))

(defthmd bvchop-of-*-when-unsigned-byte-p-of-*-of-bvchop-and-bvchop
  (implies (and (integerp x)
                (integerp y))
           (implies (unsigned-byte-p size (* (bvchop size x) (bvchop size y)))
                    (equal (bvchop size (* x y))
                           (* (bvchop size x) (bvchop size y)))))
  :hints (("Goal" :use (bvchop-of-*-of-bvchop
                        (:instance bvchop-of-*-of-bvchop-arg2
                                   (x (bvchop size x))))
           :in-theory (disable bvchop-of-*-of-bvchop
                               bvchop-of-*-of-bvchop-arg2
                               bvchop-times-cancel-better-alt))))

;gen the exponent
(defthm bvchop-of-plus-of-expt-bigger
  (implies (and (posp size)
                (integerp x))
           (equal (bvchop (+ -1 size) (+ x (expt 2 size)))
                  (bvchop (+ -1 size) x))))

(defthm bvchop-of-+-of-bvchop-arg3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvchop size (+ x y (bvchop size z)))
                  (bvchop size (+ x y z))))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-of-+-of-*-of-bvchop
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvchop size (+ x (* y (bvchop size z))))
                  (bvchop size (+ x (* y z))))))

(defthm bvchop-of-*-of-expt-arg3
  (implies (and (<= size size2)
                (integerp x)
                (integerp y)
                (natp size)
                (natp size2))
           (equal (bvchop size (* x y (expt 2 size2)))
                  0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-of-+-of-expt-arg2-arg3
  (implies (and (<= size size2)
                (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                (natp size2))
           (equal (bvchop size (+ x (* y z (expt 2 size2))))
                  (bvchop size x))))

;gen?
(defthm bvchop-31-of-*-of-2147483648
  (IMPLIES (INTEGERP X)
           (EQUAL (BVCHOP 31 (* 2147483648 X))
                  0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-of-+-of---of-*-of-expt
  (implies (and (integerp x)
                (integerp y)
                (natp size))
           (equal (bvchop size (+ (- (* x (expt 2 size))) y))
                  (bvchop size y))))

(local
 (defthmd mod-both-sides
   (implies (equal x1 x2)
            (equal (mod x1 y) (mod x2 y)))))

(defthm bvchops-same-when-bvchops-same
  (implies (and (equal (bvchop free x) (bvchop free y))
                (<= n free)
                (natp free)
                (natp n)
                )
           (equal (equal (bvchop n x) (bvchop n y))
                  t))
  :hints (("Goal" :use ((:instance BVCHOP-OF-BVCHOP (size1 n) (size free) (i x))
                        (:instance BVCHOP-OF-BVCHOP (size1 n) (size free) (i y)))
           :in-theory (disable BVCHOP-OF-BVCHOP))))

(defthm bvchop-of-1-and-+-of-1-and-expt
  (implies (posp i)
           (equal (BVCHOP 1 (+ 1 (EXPT 2 i)))
                  1))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm <-of-bvchop-when-<-of-bvchop-bigger
  (implies (and (< (bvchop freesize x) y)
                (<= size freesize)
                (integerp freesize))
           (< (bvchop size x) y))
  :hints (("Goal" :use (:instance <-of-bvchop-and-bvchop-same
                                  (s2 freesize)
                                  (s1 size))
           :in-theory (disable <-of-bvchop-and-bvchop-same))))

(defthm evenp-of-bvchop
  (implies (and (< 1 n)
                (integerp n))
           (equal (evenp (bvchop n x))
                  (equal 0 (bvchop 1 x))))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-of-sum-expt
  (implies (and (natp size)
                (integerp y)
                (integerp x))
           (equal (bvchop size (+ x (expt 2 size) y))
                  (bvchop size (+ x y))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-sum-minus-expt
  (implies (and (natp size)
                (integerp x))
           (equal (bvchop size (+ x (- (expt 2 size))))
                  (bvchop size x)))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-sum-minus-expt-alt
  (implies (and (natp size)
                (integerp x)
                (integerp y))
           (equal (bvchop size (+ x (- (expt 2 size)) y))
                  (bvchop size (+ x y))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm bvchop-of-plus-of-times-expt
  (implies (and (natp size)
                (integerp x)
                (integerp y))
           (equal (bvchop size (+ x (* (expt 2 size) y)))
                  (bvchop size x))))

;rename
(defthmd bvchop-when-negative-lemma
  (implies (and (< x 0)
                (<= (- (expt 2 size)) x)
                (integerp x)
                (natp size))
           (equal (bvchop size x)
                  (+ (expt 2 size) x)))
  :hints (("Goal"
           :use (:instance acl2::bvchop-identity (acl2::size size) (i (+ (expt 2 size) X)))
           :in-theory (enable bvchop unsigned-byte-p))))

(defthmd bvchop-when-signed-byte-p
  (implies (and (signed-byte-p size x)
                (posp size))
           (equal (bvchop size x)
                  (if (< x 0)
                      (+ x (expt 2 size))
                    x)))
  :hints (("Goal" :in-theory (enable signed-byte-p bvchop))))
