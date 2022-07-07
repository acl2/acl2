; A book about the sign-extending operation logext
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ihs/basic-definitions" :dir :system) ;for logext
(include-book "getbit")
(local (include-book "logapp"))
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "unsigned-byte-p"))
(local (include-book "getbit-rules"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "bvcat")) ;for BVCHOP-OF-LOGAPP-BIGGER
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop, for floor-type-4

(in-theory (disable logext))

(defthm integerp-of-logext
  (integerp (logext size x)))

(defthm logext-when-i-is-not-an-integer
  (implies (not (integerp i))
           (equal (logext size i)
                  0))
  :hints (("Goal" :in-theory (enable logext logbitp))))

(defthm logext-of-bvchop-same
  (implies (posp size)
           (equal (logext size (bvchop size x))
                  (logext size x)))
  :hints (("Goal" :cases ((integerp size))
           :in-theory (enable logext))))

;; (thm
;;  (IMPLIES (AND (INTEGERP X)
;;                (INTEGERP Y)
;;                (INTEGERP z)
;;                (INTEGERP w)
;;                )
;;           (EQUAL (LOGAPP 31 (* X (LOGAPP 31 Y z)) w)
;;                  (LOGAPP 31 (* X Y) w)))
;;  :hints (("Goal" :in-theory (enable logapp bvchop))))

(in-theory (disable logbitp))

;; (thm
;;  (implies (and (integerp x)
;;                (integerp y))
;;           (equal (logapp 31 (* x (logapp 31 y -1)) -1)
;;                  (logapp 31 (* x y) -1)))
;;  :hints (("Goal" :in-theory (enable logapp))))

;; (thm
;;  (implies (and (integerp x)
;;                (integerp y))
;;           (equal (LOGBITP 31 (* X (BVCHOP 31 Y)))
;;                  (LOGBITP 31 (* X Y))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (logbitp bvchop) (evenp)))))

;; (defthm logbitp-of-31-of-*-of-bvchop
;;   (IMPLIES (AND (EVENP X)
;;                 (INTEGERP X)
;;                 (INTEGERP Y)
;;                 (NOT (LOGBITP 31 Y))
;;                 (NOT (LOGBITP 31 (* X Y))))
;;            (equal (LOGBITP 31 (* X (BVCHOP 31 Y)))
;;                   (LOGBITP 31 (* X Y))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :cases ((evenp x))
;;            :in-theory (e/d (LOGEXT
;;                             logapp logbitp
;;                             BVCHOP
;;                             mod
;;                             evenp
;;                             oddp
;;                             INTEGERP-OF-*-OF-/-BECOMES-EQUAL-OF-0-AND-MOD
;;                             )
;;                            (LOGBITP-IFF-GETBIT
;;                             EQUAL-OF-*-2-OF-FLOOR-OF-2-SAME)))))

(defthm bvchop-of-*-of-logapp
  (implies (and (<= size size2)
                (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                (natp size2))
           (equal (bvchop size (* x (logapp size2 y z)))
                  (bvchop size (* x y))))
  :hints (("Goal" :in-theory (enable logapp))))

(defthmd widen-logapp-when-top-bit-1
  (IMPLIES (AND (EQUAL 1 (GETBIT (+ -1 SIZE) X))
                (INTEGERP X)
                (INTEGERP SIZE)
                (< 0 SIZE)
                )
           (equal (LOGAPP (+ -1 SIZE) X -1)
                  (LOGAPP SIZE X -1))))

(defthmd widen-bvchop-when-top-bit-0
  (IMPLIES (AND (EQUAL 0 (GETBIT (+ -1 SIZE) X))
                (INTEGERP X)
                (posp SIZE))
           (equal (bvchop (+ -1 SIZE) X)
                  (bvchop SIZE X))))

(theory-invariant (incompatible (:rewrite widen-bvchop-when-top-bit-0)
                                (:rewrite bvchop-when-top-bit-not-1-fake-free)))

(defthm getbit-of-*-of-logapp
  (implies (and (< size size2)
                (integerp x)
                (integerp y)
                (integerp z)
                (natp size)
                (natp size2))
           (equal (getbit size (* x (logapp size2 y z)))
                  (getbit size (* x y))))
  :hints (("Goal" :in-theory (e/d (logapp getbit slice-alt-def)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit)))))

(defthm getbit-of-*-of-bvchop
  (implies (and (< size size2)
                (integerp x)
                (integerp y)
                (natp size)
                (natp size2))
           (equal (getbit size (* x (bvchop size2 y)))
                  (getbit size (* x y))))
  :hints (("Goal" :in-theory (e/d (getbit slice-alt-def)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit)))))

(defthm logext-of-*-of-logext-arg1
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (logext size (* (logext size x) y))
                  (logext size (* x y))))
  :hints (("Goal" :in-theory (e/d (logext
                                   widen-logapp-when-top-bit-1
                                   widen-bvchop-when-top-bit-0)
                                  (bvchop-when-top-bit-not-1-fake-free)))))

(defthm logext-of-*-of-logext-arg2
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (logext size (* x (logext size y)))
                  (logext size (* x y))))
  :hints (("Goal" :in-theory (e/d (logext
                                   widen-logapp-when-top-bit-1
                                   widen-bvchop-when-top-bit-0)
                                  (bvchop-when-top-bit-not-1-fake-free)))))



;fixme gen
(defthm logapp-lemma
  (IMPLIES (AND (<= M N)
                (<= 0 M)
                (INTEGERP M)
                (INTEGERP N)
                (LOGBITP (+ -1 N) X)
                (LOGBITP (+ -1 M) X))
           (EQUAL (LOGAPP (+ -1 M)
                          (LOGAPP (+ -1 N) X -1)
                          -1)
                  (LOGAPP (+ -1 M) X -1)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logapp bvchop) (MOD-EXPT-SPLIT)))))

(defthm logbitp-when-j-is-not-integerp
  (implies (not (integerp j))
           (not (logbitp i j)))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-of-0
  (not (logbitp n 0))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm oddp-of-bvchop
  (equal (ODDP (BVCHOP n X))
         (if (not (posp n))
             nil
           (ODDP (ifix X))))
  :hints (("Goal" :in-theory (enable bvchop ODDP EVENP-BECOMES-EQUAL-OF-0-AND-MOD))))

(defthm logext-of-logext
  (implies (and (<= m n)
                (< 0 m) ;gen
                (integerp m)
                (integerp n))
           (equal (logext m (logext n x))
                  (logext m x)))
  :hints (("Goal" :in-theory (e/d (logext getbit slice)
                                  (bvchop-of-logtail-becomes-slice
                                   bvchop-1-becomes-getbit slice-becomes-getbit)))))

(defthm logext-of-0
  (equal (logext size 0)
         0)
  :hints (("Goal" :in-theory (enable logext))))

;should (logext 0 0) be 0 or -1?

;proof uses elim
(defthm logext-does-nothing-rewrite
  (implies (posp size)
           (equal (equal x (logext size x))
                  (signed-byte-p size x)))
  :hints (("Goal" :in-theory (e/d (logext logbitp logtail) (LOGBITP-IFF-GETBIT)))))

;; See also logext-identity
(defthm logext-when-signed-byte-p
  (implies (signed-byte-p size x)
           (equal (logext size x)
                  x))
  :hints (("Goal" :in-theory (e/d (logext logbitp logtail) (LOGBITP-IFF-GETBIT)))))

(defthm acl2-numberp-of-logext
  (acl2-numberp (logext size i)))

;hope the new hyps are okay
(defthm bvchop-of-logext
  (implies (and (integerp ext-size)
                (<= final-size ext-size)
                )
           (equal (bvchop final-size (logext ext-size i))
                  (bvchop final-size i)))
  :hints (("Goal" :cases (;messy
                          (not (integerp final-size))
                          (< final-size 0)
;                          (< EXT-SIZE (BINARY-+ '1 FINAL-SIZE))
                          (equal 0 ext-size)
                          )
           :use (:instance BVCHOP-OF-LOGAPP-BIGGER
                           (X -1)
                 (Y I)
                 (N2 (+ -1 EXT-SIZE))
                 (N FINAL-SIZE))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;BVCHOP-OF-LOGTAIL
                            LOGTAIL-OF-BVCHOP
                            logext ;bvchop logapp
                                   getbit
                                   slice
                                   ) (BVCHOP-OF-LOGAPP-BIGGER
                                      BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                   MOD-EXPT-SPLIT ;bad?
                                   SLICE-BECOMES-GETBIT
                                   BVCHOP-1-BECOMES-GETBIT)))))

(defthm logext-of-bvchop-smaller
  (implies (and (<= size n)
                (integerp n)
                (posp size))
           (equal (logext size (bvchop n x))
                  (logext size x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable logext))))

(defthm signed-byte-p-of-logext
  (implies (and (>= size1 size)
                (integerp size1)
                (posp size))
           (signed-byte-p size1 (logext size i))))

;; Splits based on the high bit
(defthmd logext-cases
  (implies (posp size)
           (equal (logext size x)
                  (if (equal 1 (getbit (+ -1 size) x))
                      (+ (bvchop (+ -1 size) x)
                         (- (expt 2 (+ -1 size))))
                    (bvchop (+ -1 size) x))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-when-size-not-posp
  (implies (not (posp n))
           (equal (logext n x)
                  (logext 1 x)))
  :hints (("Goal" :in-theory (e/d (logext getbit slice)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

(defthm bvchop-of-logext-same
  (equal (bvchop size (logext size x))
         (bvchop size x))
  :hints (("Goal" :cases ((integerp size)))))

;todo: prove without opening up so much stuff
(defthm equal-of-0-and-bvchop
  (implies (posp n)
           (equal (equal 0 (logext n x))
                  (equal 0 (bvchop n x))))
  :hints (("Goal" :in-theory (e/d (logext bvchop getbit slice logtail
                                          expt-of-+
                                          mod-=-0)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice
                                   )))))

(defthm logext-of-expt-same
  (implies (posp size)
           (equal (logext size (expt 2 size))
                  0))
  :hints (("Goal" :cases ((posp size)))))

(defthm logext-of-+-of-expt-same
  (implies (and (posp size)
                (integerp x))
           (equal (logext size (+ x (expt 2 size)))
                  (logext size x)))
  :hints (("Goal" :use ((:instance logext-of-bvchop-same
                                   (x (+ x (expt 2 size))))
                        (:instance logext-of-bvchop-same
                                   (x x)))
           :in-theory (disable logext-of-bvchop-same expt
                               logext-of-bvchop-smaller))))

(defthm logext-of-+-of-expt-gen
  (implies (and (<= size size2)
                (integerp x)
                (posp size)
                (integerp size2))
           (equal (logext size (+ x (expt 2 size2)))
                  (logext size x)))
  :hints (("Goal":in-theory (enable logext))))

(defthm logext-of-minint
  (implies (posp size)
           (equal (logext size (expt 2 (+ -1 size)))
                  (- (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-of-minus1
  (equal (logext size -1)
         -1)
  :hints (("Goal" :cases ((posp size)
                          (equal 0 size)))))

(defthm equal-of-logext-of-1-and-minus1
  (equal (equal (logext 1 x) -1)
         (equal 1 (getbit 0 x)))
  :hints (("Goal" :in-theory (enable logext))))

(defthm equal-of-logext-of-1-and-0
  (equal (equal (logext 1 x) 0)
         (equal 0 (getbit 0 x)))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-of-1-arg2
  (implies (posp size)
           (equal (logext size 1)
                  (if (equal 1 size)
                      -1
                    1))))

(defthm logext-of-logext-same
  (equal (logext size (logext size i))
         (logext size i))
  :hints (("Goal" :cases ((posp size)))))

;; (defthm <-of-logext-linear-upper
;;   (implies (posp size)
;;            (< (logext size x) (expt 2 (+ -1 size))))
;;   :rule-classes :linear)

(defthm <=-of-logext-linear-upper
  (implies (posp size)
           (<= (logext size x) (+ -1 (expt 2 (+ -1 size)))))
  :rule-classes :linear)

(defthm <-of-logext-linear-lower
  (implies (posp size)
           (<= (- (expt 2 (+ -1 size))) (logext size x)))
  :rule-classes :linear)

(defthm <-of-logext-same-linear
  (implies (and (natp x)
                (posp size))
           (<= (logext size x) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-when-top-bit-0
  (implies (and (equal (getbit (+ -1 n) x) 0)
                (posp n))
           (equal (logext n x)
                  (bvchop (+ -1 n) x)))
  :hints (("Goal" :use ((:instance logext-identity (size n) (i (bvchop n x))))
           :in-theory (e/d (logext)
                           (logext-identity
                            logext-does-nothing-rewrite)))))

;could loop?
(defthmd logext-when-positive-gen
  (implies (<= 0 (logext size x))
           (equal (logext size x)
                  (bvchop (+ -1 size) x)))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthmd logext-when-negative
  (implies (< (logext 32 x) 0)
           (equal (logext 32 x)
                  (+ (bvchop 31 x)
                     (- (expt 2 31)))))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthmd logext-when-negative-2
  (implies (and (equal 1 (getbit (+ -1 size) x))
                (posp size))
           (equal (logext size x)
                  (+ (bvchop (+ -1 size) x)
                     (- (expt 2 (+ -1 size))))))
  :hints (("Goal" :in-theory (e/d (logext logapp bvchop)
                                  (logapp-equal-rewrite)))))

(defthm logext-negative
  (implies (and (integerp x)
                (< 0 n)
                (natp n))
           (equal (< (logext n x) 0)
                  (equal 1 (getbit (+ -1 n) x))))
  :hints (("Goal" :in-theory (enable logext))))

(defthmd logext-bound-when-unsigned-byte-p
  (implies (and (syntaxp (quotep k))
                ;; (< 0 k)
                (natp k)
                (<= k (expt 2 (+ -1 n)))
                (< x k)
                (unsigned-byte-p n x)
                ;; (< 0 n)
                )
           (< (logext n x) k))
  :hints (("Goal" :cases ((equal n 0))
           :in-theory (enable ;logext
                              ))))

;for axe
(defthmd logext-not-nil1
  (not (equal (logext n x) nil)))

;for axe
(defthm logext-not-nil2
  (not (equal nil (logext n x))))

;; A bit odd
(defthm logext-of-0-arg1
  (equal (logext 0 x)
         (if (equal (getbit 0 x) 1)
             -1
           0))
  :hints (("Goal" :in-theory (enable logext))))

;todo better than logext-negative above
(defthmd <-of-logext-and-0
  (implies (posp size)
           (equal (< (logext size k) 0)
                  (equal 1 (getbit (+ -1 size) k))))
  :hints (("Goal" :in-theory (enable logext))))

(defthmd <-of-0-and-logext-alt
  (implies (posp size)
           (equal (< 0 (logext size x))
                  (and (equal 0 (getbit (+ -1 size) x))
                       (not (equal 0 (bvchop (+ -1 size) x))))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-of-maxint
  (implies (posp size)
           (equal (logext size (+ -1 (expt 2 (+ -1 size))))
                  (+ -1 (expt 2 (+ -1 size))))))

(defthmd equal-of-logext-and-logext
  (implies (posp size)
           (equal (equal (logext size x) (logext size y))
                  (equal (bvchop size x) (bvchop size y))))
  :hints (("Goal" :use ((:instance bvchop-of-logext-same (x x))
                        (:instance bvchop-of-logext-same (x y))
                        (:instance logext-of-bvchop-same (x x))
                        (:instance logext-of-bvchop-same (x y)))
           :in-theory (disable bvchop-of-logext-same
                               logext-of-bvchop-same
                               logext-of-bvchop-smaller
                               bvchop-of-logext))))

(defthm logext-of-+-of-logext-arg1
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (logext size (+ (logext size x) y))
                  (logext size (+ x y))))
  :hints (("Goal" :in-theory (enable equal-of-logext-and-logext))))

(defthm logext-of-+-of-logext-arg2
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (logext size (+ x (logext size y)))
                  (logext size (+ x y))))
  :hints (("Goal" :in-theory (enable equal-of-logext-and-logext))))

;; Normalizes the constant
(defthm logext-of-+-of-constant
  (implies (and (syntaxp (quotep k))
                (not (signed-byte-p size k))
                (integerp k)
                (integerp x)
                (posp size))
           (equal (logext size (+ k x))
                  (logext size (+ (logext size k) x)))))

(defthm logext-of---of-bvchop
  (implies (and (integerp x)
                (posp size))
           (equal (logext size (- (bvchop size x)))
                  (logext size (- x))))
  :hints (("Goal" :in-theory (enable logext-cases))))

;used to allow n=1 but untrue for that case?
;rename
(defthm logext-shift
  (implies (and (integerp x)
                (natp n)
                (< 1 n))
           (equal (logext n (* 2 x))
                  (* 2 (logext (+ -1 n) x))))
  :hints (("Goal" :in-theory (e/d (logext) ()))))

(defthm logext-of-expt-of-one-less
  (implies (posp size)
           (equal (logext size (expt 2 (+ -1 size)))
                  (- (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-of-*-of-expt-arg1
  (implies (and (integerp x)
                (integerp size)
                (posp i)
                (< i size))
           (equal (logext size (* (expt 2 i) x))
                  (* (expt 2 i) (logext (- size i) x))))
  :hints (("Goal" :in-theory (e/d (logext) ()))))

(defthm logext-when-low-bits-known
  (implies (and (equal (bvchop 31 x) free)
                (syntaxp (quotep free)))
           (equal (logext 32 x)
                  (if (equal 0 (getbit 31 x))
                      free
                    (+ (- (expt 2 31))
                       free))))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthm logext-negative-linear-cheap
  (implies (equal (getbit 31 x) 1)
           (< (logext 32 x) 0))
  :rule-classes ((:linear :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable logext))))

(defthmd apply-logext-32-to-both-sides
  (implies (and (equal x y)
                (equal a (logext 32 x))
                (equal b (logext 32 y)))
           (equal (equal a b)
                  t)))

(defthmd apply-logext-32-to-both-sides-alt
  (implies (and (equal y x)
                (equal b (logext 32 x))
                (equal a (logext 32 y)))
           (equal (equal a b)
                  t)))

;yikes, don't we want to go the other way?
(defthmd bvchop-of-sbp-equal-constant
  (implies (and (syntaxp (quotep k))
                (signed-byte-p 32 x) ;backchain limit?
                )
           (equal (equal k (bvchop 32 x))
                  (and (unsigned-byte-p 32 k)
                       (equal (logext 32 k) x))))
  :hints (("Goal" :in-theory (enable apply-logext-32-to-both-sides-alt apply-logext-32-to-both-sides))))

(defthm logext-of-plus-of-logext
  (implies (and (<= smallsize bigsize)
                (integerp smallsize)
                (integerp bigsize)
                (< 0 smallsize)
                (force (integerp x))
                (force (integerp y)))
           (equal (LOGEXT smallsize (+ x (LOGEXT bigsize y)))
                  (LOGEXT smallsize (+ x y)))))

(defthm logext-of-plus-of-logext-alt
  (implies (and (<= smallsize bigsize)
                (integerp smallsize)
                (integerp bigsize)
                (< 0 smallsize)
                (force (integerp x))
                (force (integerp y)))
           (equal (LOGEXT smallsize (+ (LOGEXT bigsize y) x))
                  (LOGEXT smallsize (+ x y)))))

;gen
(defthm bvchop-times-logext-32
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop 32 (* x (logext 32 y)))
                  (bvchop 32 (* x y))))
  :hints (("Goal" :in-theory (disable bvchop-of-*-of-bvchop)
           :use ((:instance bvchop-of-*-of-bvchop (size 32) (x (logext 32 y)) (y x))
                 (:instance bvchop-of-*-of-bvchop (size 32) (x y) (y x))))))

(defthm bvchop-of---of-logext-same
  (implies (and (integerp x)
                (posp size))
           (equal (bvchop size (- (logext size x)))
                  (bvchop size (- x)))))

(defthm logext-of---of-logext
  (implies (and (integerp x)
                (posp size))
           (equal (logext size (- (logext size x)))
                  (logext size (- x))))
  :hints (("Goal" :use ((:instance logext-of-bvchop-same (x (- x)))
                        (:instance logext-of-bvchop-same (x (- (logext size x)))))
           :in-theory (disable logext-of-bvchop-same
                               logext-of-bvchop-smaller
                               logext-when-signed-byte-p
                               logext-identity
                               bvchop-of-minus))))

(defthm logext-of-+-of---of-logext-arg2
  (implies (and (integerp x)
                (integerp y)
                (posp size))
           (equal (logext size (+ x (- (logext size y))))
                  (logext size (+ x (- y))))))

(defthm logext-of-minus
  (implies (and (integerp x)
                (posp size)
                )
           (equal (logext size (- x))
                  (if (and (equal 0 (bvchop (+ -1 size) x))
                           (equal 1 (getbit (+ -1 size) x)))
                      (+ (- (expt 2 size)) (- (logext size x)))
                    (- (logext size x)))))
  :hints (("Goal" :in-theory (e/d (logext logapp getbit slice logtail-of-bvchop bvchop-32-split-hack)
                                  (;anti-slice
                                   bvchop-1-becomes-getbit slice-becomes-getbit
                                                           ;bvplus-recollapse
                                                           bvchop-of-logtail)))))

(defthm bvchop-subst-constant-from-logext
  (implies (and (syntaxp (not (quotep x)))
                (equal (logext free x) k)
                (syntaxp (quotep k))
                (<= size free)
                (posp size)
                (integerp free)
                )
           (equal (bvchop size x)
                  (bvchop size k)))
  :hints (("Goal"
           :cases ((equal size (+ -1 free))
                   (< size (+ -1 free)))
           :in-theory (e/d (logext logtail-of-bvchop)
                           ( slice  BVCHOP-OF-LOGTAIL
                                    )))))

(defthm getbit-of-logext
  (implies (and (< n size)
                (integerp size)
                (< 0 size)
                (natp n))
           (equal (getbit n (logext size x))
                  (getbit n x)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (getbit slice BVCHOP-OF-LOGTAIL)
                           (SLICE-BECOMES-GETBIT ;LOGTAIL-BVCHOP
                                               BVCHOP-1-BECOMES-GETBIT
                                               BVCHOP-OF-LOGTAIL-BECOMES-SLICE
                                               ;;BVCHOP-OF-LOGTAIL
                                               )))))
