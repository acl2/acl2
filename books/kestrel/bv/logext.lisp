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
(local (include-book "ihs/logops-lemmas" :dir :system))
(include-book "logapp")
(include-book "getbit")
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "unsigned-byte-p"))
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

(defthm logext-bvchop-better
  (implies (posp n)
           (equal (logext n (bvchop n i))
                  (logext n i)))
  :hints (("Goal" :in-theory (enable logext logapp bvchop-when-i-is-not-an-integer bvchop
                                     mod-expt-split)
           :cases ((integerp i)))))

;; (local ;newly local
;;  (defthm logext-bvchop
;;    (implies (and (integerp x)
;;                  (< 0 n)
;;                  (integerp n))
;;             (equal (logext n (bvchop n x))
;;                    (logext n x)))
;;    :hints (("Goal" ;:cases ((EQUAL N 0))
;;             :in-theory (enable logext logapp)))))


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


;gross proof
(defthmd evenp-becomes-mod-fact
  (implies (rationalp x)
           (equal (evenp x)
                  (equal 0 (mod x 2)))) :hints (("Goal" :in-theory (enable evenp))))

;; (defthm int-lemma4a
;;    (implies (and (integerp x)
;;                  (integerp y))
;;             (equal (acl2::logext 32 (* x (acl2::logext 32 y)))
;;                    (acl2::logext 32 (* x y))))
;;    :otf-flg t
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :in-theory (e/d (ACL2::LOGEXT logapp bvchop logbitp
;;                                           evenp-becomes-mod-fact)
;;                             (evenp MOD-=-0)))))

(defthm logbitp-of-31-of-*-of-bvchop
  (IMPLIES (AND (EVENP X)
                (INTEGERP X)
                (INTEGERP Y)
                (NOT (LOGBITP 31 Y))
                (NOT (LOGBITP 31 (* X Y))))
           (equal (LOGBITP 31 (* X (BVCHOP 31 Y)))
                  (LOGBITP 31 (* X Y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :cases ((evenp x))
           :in-theory (e/d (ACL2::LOGEXT
                            acl2::logapp logbitp
                            BVCHOP
                            mod
                            evenp
                            oddp
                            INTEGERP-OF-*-OF-/-BECOMES-EQUAL-OF-0-AND-MOD
                            )
                           (LOGBITP-IFF-GETBIT
                            EQUAL-OF-*-2-OF-FLOOR-OF-2-SAME)))))

(defthm bvchop-of-+-of-*-of-bvchop
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (bvchop 31 (+ x (* y (bvchop 31 z))))
                  (bvchop 31 (+ x (* y z))))))

(defthm bvchop-31-of-*-of-2147483648
  (IMPLIES (INTEGERP X)
           (EQUAL (BVCHOP 31 (* 2147483648 X))
                  0))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm bvchop-31-of-*-of-logapp-31
  (IMPLIES (AND (INTEGERP X)
                (INTEGERP Y))
           (EQUAL (BVCHOP 31 (* X (LOGAPP 31 Y -1)))
                  (BVCHOP 31 (* X Y))))
  :hints (("Goal" :in-theory (enable logapp))))

;FIXME first prove some more general theorems about logbitp and bvchop
;FIXME gen the 32
;FIXME rename
(defthm int-lemma4a
  (implies (and (integerp x)
                (integerp y))
           (equal (acl2::logext 32 (* x (acl2::logext 32 y)))
                  (acl2::logext 32 (* x y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :cases ((evenp x))
           :in-theory (e/d (LOGEXT
                            logapp logbitp
                            BVCHOP
                            mod
                            oddp) (LOGBITP-IFF-GETBIT
                            EQUAL-OF-*-2-OF-FLOOR-OF-2-SAME)))))



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
  :hints (("Goal" :in-theory (enable bvchop ODDP  EVENP-BECOMES-MOD-FACT))))

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

;(in-theory (disable logextu-as-bvchop))

(defthm logext-of-bvchop-smaller
  (implies (and (integerp x) ;drop
                (<= size n)
                (integerp n)
                (integerp size)
                (< 0 size))
           (equal (logext size (bvchop n x))
                  (logext size x)))
  :hints (("Goal" :in-theory (enable logext))))

(DEFTHM LOGEXT-OF-BVCHOP-SMALLER-better
  (IMPLIES (AND ;(INTEGERP X)
            (<= SIZE N)
        ;    (INTEGERP X)
            (INTEGERP N)
            (INTEGERP SIZE)
            (< 0 SIZE))
           (EQUAL (LOGEXT SIZE (BVCHOP N X))
                  (LOGEXT SIZE X)))
  :HINTS (("Goal" :cases ((integerp x)):IN-THEORY (E/d (LOGEXT) (;LOGBITP-BVCHOP
                                            )))))

(defthm signed-byte-p-of-logext
  (implies (and (>= size1 size)
                (> size 0)
                (integerp size1)
                (integerp size))
           (equal (signed-byte-p size1 (logext size i))
                  t)))

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

(defthm logext-of-bvchop-same
  (implies (posp size)
           (equal (logext size (bvchop size x))
                  (logext size x)))
  :hints (("Goal" :cases ((integerp size))
           :in-theory (enable logext))))

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
                               LOGEXT-BVCHOP-BETTER
                               logext-of-bvchop-smaller-better))))

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
  (implies (and (posp size)
                ;; (<= (- (expt 2 (+ -1 size))) x) ;todo
                (natp x))
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

(defthmd logext-when-positive
  (implies (and (equal 0 (getbit (+ -1 size) x))
                (posp size))
           (equal (logext size x)
                  (bvchop (+ -1 size) x)))
  :hints (("Goal" :in-theory (enable logext))))

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
                (< 0 k)
                (natp k)
                (<= k (expt 2 (+ -1 n)))
                (< x k)
                (unsigned-byte-p n x)
                (natp n)
                (< 0 n))
           (< (logext n x) k))
  :hints (("Goal" :in-theory (enable ;logext
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
