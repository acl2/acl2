; Arithmetic helpers for IEEE floating point spec
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: use an IEEE package?

(include-book "kestrel/arithmetic-light/log2" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; in case we are not enforcing either normal form
(defthm -of-*-of--
  (equal (- (* -1 x))
         (fix x)))

(defthm *-of-2-and-expt-of-+-of--1
  (implies (integerp i)
           (equal (* 2 (expt 2 (+ -1 i)))
                  (expt 2 i))))



;rename
(defun expt-induct (r i k)
  (declare (xargs :measure (abs (ifix i))))
  (cond ((zip i) (list r i k))
        ((= (fix r) 0) 0)
        ((> i 0) (* r (expt-induct r (+ i -1) (/ k 2))))
        (t (* (/ r) (expt-induct r (+ i 1) (* k 2))))))

(defthm log2-of-+-of-*-of-2-and-expt-of-+-of-1
  (implies (and (<= 0 k)
                (rationalp k)
                (integerp i))
           (equal (log2 (+ (* 2 k) (expt 2 (+ 1 i))))
                  (+ 1 (log2 (+ k (expt 2 i))))))
  :hints (("Goal" :use (:instance log2-of-*-of-2
                                  (x (+ k (expt 2 i))))
           :in-theory (e/d (expt-of-+)
                           (log2-of-*-of-2
                            log2-of-expt)))))

(defthm log2-of-+-of-*-of-1/2-and-expt-of-+-of--1
  (implies (and (<= 0 k)
                (rationalp k)
                (integerp i))
           (equal (log2 (+ (* 1/2 k) (expt 2 (+ -1 i))))
                  (+ -1 (log2 (+ k (expt 2 i))))))
  :hints (("Goal" :use (:instance log2-of-*-of-1/2
                                  (x (+ k (expt 2 i))))
           :in-theory (e/d (expt-of-+)
                           (log2-of-*-of-1/2
                            log2-of-expt)))))

(defthm log2-of-+-of-expt-and-small
  (implies (and (integerp i)
                (rationalp k)
                (<= 0 k)
                (< k (expt 2 i)))
           (equal (log2 (+ (expt 2 i) k))
                  i))
  :hints (("Goal" :induct (expt-induct 2 i k)
           :in-theory (enable log2 expt))))

(defthm <-of-*-and-*-cancel-arg3-all-and-all
  (implies (and (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (< (* x1 x2 y) y)
                  (< (* x1 x2) 1)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x2 1)
                                  (x1 (* x1 x2)))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <-of-*-of-expt-of-+-of-1-and---and-1
  (implies (integerp p)
           (equal (< (* x (expt 2 (+ 1 (- p)))) 1)
                  (< x (expt 2 (- p 1)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <-of-+-of---arg1
  (equal (< (+ (- x) y) z)
         (< y (+ x z)))
  :hints (("Goal" :cases ((< y x)))))

(defthm <-of-+-of---arg2
  (equal (< (+ y (- x)) z)
         (< y (+ x z))))

(defthm <-of-+-of---arg3
  (equal (< (+ y1 y2 (- x)) z)
         (< (+ y1 y2) (+ x z))))

(defthm <-of-+-of---arg3-alt
  (equal (< z (+ y1 y2 (- x)))
         (< (+ x z) (+ y1 y2))))

(defthm +-of-expt-of-+-of--1-and-same
 (implies (integerp i)
          (equal (+ (expt 2 (+ -1 i))
                    (expt 2 (+ -1 i)))
                 (expt 2 i))))

(defthm type-helper
   (implies (<= p k)
            (<= 0 (+ k (- p))))
   :rule-classes :type-prescription)

(defthm integerp-of-expt-type-helper
   (implies (<= p k)
            (integerp (expt 2 (+ k (- p)))))
   :rule-classes :type-prescription)


(defthm log2-of-*-of-expt
  (implies (and (integerp i)
                (< 0 x)
                (rationalp x))
           (equal (log2 (* x (expt 2 i)))
                  (+ i (log2 x))))
  :hints (("Goal" :in-theory (enable expt log2))))

(defthm log2-of-*-of-expt-arg3
  (implies (and (integerp i)
                (< 0 (* x1 x2))
                (rationalp x1)
                (rationalp x2))
           (equal (log2 (* x1 x2 (expt 2 i)))
                  (+ i (log2 (* x1 x2)))))
  :hints (("Goal" :use (:instance log2-of-*-of-expt (x (* x1 x2)))
           :in-theory (disable log2-of-*-of-expt))))

(defthm log2-of-*-of-expt-arg2+
  (implies (and (integerp i)
                (< 0 (* x1 x2))
                (rationalp x1)
                (rationalp x2))
           (equal (log2 (* x1 (expt 2 i) x2))
                  (+ i (log2 (* x1 x2)))))
  :hints (("Goal" :use (:instance log2-of-*-of-expt (x (* x1 x2)))
           :in-theory (disable log2-of-*-of-expt))))

(defthm cancel-helper
  (equal (< (+ x1 x2 x3 y) (+ x4 y))
         (< (+ x1 x2 x3) x4)))

(defthm <-of-log2-when-<-of-expt-linear
  (implies (and (< x (expt 2 i))
                (integerp i)
                (< 0 x)
                (rationalp x))
           (< (log2 x) i))
  :rule-classes :linear)

(defthm <-of-*-cancel-2+
  (implies (and (< 0 z)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (* x z y) z)
                  (< (* x y) 1))))

(defthm <-of----and-*-+-of-*-arg2+
  (implies (and (< 0 z)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (- z) (+ z (* x z y)))
                  (< -1 (+ 1 (* x y)))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel-gen
                                  (y z)
                                  (x1 -1)
                                  (x2 (+ 1 (* x y)))))))

(defthm <-of---of-*-arg2+
  (implies (and (< 0 z)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (- (* x z y)) z)
                  (< (- (* x y)) 1)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel-gen
                                  (y z)
                                  (x1 (- (* x y)))
                                  (x2 1))
           :in-theory (disable <-of-*-and-*-cancel-arg3-all-and-all))))

(defthm <-of-*-arg2+-and-+-both
  (implies (and (< 0 z)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (* x z y) (+ z z))
                  (< (* x y) 2)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel-gen
                                  (y z)
                                  (x1 (* x y))
                                  (x2 2))
           :in-theory (disable <-of-*-and-*-cancel-arg3-all-and-all))))

(defthm integerp-of-*-of-1/2-and-expt-and-/-of-expt
  (implies (and (integerp k)
                (integerp p))
           (equal (integerp (* 1/2 (expt 2 k) (/ (expt 2 p))))
                  (<= 1 (+ k (- p)))))
  :hints (("Goal" :use (:instance integerp-of-expt2 (i (+ k -1 (- p))))
           :in-theory (e/d (expt-of-+) (integerp-of-expt2
                                        integerp-of-expt-when-natp)))))

(defthmd <=-of-expt-of-2-when-<=-of-log2
  (implies (and (<= i (log2 x))
                (integerp i)
                (rationalp x)
                (< 0 x)
                )
           (<= (expt 2 i) x)))

(defthmd *-of-expt-and-expt
  (implies (and (integerp i)
                (integerp j)
                (acl2-numberp r)
                (not (equal 0 r)))
           (equal (* (expt r i) (expt r j))
                  (expt r (+ i j))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(theory-invariant (incompatible (:rewrite *-of-expt-and-expt) (:rewrite expt-of-+)))

(defthmd *-of-/-of-expt-and-expt
  (implies (and (integerp i)
                (integerp j)
                (acl2-numberp r)
                (not (equal 0 r)))
           (equal (* (/ (expt r i)) (expt r j))
                  (expt r (+ (- i) j))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(theory-invariant (incompatible (:rewrite *-of-/-of-expt-and-expt) (:rewrite expt-of--)))

(defthm <-of-0-and-+-of--
  (equal (< 0 (+ x (- y)))
         (< y x)))

(defthm <-of-log2-of-+-of-expt-and--
  (implies (and (< 0 x)
                (< x (expt 2 i)) ; so we don't call log2 on a non-positive number
                (integerp i)
                (rationalp x))
           (< (log2 (+ (expt 2 i) (- x)))
              i))
  :rule-classes :linear
  :hints (("Goal" :induct (expt-induct 2 i x)
           :in-theory (enable log2 expt)))
  )

(defthm log2-of-+-of--of-*-of-2-and-expt-of-+-of-1
  (implies (and (<= 0 k)
                (rationalp k)
                (< k (expt 2 i))
                (integerp i))
           (equal (log2 (+ (- (* 2 k)) (expt 2 (+ 1 i))))
                  (+ 1 (log2 (+ (- k) (expt 2 i))))))
  :hints (("Goal" :use (:instance log2-of-*-of-2
                                  (x (+ (- k) (expt 2 i))))
           :in-theory (e/d (expt-of-+)
                           (log2-of-*-of-2
                            log2-of-expt)))))

(defthm log-is--1
  (implies (and (<= 1/2 x)
                (< x 1)
                (rationalp x))
           (equal (log2 x)
                  -1))
  :hints (("Goal" :expand (log2 x)
           :in-theory (e/d () (log2-of-*-of-2)))))

(defthm log2-of-+-of-expt-and---when-small
  (implies (and (< 0 x)
                (<= x (expt 2 (+ -1 i)))
                (integerp i)
                (rationalp x))
           (equal (log2 (+ (expt 2 i) (- x)))
                  (- i 1)))
  :hints (("Goal" :induct (expt-induct 2 i x)
           :expand (log2 (+ (- x) (expt 2 i)))
           :in-theory (enable log2 expt-of-+)))
  )

(defthm log2-of-+-of-expt2-and-small
  (implies (and (< j i)
                (integerp i)
                (integerp j))
           (equal (log2 (+ (expt 2 i) (- (expt 2 j))))
                  (- i 1)))
  :hints (("Goal" :cases ((< (log2 (+ (expt 2 i) (- (expt 2 j))))
                             (- i 1))
                          (> (log2 (+ (expt 2 i) (- (expt 2 j))))
                             (- i 1)))
           :in-theory (enable log2))))

(defthm <-of-log2-arg1
  (implies (and (rationalp rat)
                (< 0 rat)
                (integerp i))
           (equal (< (log2 rat) i)
                  (< rat (expt 2 i)))))

(defthm <=-of-+-of-1-and-log2-arg1
  (implies (and (rationalp rat)
                (< 0 rat)
                (integerp i))
           (equal (< i (+ 1 (log2 rat)))
                  (not (< rat (expt 2 i))))))

(defthmd <=-of-+-and-+-when-<=-and-<=
  (implies (and (<= x1 x2)
                (<= y1 y2))
           (<= (+ x1 y1) (+ x2 y2))))

;;gen?
(defthmd <=-of-*-and-*-when-<=-and-<=
  (implies (and (<= x1 x2)
                (<= y1 y2)
                (<= 0 x1)
                ;(<= 0 x2)
                ;; (<= 0 y1)
                (<= 0 y2)
                (rationalp x1)
                (rationalp x2)
                (rationalp y1)
                (rationalp y2))
           (<= (* x1 y1) (* x2 y2))))

(defthm <-of-2-and-expt2
  (implies (integerp i)
           (equal (< 2 (expt 2 i))
                  (< 1 i))))

;could be expensive?
(defthm <=-of-2-and-expt2-linear
  (implies (and (< 0 i)
                (integerp i))
           (<= 2 (expt 2 i)))
  :rule-classes :linear)
