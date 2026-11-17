;; Copyright 2026 Google LLC
;; Use of this source code is governed by a BSD-style license that can be
;; found in the LICENSE file.

(in-package "ACL2")

;; Prove that the sum of the interior angles of a triangle is 180 degrees.
;;
;; An angle is represented in two ways: 1) as a nonzero complex number
;;                                      2) as a turn number and a nonzero complex number
;;
;; 1) represents radians that are a priori in the range [0, 2*pi) .
;; 2) can represent angles outside the range [0, 2*pi) via the formula n*2*pi + w, where
;;      n is an integer and w is an angle in format 1
;;
;; Logically, format 2 exists so that we can check overflow and underflow and prove that
;; the sum of the angles really is 180 degrees, and not just congruent to 180 degrees
;; modulo 360.

(defun nonzero-complexp (z)
  (and (acl2-numberp z)
       (not (equal z 0))))

(thm (nonzero-complexp 1))
(thm (not (nonzero-complexp 0)))
(thm (not (nonzero-complexp "a")))

(defun nonzero-complex-fix (z)
  (if (nonzero-complexp z)
      z
      1))

(defun angle-equiv-up-to-180 (z w)
  (let ((z (nonzero-complex-fix z))
        (w (nonzero-complex-fix w)))
    (real/rationalp (/ z w))))

(thm (angle-equiv-up-to-180 1 -1))
(thm (not (angle-equiv-up-to-180 1 #C(0 1))))

(defun angle-equiv (z w)
  (let ((z (nonzero-complex-fix z))
        (w (nonzero-complex-fix w)))
    (and (real/rationalp (/ z w))
         (< 0 (/ z w)))))

(encapsulate ()
             (local (include-book "arithmetic-5/top" :dir :system))

             (local
              (defthm quotient-symm-ident
                  (equal (* (/ x) y)
                         (/ (* x (/ y))))
                :rule-classes nil))

             (local
              (defthm real/rationalp-quotient-symm
                  (implies (real/rationalp (* x (/ y)))
                           (real/rationalp (* (/ x) y)))
                :hints (("Goal" :use quotient-symm-ident
                                :in-theory (disable |(/ (* x y))|)))))

             (local
              (defthm positive-quotient-symm
                  (implies (and (real/rationalp (* x (/ y)))
                                (< 0 (* x (/ y))))
                           (< 0 (* (/ x) y)))
                :hints (("Goal" :use quotient-symm-ident
                                :in-theory (disable |(/ (* x y))|)))))

             (local
              (defthm quotient-trans-ident
                  (implies (and (acl2-numberp y)
                                (not (equal y 0)))
                           (equal (* (* x (/ y)) (* y (/ z)))
                                  (* x (/ z))))
                :rule-classes nil))

             (local
              (defthm real/rationalp-quotient-trans
                  (implies (and (acl2-numberp y)
                                (not (equal y 0))
                                (real/rationalp (* x (/ y)))
                                (real/rationalp (* y (/ z))))
                           (real/rationalp (* x (/ z))))
                :hints (("Goal" :use quotient-trans-ident
                                :in-theory (disable |(* (* x y) z)| |(* y (* x z))|)))))

             (local
              (defthm positive-quotient-trans
                  (implies (and (acl2-numberp y)
                                (not (equal y 0))
                                (real/rationalp (* x (/ y)))
                                (real/rationalp (* y (/ z)))
                                (< 0 (* x (/ y)))
                                (< 0 (* y (/ z))))
                           (< 0 (* x (/ z))))
                :hints (("Goal" :use quotient-trans-ident
                                :in-theory (disable |(* (* x y) z)| |(* y (* x z))|)))))

             (defequiv angle-equiv-up-to-180)
             (defequiv angle-equiv)
             (defrefinement angle-equiv angle-equiv-up-to-180))

(defun angle (a b c)
  (/ (- c b) (- a b)))

(defun triangle-angles-product (a b c)
  (* (angle a b c)
     (angle b c a)
     (angle c a b)))

(local
 (encapsulate ()
              (local (include-book "arithmetic-5/top" :dir :system))

              (defthm product-of-three-negated-ratios
                  (implies (and (acl2-numberp x)
                                (acl2-numberp y)
                                (acl2-numberp z))
                           (or (equal (* (* (- x) (/ y))
                                         (* (- z) (/ x))
                                         (* (- y) (/ z)))
                                      0)
                               (equal (* (* (- x) (/ y))
                                         (* (- z) (/ x))
                                         (* (- y) (/ z)))
                                      -1)))
                :rule-classes nil)

              (defthm angle-as-negated-ratio
                  (equal (angle a b c)
                         (* (- (- b c)) (/ (- a b)))))))

(local
 (defthm triangle-angles-product-is-0-or--1
     (or (equal (triangle-angles-product a b c) 0)
         (equal (triangle-angles-product a b c) -1))
   :hints (("Goal" :use (:instance product-of-three-negated-ratios
                                   (x (- b c))
                                   (y (- a b))
                                   (z (- c a)))
                   :in-theory (e/d (angle-as-negated-ratio)
                                   (angle distributivity
                                          distributivity-of-minus-over-+
                                          commutativity-of-*
                                          associativity-of-*))))
   :rule-classes nil))

(defthm triangle-angles-product-equiv-up-to-180
    (angle-equiv-up-to-180 (triangle-angles-product a b c) 1)
  :hints (("Goal" :use triangle-angles-product-is-0-or--1
                  :in-theory (disable triangle-angles-product))))

(defun turn-count-and-angle-p (x)
  (and (consp x)
       (consp (cdr x))
       (null (cddr x))
       (integerp (car x))
       (nonzero-complexp (cadr x))))

(defun turn-count-and-angle-fix (x)
  (if (turn-count-and-angle-p x)
      x
      '(0 1)))

(defun detect-inbounds-angle*-strict-upper-half-plane (z w)
  (let ((z (nonzero-complex-fix z))
        (w (nonzero-complex-fix w)))
    (and (< 0 (imagpart z))
         (< 0 (imagpart w))
         (< 0 (imagpart (* z w))))))

(defun detect-inbounds-angle*-strict-upper-half-plane-and-arbitrary (z w)
  (let ((z (nonzero-complex-fix z))
        (w (nonzero-complex-fix w)))
    (and (< 0 (imagpart z))
         (or (< 0 (imagpart w))
             (angle-equiv w 1)
             (angle-equiv w -1)
             (< 0 (imagpart (- (* z w))))))))

(defun detect-inbounds-angle* (z w)
  (or (angle-equiv z 1)
      (angle-equiv w 1)
      (detect-inbounds-angle*-strict-upper-half-plane-and-arbitrary z w)
      (detect-inbounds-angle*-strict-upper-half-plane-and-arbitrary w z)))

(defun angle-* (x y)
  (let* ((x (turn-count-and-angle-fix x))
         (y (turn-count-and-angle-fix y))
         (z (cadr x))
         (w (cadr y)))
    (list (+ (car x)
             (car y)
             (if (detect-inbounds-angle* z w) 0 1))
          (* z w))))

(local
 (defthm commutativity-of-detect-inbounds-angle*
     (equal (detect-inbounds-angle* z w)
            (detect-inbounds-angle* w z))
   :hints (("Goal" :in-theory (disable angle-equiv
                                       detect-inbounds-angle*-strict-upper-half-plane-and-arbitrary)))))

(defthm commutativity-of-angle-*
    (equal (angle-* x y)
           (angle-* y x))
  :hints (("Goal" :in-theory (disable turn-count-and-angle-fix
                                      detect-inbounds-angle*))))


(defun upper-half-plane-p (z)
  (let ((z (nonzero-complex-fix z)))
    (or (< 0 (imagpart z))
        (and (equal (imagpart z) 0)
             (< 0 (realpart z))))))

(defun uhp-fix (z)
  (let ((z (nonzero-complex-fix z)))
    (if (upper-half-plane-p z)
        z
        (- z))))

(local
 (encapsulate ()
              (local (set-override-hints nil))
              (local (include-book "arithmetic-5/top" :dir :system))
              (local (set-default-hints
                      '((nonlinearp-default-hint++ id stable-under-simplificationp hist nil))))

              (defthm realpart-of-uminus
                  (equal (realpart (- x))
                         (- (realpart x)))
                :hints (("Goal" :use (:instance realpart-+ (x x) (y (- x)))
                                :in-theory (disable realpart-+))))

              (defthm imagpart-of-uminus
                  (equal (imagpart (- y))
                         (- (imagpart y)))
                :hints (("Goal" :use (:instance imagpart-+ (x y) (y (- y)))
                                :in-theory (disable imagpart-+))))

              (local
               (defthm mult-def-complex
                   (equal (* x y)
                          (complex (- (* (realpart x) (realpart y))
                                      (* (imagpart x) (imagpart y)))
                                   (+ (* (realpart x) (imagpart y))
                                      (* (imagpart x) (realpart y)))))
                 :hints (("Goal" :use ((:instance complex-definition
                                                  (x (- (* (realpart x) (realpart y))
                                                        (* (imagpart x) (imagpart y))))
                                                  (y (+ (* (realpart x) (imagpart y))
                                                        (* (imagpart x) (realpart y)))))
                                       (:instance complex-definition
                                                  (x (realpart x))
                                                  (y (imagpart x)))
                                       (:instance complex-definition
                                                  (x (realpart y))
                                                  (y (imagpart y))))))
                 :rule-classes nil))

              (defthm realpart-*
                  (equal (realpart (* x y))
                         (- (* (realpart x) (realpart y))
                            (* (imagpart x) (imagpart y))))
                :hints (("Goal" :use mult-def-complex)))

              (defthm imagpart-*
                  (equal (imagpart (* x y))
                         (+ (* (realpart x) (imagpart y))
                            (* (imagpart x) (realpart y))))
                :hints (("Goal" :use mult-def-complex)))

              (defthm realpart-when-real/rationalp
                  (implies (real/rationalp x)
                           (equal (realpart x) x))
                :hints (("Goal" :use ((:instance complex-definition (x x) (y 0))
                                      (:instance realpart-complex (x x) (y 0)))
                                :in-theory (disable realpart-complex))))

              (defthm imagpart-when-real/rationalp
                  (implies (real/rationalp x)
                           (equal (imagpart x) 0))
                :hints (("Goal" :use ((:instance complex-definition (x x) (y 0))
                                      (:instance imagpart-complex (x x) (y 0)))
                                :in-theory (disable imagpart-complex))))

              (defthm nonzero-complexp-of-*
                  (implies (and (nonzero-complexp u)
                                (nonzero-complexp v))
                           (nonzero-complexp (* u v))))

              (defthm nonzero-complexp-of-uminus
                  (implies (nonzero-complexp u)
                           (nonzero-complexp (- u))))

              (defthm angle-equiv-1-rewrite
                  (equal (angle-equiv z 1)
                         (let ((z (nonzero-complex-fix z)))
                           (and (equal (imagpart z) 0)
                                (< 0 (realpart z)))))
                :hints (("Goal" :use (:instance complex-definition
                                                (x (realpart (nonzero-complex-fix z)))
                                                (y (imagpart (nonzero-complex-fix z)))))))

              (defthm angle-equiv--1-rewrite
                  (equal (angle-equiv z -1)
                         (let ((z (nonzero-complex-fix z)))
                           (and (equal (imagpart z) 0)
                                (< (realpart z) 0))))
                :hints (("Goal" :use (:instance complex-definition
                                                (x (realpart (nonzero-complex-fix z)))
                                                (y (imagpart (nonzero-complex-fix z)))))))

              (defthm upper-half-plane-p-of-uminus
                  (implies (nonzero-complexp z)
                           (equal (upper-half-plane-p (- z))
                                  (not (upper-half-plane-p z))))
                :hints (("Goal" :use (:instance complex-definition
                                                (x (realpart z))
                                                (y (imagpart z))))))

              (local
               (defthm expt-2-nonnegative
                   (implies (real/rationalp x)
                            (<= 0 (expt x 2)))
                 :hints (("Goal" :cases ((< x 0))))
                 :rule-classes (:linear :type-prescription :rewrite)))

              (local
               (defthm realpart-v-from-imagpart-*-0
                   (implies (and (< 0 (imagpart u))
                                 (equal (+ (* (realpart u) (imagpart v))
                                           (* (imagpart u) (realpart v)))
                                        0))
                            (equal (realpart v)
                                   (- (* (realpart u) (imagpart v) (/ (imagpart u))))))))

              (defthm realpart-*-positive-when-imagpart-*-0
                  (implies (and (< 0 (imagpart u))
                                (< (imagpart v) 0)
                                (equal (+ (* (realpart u) (imagpart v))
                                          (* (imagpart u) (realpart v)))
                                       0))
                           (< (* (imagpart u) (imagpart v))
                              (* (realpart u) (realpart v)))))

              (local (in-theory (disable realpart-v-from-imagpart-*-0)))

              (defthm detect-inbounds-angle*-as-upper-half-plane
                  (equal (detect-inbounds-angle* u v)
                         (cond ((and (upper-half-plane-p u)
                                     (upper-half-plane-p v))
                                t)
                               ((and (not (upper-half-plane-p u))
                                     (not (upper-half-plane-p v)))
                                nil)
                               (t (not (upper-half-plane-p (* (nonzero-complex-fix u)
                                                              (nonzero-complex-fix v)))))))
                :hints (("Goal" :in-theory (disable angle-equiv)
                                :use ((:instance realpart-*-positive-when-imagpart-*-0
                                                 (u (nonzero-complex-fix u))
                                                 (v (nonzero-complex-fix v)))
                                      (:instance realpart-*-positive-when-imagpart-*-0
                                                 (u (nonzero-complex-fix v))
                                                 (v (nonzero-complex-fix u)))
                                      (:instance complex-definition
                                                 (x (realpart (nonzero-complex-fix u)))
                                                 (y (imagpart (nonzero-complex-fix u))))
                                      (:instance complex-definition
                                                 (x (realpart (nonzero-complex-fix v)))
                                                 (y (imagpart (nonzero-complex-fix v))))))))

              (local
               (defthm imagpart-triple-product-identity
                   (equal (* (imagpart (* a b))
                             (imagpart (* b c)))
                          (+ (* (imagpart b) (imagpart (* a (* b c))))
                             (* (+ (* (realpart b) (realpart b))
                                   (* (imagpart b) (imagpart b)))
                                (imagpart a)
                                (imagpart c))))
                 :rule-classes nil))

              (local
               (defthm uhp-triple-strict-imagpart-lemma
                   (implies (and (< 0 (imagpart a))
                                 (< 0 (imagpart b))
                                 (< 0 (imagpart c))
                                 (<= 0 (imagpart (* a b)))
                                 (<= (imagpart (* b c)) 0))
                            (< (imagpart (* a (* b c))) 0))
                 :hints (("Goal" :in-theory (disable imagpart-* realpart-*)
                                 :use imagpart-triple-product-identity))))

              (local
               (defthm imagpart-*-when-imagpart-0-left
                   (implies (equal (imagpart a) 0)
                            (equal (imagpart (* a b))
                                   (* (realpart a) (imagpart b))))))

              (local
               (defthm realpart-*-when-imagpart-0-left
                   (implies (equal (imagpart a) 0)
                            (equal (realpart (* a b))
                                   (* (realpart a) (realpart b))))))

              (local
               (defthm imagpart-*-when-imagpart-0-right
                   (implies (equal (imagpart b) 0)
                            (equal (imagpart (* a b))
                                   (* (imagpart a) (realpart b))))))

              (local
               (defthm realpart-*-when-imagpart-0-right
                   (implies (equal (imagpart b) 0)
                            (equal (realpart (* a b))
                                   (* (realpart a) (realpart b))))))

              (defthm uhp-triple-lemma
                  (implies (and (nonzero-complexp a)
                                (nonzero-complexp b)
                                (nonzero-complexp c)
                                (upper-half-plane-p a)
                                (upper-half-plane-p b)
                                (upper-half-plane-p c)
                                (upper-half-plane-p (* a b))
                                (not (upper-half-plane-p (* b c))))
                           (not (upper-half-plane-p (* a (* b c)))))
                :hints (("Goal" :in-theory (disable imagpart-* realpart-*)
                                :use uhp-triple-strict-imagpart-lemma)))

              (defthm upper-half-plane-p-of-uhp-fix
                  (upper-half-plane-p (uhp-fix z))
                :hints (("Goal" :in-theory (disable upper-half-plane-p))))

              (defthm nonzero-complexp-of-uhp-fix
                  (nonzero-complexp (uhp-fix z))
                :hints (("Goal" :in-theory (disable upper-half-plane-p))))

              (defthm upper-half-plane-p-of-*-uhp-fix-2
                  (implies (and (nonzero-complexp u)
                                (nonzero-complexp v))
                           (equal (upper-half-plane-p (* (uhp-fix u) (uhp-fix v)))
                                  (equal (equal (upper-half-plane-p u)
                                                (upper-half-plane-p v))
                                         (upper-half-plane-p (* u v)))))
                :hints (("Goal" :in-theory (disable upper-half-plane-p))))

              (defthm upper-half-plane-p-of-*-uhp-fix-3
                  (implies (and (nonzero-complexp u)
                                (nonzero-complexp v)
                                (nonzero-complexp w))
                           (equal (upper-half-plane-p (* (uhp-fix u) (* (uhp-fix v) (uhp-fix w))))
                                  (equal (equal (upper-half-plane-p u)
                                                (equal (upper-half-plane-p v)
                                                       (upper-half-plane-p w)))
                                         (upper-half-plane-p (* u (* v w))))))
                :hints (("Goal" :in-theory (disable upper-half-plane-p))))

              (defthm detect-inbounds-angle*-carry-associative
                  (implies (and (nonzero-complexp u)
                                (nonzero-complexp v)
                                (nonzero-complexp w))
                           (equal (+ (if (detect-inbounds-angle* u v) 0 1)
                                     (if (detect-inbounds-angle* (* u v) w) 0 1))
                                  (+ (if (detect-inbounds-angle* v w) 0 1)
                                     (if (detect-inbounds-angle* u (* v w)) 0 1))))
                :hints (("Goal" :in-theory (disable detect-inbounds-angle*
                                                    upper-half-plane-p
                                                    uhp-fix)
                                :use ((:instance uhp-triple-lemma
                                                 (a (uhp-fix u))
                                                 (b (uhp-fix v))
                                                 (c (uhp-fix w)))
                                      (:instance uhp-triple-lemma
                                                 (a (uhp-fix w))
                                                 (b (uhp-fix v))
                                                 (c (uhp-fix u)))))))

              (defthm turn-count-and-angle-p-of-turn-count-and-angle-fix
                  (turn-count-and-angle-p (turn-count-and-angle-fix x)))

              (defthm turn-count-and-angle-fix-when-turn-count-and-angle-p
                  (implies (turn-count-and-angle-p x)
                           (equal (turn-count-and-angle-fix x) x)))

              (defthm turn-count-and-angle-fix-of-list
                  (implies (and (integerp n)
                                (nonzero-complexp z))
                           (equal (turn-count-and-angle-fix (list n z))
                                  (list n z))))

              (defthm integerp-of-car-turn-count-and-angle-fix
                  (integerp (car (turn-count-and-angle-fix x)))
                :rule-classes (:rewrite :type-prescription))

              (defthm acl2-numberp-of-car-turn-count-and-angle-fix
                  (acl2-numberp (car (turn-count-and-angle-fix x)))
                :rule-classes (:rewrite :type-prescription))

              (defthm nonzero-complexp-of-cadr-turn-count-and-angle-fix
                  (nonzero-complexp (cadr (turn-count-and-angle-fix x))))

              (defthm acl2-numberp-of-cadr-turn-count-and-angle-fix
                  (acl2-numberp (cadr (turn-count-and-angle-fix x)))
                :rule-classes (:rewrite :type-prescription))

              (defthm turn-count-and-angle-p-of-angle-*
                  (turn-count-and-angle-p (angle-* x y))
                :hints (("Goal" :in-theory (disable turn-count-and-angle-fix
                                                    nonzero-complexp
                                                    detect-inbounds-angle*
                                                    detect-inbounds-angle*-as-upper-half-plane))))

              (defthm commutativity-2-of-*
                  (equal (* x (* y z))
                         (* y (* x z))))

              (defthm associativity-of-angle*-lemma-1
                  (equal (* (cadr z) (cadr x) (cadr y))
                         (* (cadr x) (cadr y) (cadr z))))))

(defthm associativity-of-angle*-lemma-3
    (implies (acl2-numberp y)
             (iff (< (imagpart (- y)) 0)
                  (< 0 (imagpart y)))))

(defthm associativity-of-angle*-lemma-2
    (implies (and (< 0 y)
                  (real/rationalp y)
                  (< 0 (imagpart z)))
             (< 0 (imagpart (* y z)))))

(defthm associativity-of-angle*
    (equal (angle-* (angle-* x y) z)
           (angle-* x (angle-* y z)))
  :hints (("Goal" :use (:instance detect-inbounds-angle*-carry-associative
                                  (u (cadr (turn-count-and-angle-fix x)))
                                  (v (cadr (turn-count-and-angle-fix y)))
                                  (w (cadr (turn-count-and-angle-fix z))))
                  :in-theory (disable turn-count-and-angle-fix
                                      turn-count-and-angle-p
                                      detect-inbounds-angle*
                                      detect-inbounds-angle*-as-upper-half-plane
                                      detect-inbounds-angle*-carry-associative
                                      commutativity-of-angle-*))))

(defun collinear-p (a b c)
  (angle-equiv-up-to-180 (angle a b c) 1))

(local
 (encapsulate ()
              (local (set-override-hints nil))
              (local (include-book "arithmetic-5/top" :dir :system))
              (local (set-default-hints '((nonlinearp-default-hint++ id stable-under-simplificationp
                                           hist nil))))

              (local
               (defthm imagpart-*-0-and-realpart-*--1-implies-positive-imagpart
                   (implies (and (acl2-numberp w)
                                 (acl2-numberp q)
                                 (< 0 (imagpart w))
                                 (equal (imagpart (* w q)) 0)
                                 (equal (realpart (* w q)) -1))
                            (< 0 (imagpart q)))
                 :hints (("Goal" :use (:instance realpart-*-positive-when-imagpart-*-0
                                                 (u w)
                                                 (v q))
                                 :in-theory (enable realpart-* imagpart-*)))))

              (defthm product--1-preserves-positive-imagpart
                  (implies (and (acl2-numberp w)
                                (acl2-numberp q)
                                (equal (* w q) -1)
                                (< 0 (imagpart w)))
                           (< 0 (imagpart q)))
                :hints (("Goal" :in-theory (disable imagpart-* realpart-*)
                                :use imagpart-*-0-and-realpart-*--1-implies-positive-imagpart)))

              (defthm product--1-preserves-negative-imagpart
                  (implies (and (acl2-numberp w)
                                (acl2-numberp q)
                                (equal (* w q) -1)
                                (< (imagpart w) 0))
                           (< (imagpart q) 0))
                :hints (("Goal" :in-theory (disable imagpart-* realpart-*)
                                :use (:instance product--1-preserves-positive-imagpart
                                                (w (- w))
                                                (q (- q))))))

              (local
               (defthm ratio-minus-1-times-neg-inverse
                   (implies (and (acl2-numberp x)
                                 (acl2-numberp z)
                                 (not (equal x 0))
                                 (not (equal z 0)))
                            (equal (* (+ -1 (* (+ x z) (/ x)))
                                      (* (- x) (/ z)))
                                   -1))))

              (defthm angle-minus-1-times-next-angle
                  (implies (and (not (equal (- a b) 0))
                                (not (equal (- c a) 0)))
                           (equal (* (+ -1 (angle a b c))
                                     (angle c a b))
                                  -1))
                :hints (("Goal" :use (:instance ratio-minus-1-times-neg-inverse
                                                (x (- a b))
                                                (z (- c a))))))

              (defthm triangle-angles-product-when-nondegen
                  (implies (and (not (equal (- a b) 0))
                                (not (equal (- b c) 0))
                                (not (equal (- c a) 0)))
                           (equal (* (angle a b c)
                                     (* (angle b c a)
                                        (angle c a b)))
                                  -1))
                :hints (("Goal" :use (:instance product-of-three-negated-ratios
                                                (x (- b c))
                                                (y (- a b))
                                                (z (- c a)))
                                :in-theory (e/d (angle-as-negated-ratio)
                                                (angle)))))

              (local
               (defthm equal-diff-sum
                   (equal (+ (- a b) (- c a))
                          (- c b))))

              (local
               (defthm imagpart-of-self-quotient
                   (equal (imagpart (* x (/ x))) 0)
                 :hints (("Goal" :cases ((equal (fix x) 0))))))

              (defthm diffs-nonzero-when-imagpart-angle-nonzero
                  (implies (not (equal (imagpart (angle a b c)) 0))
                           (and (not (equal (- a b) 0))
                                (not (equal (- b c) 0))
                                (not (equal (- c b) 0))
                                (not (equal (- c a) 0))
                                (not (equal (- a c) 0))
                                (not (equal (- b a) 0))))
                :hints (("Goal" :use (equal-diff-sum
                                      (:instance imagpart-of-self-quotient
                                                 (x (- a b))))
                                :in-theory (disable imagpart-*
                                                    imagpart-+
                                                    |(* x (+ y z))|
                                                    |(* a (/ a))|))))

              (defthm angle-equiv-up-to-180-1-rewrite
                  (implies (acl2-numberp z)
                           (equal (angle-equiv-up-to-180 z 1)
                                  (equal (imagpart z) 0)))
                :hints (("Goal" :use (:instance complex-definition
                                                (x (realpart z))
                                                (y (imagpart z))))))

              (defthm acl2-numberp-of-angle
                  (acl2-numberp (angle a b c)))

              (defthm collinear-p-as-imagpart-0
                  (equal (collinear-p a b c)
                         (equal (imagpart (angle a b c)) 0))
                :hints (("Goal" :in-theory (disable angle
                                                    angle-as-negated-ratio
                                                    angle-equiv-up-to-180))))

              (defthm positive-imagpart-chain-for-triangle-angles
                  (implies (< 0 (imagpart (angle a b c)))
                           (and (< 0 (imagpart (angle c a b)))
                                (< 0 (imagpart (angle b c a)))
                                (< 0 (imagpart (* (angle b c a) (angle c a b))))))
                :hints (("Goal" :in-theory (disable angle
                                                    angle-as-negated-ratio
                                                    imagpart-*)
                                :use ((:instance diffs-nonzero-when-imagpart-angle-nonzero)
                                      (:instance angle-minus-1-times-next-angle
                                                 (a a) (b b) (c c))
                                      (:instance angle-minus-1-times-next-angle
                                                 (a c) (b a) (c b))
                                      (:instance triangle-angles-product-when-nondegen)
                                      (:instance product--1-preserves-positive-imagpart
                                                 (w (+ -1 (angle a b c)))
                                                 (q (angle c a b)))
                                      (:instance product--1-preserves-positive-imagpart
                                                 (w (+ -1 (angle c a b)))
                                                 (q (angle b c a)))
                                      (:instance product--1-preserves-positive-imagpart
                                                 (w (angle a b c))
                                                 (q (* (angle b c a) (angle c a b))))))))

              (defthm negative-imagpart-chain-for-triangle-angles
                  (implies (< (imagpart (angle a b c)) 0)
                           (and (< (imagpart (angle c a b)) 0)
                                (< (imagpart (angle b c a)) 0)
                                (< (imagpart (* (angle b c a) (angle c a b))) 0)))
                :hints (("Goal" :in-theory (disable angle
                                                    angle-as-negated-ratio
                                                    imagpart-*)
                                :use ((:instance diffs-nonzero-when-imagpart-angle-nonzero)
                                      (:instance angle-minus-1-times-next-angle
                                                 (a a) (b b) (c c))
                                      (:instance angle-minus-1-times-next-angle
                                                 (a c) (b a) (c b))
                                      (:instance triangle-angles-product-when-nondegen)
                                      (:instance product--1-preserves-negative-imagpart
                                                 (w (+ -1 (angle a b c)))
                                                 (q (angle c a b)))
                                      (:instance product--1-preserves-negative-imagpart
                                                 (w (+ -1 (angle c a b)))
                                                 (q (angle b c a)))
                                      (:instance product--1-preserves-negative-imagpart
                                                 (w (angle a b c))
                                                 (q (* (angle b c a) (angle c a b))))))))

              (local
               (defthm neg-angle-times-reversed-angle
                   (implies (and (not (equal (- a b) 0))
                                 (not (equal (- c b) 0)))
                            (equal (* (- (angle a b c))
                                      (angle c b a))
                                   -1))))

              (defthm imagpart-angle-reversed-sign
                  (and (implies (< 0 (imagpart (angle a b c)))
                                (< (imagpart (angle c b a)) 0))
                       (implies (< (imagpart (angle a b c)) 0)
                                (< 0 (imagpart (angle c b a)))))
                :hints (("Goal" :in-theory (disable angle
                                                    angle-as-negated-ratio
                                                    imagpart-*)
                                :use (diffs-nonzero-when-imagpart-angle-nonzero
                                      neg-angle-times-reversed-angle
                                      (:instance product--1-preserves-negative-imagpart
                                                 (w (- (angle a b c)))
                                                 (q (angle c b a)))
                                      (:instance product--1-preserves-positive-imagpart
                                                 (w (- (angle a b c)))
                                                 (q (angle c b a)))))))

              (defthm nonzero-complexp-when-imagpart-positive
                  (implies (< 0 (imagpart z))
                           (nonzero-complexp z)))

              (defthm nonzero-complexp-when-imagpart-negative
                  (implies (< (imagpart z) 0)
                           (nonzero-complexp z)))

              (defthm upper-half-plane-p-when-imagpart-positive
                  (implies (< 0 (imagpart z))
                           (upper-half-plane-p z)))

              (defthm not-upper-half-plane-p-when-imagpart-negative
                  (implies (< (imagpart z) 0)
                           (not (upper-half-plane-p z))))))

(defthm one-angle-less-than-180-implies-all-angles-less-than-180
    (implies (< 0 (imagpart (angle a b c)))
             (and (< 0 (imagpart (angle b c a)))
                  (< 0 (imagpart (angle c a b)))))
  :hints (("Goal" :in-theory (disable angle angle-as-negated-ratio)
                  :use positive-imagpart-chain-for-triangle-angles)))

(defthm triangle-angles-angle-*-positive-orientation
    (implies (< 0 (imagpart (angle a b c)))
             (equal (angle-* (list 0 (angle a b c))
                             (angle-* (list 0 (angle b c a))
                                      (list 0 (angle c a b))))
                    '(0 -1)))
  :hints (("Goal" :in-theory (disable angle
                                      angle-as-negated-ratio
                                      imagpart-*
                                      turn-count-and-angle-fix
                                      detect-inbounds-angle*
                                      upper-half-plane-p
                                      nonzero-complexp
                                      commutativity-of-angle-*
                                      associativity-of-angle*)
                  :use (diffs-nonzero-when-imagpart-angle-nonzero
                        positive-imagpart-chain-for-triangle-angles
                        triangle-angles-product-when-nondegen))))

(defthm triangle-angles-angle-*-negative-orientation
    (implies (< (imagpart (angle a b c)) 0)
             (equal (angle-* (list 0 (angle a b c))
                             (angle-* (list 0 (angle b c a))
                                      (list 0 (angle c a b))))
                    '(2 -1)))
  :hints (("Goal" :in-theory (disable angle
                                      angle-as-negated-ratio
                                      imagpart-*
                                      turn-count-and-angle-fix
                                      detect-inbounds-angle*
                                      upper-half-plane-p
                                      nonzero-complexp
                                      commutativity-of-angle-*
                                      associativity-of-angle*)
                  :use (diffs-nonzero-when-imagpart-angle-nonzero
                        negative-imagpart-chain-for-triangle-angles
                        triangle-angles-product-when-nondegen))))

(defthm triangle-angles-angle-*-non-collinear
    (implies (not (collinear-p a b c))
             (or (and (equal (angle-* (list 0 (angle a b c))
                                      (angle-* (list 0 (angle b c a))
                                               (list 0 (angle c a b))))
                             '(0 -1))
                      (equal (angle-* (list 0 (angle c b a))
                                      (angle-* (list 0 (angle b a c))
                                               (list 0 (angle a c b))))
                             '(2 -1)))
                 (and (equal (angle-* (list 0 (angle a b c))
                                      (angle-* (list 0 (angle b c a))
                                               (list 0 (angle c a b))))
                             '(2 -1))
                      (equal (angle-* (list 0 (angle c b a))
                                      (angle-* (list 0 (angle b a c))
                                               (list 0 (angle a c b))))
                             '(0 -1)))))
  :hints (("Goal" :in-theory (disable angle
                                      angle-as-negated-ratio
                                      angle-*
                                      collinear-p
                                      commutativity-of-angle-*
                                      associativity-of-angle*)
                  :use (collinear-p-as-imagpart-0
                        imagpart-angle-reversed-sign
                        triangle-angles-angle-*-positive-orientation
                        triangle-angles-angle-*-negative-orientation
                        (:instance triangle-angles-angle-*-positive-orientation
                                   (a c) (b b) (c a))
                        (:instance triangle-angles-angle-*-negative-orientation
                                   (a c) (b b) (c a))))))
