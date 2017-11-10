; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;; ===================================
;; Arithmetic

;; Cuong Chau: Added for compatibility with old NSA books.
(defmacro standard-numberp (x)
  `(and (acl2-numberp ,x)
        (standardp ,x)))

(defun coeff-term-order (x y)
  (declare (xargs :mode :program))
  (cond ((and
          (eq (fn-symb x)
              'binary-*)
          (quotep (fargn x 1))
          (eq (fn-symb y)
              'binary-*)
          (quotep (fargn y 1)))
         (term-order (fargn x 2)
                     (fargn y 2)))
        ((and
          (eq (fn-symb x)
              'binary-*)
          (quotep (fargn x 1)))
         (if (equal (fargn x 2) y)
             nil
           (term-order (fargn x 2)
                       y)))
        ((and
          (eq (fn-symb y)
              'binary-*)
          (quotep (fargn y 1)))
         (if (equal x (fargn y 2))
             t
           (term-order x
                       (fargn y 2))))
        (t (term-order x y))))

(defthm +-commut-coeff-2way
  (implies
   (syntaxp (not (coeff-term-order y x)))
   (equal (+ y x) (+ x y)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm +-commut-coeff-3way
  (implies
   (syntaxp (not (coeff-term-order y x)))
   (equal (+ y x z) (+ x y z)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm *-commut-3way
  (equal (* y x z) (* x y z))
  :hints (("Goal" :use ((:instance commutativity-of-* (x y) (y (* x z)))))))

;; Disable the usual commuativity of +. If not disabled, looping may occur.

(in-theory (disable commutativity-of-+))

(defthm *-zero
  (equal (* 0 x) 0))

(defthm +-zero
  (equal (+ 0 x) (fix x)))

(defthm uminus-is-*-neg-1
  (equal (- x) (* -1 x)))

(defthm fold-consts-in-+
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (+ x (+ y z))
                  (+ (+ x y) z))))

(defthm fold-consts-in-*
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (* x (* y z))
                  (* (* x y) z))))

(defthm combine-terms-+-3way
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b)))
           (equal (+ (* a x) (+ (* b x) y))
                  (+ (* (+ a b) x) y))))

(defthm combine-terms-+-2way
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b)))
           (equal (+ (* a x) (* b x))
                  (* (+ a b) x))))

(defthm combine-terms-+-3way-unary
  (implies (syntaxp (quotep a))
           (equal (+ x (+ (* a x) y))
                  (+ (* (+ a 1) x) y))))

(defthm combine-terms-+-2way-unary
  (implies (syntaxp (quotep a))
           (equal (+ x (* a x))
                  (* (+ a 1) x))))

(defthm /-cancellation
  (implies (and (acl2-numberp x)
                (not (equal 0 x)))
           (equal (* x (/ x) y)
                  (fix y)))
  :hints (("Goal" :use ((:instance commutativity-of-*
                                   (x y)
                                   (y (* x (/ x))))))))

(defthm <-*-right-cancel
  (implies (and (realp x)
                (realp y)
                (realp z))
           (iff (< (* x z) (* y z))
                (cond
                 ((< 0 z)
                  (< x y))
                 ((equal z 0)
                  nil)
                 (t (< y x)))))
  :hints (("Goal" :use
           ((:instance (:theorem
                        (implies (and (realp a)
                                      (< 0 a)
                                      (realp b)
                                      (< 0 b))
                                 (< 0 (* a b))))
                       (a (abs (- y x)))
                       (b (abs z)))))))

(defthm <-*-left-cancel
  (implies (and (realp x)
                (realp y)
                (realp z))
           (iff (< (* z x) (* z y))
                (cond
                 ((< 0 z)
                  (< x y))
                 ((equal z 0)
                  nil)
                 (t (< y x))))))

(defthm distrib-/-over-*
  (equal (/ (* x y)) (* (/ x) (/ y)))
  :hints (("Goal" :use ((:instance (:theorem
                                    (implies
                                     (and
                                      (acl2-numberp y)
                                      (acl2-numberp z)
                                      (not (equal y 0))
                                      (not (equal z 0)))
                                     (equal (fix x) (* (/ y) (/ z) y z x))))
                                   (x (/ (* x y))) (y x) (z y))
                        (:instance inverse-of-* (x (* x y)))))
          ("Subgoal 2"
           :use (:instance (:theorem
                            (implies
                             (equal (* x y) 0)
                             (or (equal (fix x) 0)
                                 (equal (fix y) 0))))))))

;; Generate a list of terms each of which appears as the divisor in
;; a unary-/ term in the given TERM which is assumed to be a product
;; of terms, or itself a unary-/ form.

(defun FIND-Divisors-in-times (TERM)
  (cond
   ((eq (fn-symb term) 'binary-*)
    (append (find-divisors-in-times (fargn term 1))
            (find-divisors-in-times (fargn term 2))))
   ((eq (fn-symb term) 'unary-/)
    (list (fargn term 1)))
   (t nil)))

;; Generate a list of terms each of which appears as the divisor
;; in a unary-/ term in the given TERM which is assumed to be a
;; polynomial in sum of products form.

(DEFUN FIND-DIVISORS-IN-POLY (TERM)
  (IF (EQ (FN-SYMB TERM) 'BINARY-+)
      (append (find-divisors-in-times (FARGN TERM 1))
              (find-divisors-in-poly (FARGN TERM 2)))
      (find-divisors-in-times TERM)))

;; Find a binding to a term which appears as the divisor in a unary-/ term
;; in the given LHS or RHS polynomials.
;; Polynomials are assumed to be in sum of products form.
;; If no such term exists, return nil, if more than one exists,
;; pick the first and bind that term to x.

(DEFUN FIND-DIVISORS-BIND-TERM (LHS RHS)
  (LET ((DIVISOR-LST (APPEND (find-divisors-in-poly LHS)
                             (find-divisors-in-poly RHS))))
       (IF DIVISOR-LST
           (LIST (CONS 'X (CAR DIVISOR-LST)))
           NIL)))

;; If a term appears as a divisor in the LHS or RHS of an equality,
;; where LHS and RHS are assumed to be polynomials,
;; then rewrite the equality where both sides are multiplied by
;; the divisor term, resulting in cancellation of the divisor term

(defthm equal-cancel-divisors
  (implies
   (and
    (acl2-numberp LHS)
    (acl2-numberp RHS)
    (BIND-FREE (FIND-divisors-bind-term LHS RHS) (X))
    (acl2-numberp x)
    (not (equal x 0)))
   (equal (equal LHS RHS) (equal (* x LHS) (* x RHS))))
  :hints (("Goal" :use ((:instance (:theorem
                                    (implies
                                     (equal a b)
                                     (equal (* x a) (* x b))))
                                   (x (/ x)) (a (* x LHS)) (b (* x RHS)))))))

;; If a term appears as a divisor in the LHS or RHS of an inequality,
;; where LHS and RHS are assumed to be polynomials,
;; then rewrite the inequality where both sides are multiplied by
;; the divisor (with the inequality operand adjusted according
;; to the sign of the divisor term), resulting in cancellation
;; of the divisor term.

(defthm <-cancel-divisors
  (implies
   (and
    (realp LHS)
    (realp RHS)
    (BIND-FREE (FIND-divisors-bind-term LHS RHS) (X))
    (realp x)
    (not (equal x 0)))
   (iff (< LHS RHS) (if (< 0 x)
                        (< (* x LHS) (* x RHS))
                      (> (* x LHS) (* x RHS))))))

(defthm /-self-inversion
  (equal (/ (/ x)) (fix x))
  :hints (("Goal" :cases ((not (equal x 0))))))

(defthm distributivity-left
  (equal (* (+ x y) z)
         (+ (* x z) (* y z))))

(defthm pos-*-thm
  (implies
   (and
    (realp x)
    (realp y)
    (< 0 x)
    (< 0 y))
   (< 0 (* x y)))
  :rule-classes nil)

(defthm pos-factor-<=-thm
  (implies
   (and
    (realp x)
    (realp y)
    (realp a)
    (<= x y)
    (<= 0 a))
   (<= (* a x) (* a y)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pos-*-thm (x (- y x)) (y a))))))

(defthm pos-factor-<-thm
  (implies
   (and
    (realp x)
    (realp y)
    (realp a)
    (< x y)
    (< 0 a))
   (< (* a x) (* a y)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pos-*-thm (x (- y x)) (y a))))))

;; End arithmatic
;; =================================================

;; ==================================
;; Floor1

(defthm floor1-<
  (implies
   (and
    (realp x)
    (realp y)
    (<= (+ x 1) y))
   (< (floor1 x) (floor1 y))))

(defthm floor1-limits
  (implies
   (and
    (realp x))
   (and
    (<= 0 (- x (floor1 x)))
    (< (- x (floor1 x)) 1)))
  :rule-classes nil)

(defthm floor1-+-integer
  (implies
   (and
    (integerp i)
    (realp x))
   (equal (floor1 (+ i x)) (+ i (floor1 x)))))

(defthm floor1-pos
  (implies
   (and
    (realp x)
    (< 0 x))
   (<= 0 (floor1 x))))

(defthm floor1-neg
  (implies
   (and
    (realp x)
    (< x 0))
   (<= (floor1 x) 0)))

(defthm floor1-*-const
  (implies
   (and
    (realp x)
    (realp k)
    (syntaxp (quotep k)))
   (equal (< 0 (* k (floor1 x))) (cond
                                  ((< 0 k) (< 0 (floor1 x)))
                                  ((= 0 k) nil)
                                  ((< k 0) (< (floor1 x) 0)))))
  :hints (("Goal" :use ((:instance <-*-left-cancel
                                   (z k)
                                   (x 0)
                                   (y (floor1 x)))))))

;; End floor1
;; ==================================

;; =================================================
;; Non-standard analysis

(defthm standard-part-*-1
  (equal (standard-part (* -1 x))
         (* -1 (standard-part x)))
  :hints (("Goal" :use ((:instance standard-part-of-uminus)))))

(defthm standard-part-abs
  (implies
   (realp x)
   (equal (standard-part (abs x)) (abs (standard-part x)))))

;; End non-standard analysis
;; =================================================
