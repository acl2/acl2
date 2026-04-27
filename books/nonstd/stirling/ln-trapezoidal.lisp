(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/derivatives-composition" :dir :system))
(local (include-book "nonstd/nsa/derivative-raise" :dir :system))
(local (include-book "nonstd/nsa/continuity-product" :dir :system))
(local (include-book "nonstd/integrals/continuous-function" :dir :system))

(include-book "ln-integral")
(local (include-book "ln-factorial"))
(local (include-book "standard-close-utils"))
(local (include-book "basel-bound"))

(local (in-theory (disable binomial-theorem)))
(local (in-theory (disable binomial-theorem)))

(local
 (defthmd int-ln-integer-interval
     (implies (and (integerp i)
                   (<= 1 i))
              (equal (int-ln i (1+ i))
                     (+ (* (1+ i) (acl2-ln (1+ i)))
                        (- (* i (acl2-ln i)))
                        -1)))
   :hints (("Goal"
            :use ((:instance int-ln-computation
                             (a i)
                             (b (1+ i))))
            :in-theory (enable inside-interval-p)))))

(local
 (defun trapezoidal-ln-term (i)
   (let ((i (realposfix i)))
     (/ (+ (acl2-ln i)
           (acl2-ln (1+ i)))
        2))))

(local
 (defthmd trapezoidal-ln-term-completion
     (implies (or (not (realp i))
                  (< i 0))
              (equal (trapezoidal-ln-term i)
                     (/ (+ (acl2-ln 1) (acl2-ln 2)) 2)))))

(defun trapezoidal-error-integrand (i x)
  (let ((i (realfix i))
        (x (realposfix x)))
    (- (/ (expt (- x (+ i 1/2)) 2) 2) 1/8)))

(local
 (defthmd trapezoidal-error-integrand-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (trapezoidal-error-integrand i x)
                     (if (realp i)
                         (- (/ (expt (+ 1/2 (- i)) 2) 2) 1/8)
                         (if (and (realp x) (< 0 x))
                             (- (/ (expt (- x 1/2) 2) 2) 1/8)
                             0))))))
(local
 (defun trapezoidal-error-integrand-as-product (i x)
  (let ((i (realfix i))
        (x (realposfix x)))
    (* 1/2 (- x i) (- x (1+ i))))))

(local
 (defthmd trapezoidal-error-integrand-alternative-works
     (equal (trapezoidal-error-integrand i x)
            (trapezoidal-error-integrand-as-product i x)))
   )

(local
 (defthmd trapezoidal-error-integrand-is-negative-lemma
     (implies (and (realp x)
                   (realp i)
                   (<= 0 I)
                   (<= i x)
                   (<= x (1+ i)))
              (<= (trapezoidal-error-integrand-as-product i x) 0))
   :hints (("Goal"
            :use ((:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (<= 0 x) (<= y 0))
                                      (<= (* x y) 0)))
                   (x (- x i))
                   (y (- x (1+ i))))
                  )
            )
           )
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthmd trapezoidal-error-integrand-is-negative
     (implies (and (realp x)
                   (realp i)
                   (<= 0 I)
                   (<= i x)
                   (<= x (1+ i)))
              (<= (trapezoidal-error-integrand i x) 0))
   :hints (("Goal"
            :use ((:instance trapezoidal-error-integrand-alternative-works)
                  (:instance trapezoidal-error-integrand-is-negative-lemma))
            :in-theory (disable trapezoidal-error-integrand
                                trapezoidal-error-integrand-as-product)))))

(defun trapezoidal-error-integrand-antiderivative (i x)
  (LET ((I (REALFIX I))
        (X (REALPOSFIX X)))
    (- (/ (expt (- x (+ i 1/2)) 3) 6) (/ x 8))))

(local
 (defthmd trapezoidal-error-integrand-antiderivative-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (trapezoidal-error-integrand-antiderivative i x)
                     (if (realp i)
                         (- (/ (expt (+ (- i) 1/2) 3) 6) 1/8)
                         (if (and (realp x) (< 0 x))
                             (- (/ (expt (- x 1/2) 3) 6) (/ x 8))
                             -5/48))))))

(defun trapezoidal-error-integrand-antiderivative-differential (i x eps)
  (LET ((I (REALFIX I))
        (X (REALPOSFIX X))
        (EPS (REALFIX EPS)))
    (/ (- (trapezoidal-error-integrand-antiderivative i (+ x eps))
          (trapezoidal-error-integrand-antiderivative i x))
       eps)))

(local
 (defthmd trapezoidal-error-integrand-antiderivativ-differential-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x)))
                  (not (realp eps)))
              (equal (trapezoidal-error-integrand-antiderivative-differential i x eps)
                     (cond ((realp i)
                            (if (realp eps)
                                (trapezoidal-error-integrand-antiderivative-differential i 1 eps)
                                0))
                           ((realp eps)
                            (if (and (realp x) (< 0 x))
                                (trapezoidal-error-integrand-antiderivative-differential 0 x eps)
                                (trapezoidal-error-integrand-antiderivative-differential 0 1 eps)))
                           (t 0))))))


;;; Begin showing that trapezoidal-error-integrand-antiderivative really is
;;; the antiderivative of trapezoidal-error-integrand

(local
 (defthm swap-differential-term
     (implies (and (acl2-numberp fx)
                   (acl2-numberp fx1)
                   (acl2-numberp x)
                   (acl2-numberp x1))
              (equal (/ (- fx fx1)
                        (- x x1))
                     (/ (- fx1 fx)
                        (- x1 x))))
   :instructions (:pro (:dv 1)
                       (:dv 1)
                       (:= (- (+ fx1 (- fx))))
                       :up (:rewrite |(* (- x) y)|)
                       (:dv 1)
                       (:dv 2)
                       (:dv 1)
                       (:= (- (- x1 x)))
                       :up (:rewrite |(/ (- x))|)
                       :up (:rewrite |(* x (- y))|)
                       :up (:rewrite |(- (- x))|)
                       :UP :S)))

(local
 (defthmd x/8-antiderative
     (implies (and (realp x)
                   (standardp x)
                   (realp x1)
                   (i-close x x1)
                   (not (= x x1)))
              (i-close (/ (- (- (/ x 8))
                             (- (/ x1 8)))
                          (- x x1))
                       -1/8))
   :INSTRUCTIONS
   (:PRO
    (:DV 1)
    :S
    (:= (* -1/8
           (- (* X (/ (+ X (- X1))))
              (* X1 (/ (+ X (- X1)))))))
    (:DV 2)
    (:= (+ (* X (/ (+ X (- X1))))
           (* (- X1) (/ (+ X (- X1))))))
    (:CLAIM (NOT (= (+ X (- X1)) 0)))
    :TOP
    (:USE (:INSTANCE (:THEOREM (IMPLIES (AND (REALP X) (REALP Y) (REALP Z))
                                        (EQUAL (+ (* X Z) (* Y Z))
                                               (* (+ X Y) Z))))
                     (X X)
                     (Y (- X1))
                     (Z (/ (- X X1)))))
    :PRO (:FORWARDCHAIN 1)
    (:DV 1)
    (:DV 2)
    := (:= 1)
    :UP
    :S :BASH)
   ))

(local
 (defun term-inside-expt (i x)
   (LET ((I (REALFIX I))
         (X (REALPOSFIX X)))
     (- x (+ i 1/2)))))

(local
 (defthm term-inside-expt-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-inside-expt i x)
                     (if (realp i)
                         (+ (- i) 1/2)
                         (if (and (realp x) (< 0 x))
                             (- x 1/2)
                             1/2))))))

(local
 (defthmd term-inside-expt-derivative
     (implies (and (realp x)
                   (< 0 X)
                   (standardp x)
                   (standardp i)
                   (realp i)
                   (realp x1)
                   (< 0 X1)
                   (i-close x x1)
                   (not (= x x1)))
              (i-close (/ (- (term-inside-expt i x)
                             (term-inside-expt i x1))
                          (- x x1))
                       1))
   ))

(local
 (defun term-inside-expt-squared (i x)
   (LET ((I (REALFIX I))
         (X (REALPOSFIX X)))
     (* (- x (+ i 1/2))
        (- x (+ i 1/2))))))

(local
 (defthm term-inside-expt-squared-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-inside-expt-squared i x)
                     (if (realp i)
                         (expt (+ (- i) 1/2) 2)
                         (if (and (realp x) (< 0 x))
                             (expt (- x 1/2) 2)
                             1/4))))))

(local
 (defun term-inside-expt-squared-differential (i x eps)
   (LET ((I (REALFIX I))
         (X (REALPOSFIX X))
         (EPS (REALFIX EPS)))
     (/ (- (term-inside-expt-squared i (+ x eps))
           (term-inside-expt-squared i x))
        eps))))

(local
 (defthmd term-inside-expt-squared-differential-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x)))
                  (not (realp eps)))
              (equal (term-inside-expt-squared-differential i x eps)
                     (cond ((realp i)
                            (if (realp eps)
                                (term-inside-expt-squared-differential i 1 eps)
                                0))
                           ((realp eps)
                            (if (and (realp x) (< 0 x))
                                (term-inside-expt-squared-differential 0 x eps)
                                (term-inside-expt-squared-differential 0 1 eps)))
                           (t 0))))))


(local
 (defun term-inside-expt-squared-derivative (i x)
   (LET ((I (REALFIX I))
         (X (REALPOSFIX X)))
     (* 2 (- x (+ i 1/2))))))

(local
 (defthm term-inside-expt-squared-derivative-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-inside-expt-squared-derivative i x)
                     (if (realp i)
                         (+ (* -2 i) 1)
                         (if (and (realp x) (< 0 x))
                             (- (* 2 x) 1)
                             1))))))

(local
 (defthmd term-inside-expt-squared-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (term-inside-expt-squared-differential i x eps))
                     (term-inside-expt-squared-derivative i x)))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1*fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                    ;;;
                    (dc-fn1 (lambda (i x) (term-inside-expt i x)))
                    (differential-dc-fn1 (lambda (i x eps) (/ eps eps)))
                    (derivative-dc-fn1 (lambda (i x) 1))
                    ;;;
                    (dc-fn2 (lambda (i x) (term-inside-expt i x)))
                    (differential-dc-fn2 (lambda (i x eps) (/ eps eps)))
                    (derivative-dc-fn2 (lambda (i x) 1))
                    ;;;
                    (dc-fn1*fn2 term-inside-expt-squared)
                    (differential-dc-fn1*fn2
                     (lambda (i x eps)
                       (term-inside-expt-squared-differential i x eps)))
                    (derivative-dc-fn1*fn2
                     (lambda (i x)
                       (term-inside-expt-squared-derivative i x)))
                    ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (enable inside-interval-p)
            )
           )))

(local
 (defthm small-close-swapped
     (implies (and (realp x)
                   (realp y)
                   (i-close x y))
              (i-small (+ (- x) y)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))
   ))

(local
 (defthmd term-inside-expt-squared-differential-standard-part-is-derivative
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1))
                   )
              (equal (standard-part (/ (- (term-inside-expt-squared i x)
                                          (term-inside-expt-squared i x1))
                                       (- x x1)))
                     (term-inside-expt-squared-derivative i x)))
   :hints (("Goal"
            :use ((:instance term-inside-expt-squared-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (TERM-INSIDE-EXPT-SQUARED I X))
                             (fx1 (TERM-INSIDE-EXPT-SQUARED I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (disable STANDARD-PART-OF-PLUS
                                PREFER-POSITIVE-ADDENDS-EQUAL
                                |(equal (+ (- c) x) y)|
                                ;term-inside-expt-squared
                                term-inside-expt-squared-derivative)
            ))))


(local
 (defun term-inside-expt-cubed (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (* (- x (+ i 1/2))
        (- x (+ i 1/2))
        (- x (+ i 1/2))))))

(local
 (defthm term-inside-expt-cubed-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-inside-expt-cubed i x)
                     (if (realp i)
                         (expt (+ (- i) 1/2) 3)
                         (if (and (realp x) (< 0 x))
                             (expt (+ x -1/2) 3)
                             1/8))))))


(local
 (defun term-inside-expt-cubed-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (term-inside-expt-cubed i (+ x eps))
           (term-inside-expt-cubed i x))
        eps))))


(local
 (defthmd term-inside-expt-cubed-differential-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x)))
                  (not (realp eps)))
              (equal (term-inside-expt-cubed-differential i x eps)
                     (cond ((realp i)
                            (if (realp eps)
                                (term-inside-expt-cubed-differential i 1 eps)
                                0))
                           ((realp eps)
                            (if (and (realp x) (< 0 x))
                                (term-inside-expt-cubed-differential 0 x eps)
                                (term-inside-expt-cubed-differential 0 1 eps)))
                           (t 0))))))

(local
 (defun term-inside-expt-cubed-derivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (* 3 (- x (+ i 1/2)) (- x (+ i 1/2))))))

(local
 (defthm term-inside-expt-cubed-derivative-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-inside-expt-cubed-derivative i x)
                     (if (realp i)
                         (* 3 (expt (+ (- i) 1/2) 2))
                         (if (and (realp x) (< 0 x))
                             (* 3 (expt (+ x -1/2) 2))
                             3/4))))))

(local
 (defthmd standard-part-of-small
     (implies (i-small x)
              (equal (standard-part x) 0))
   :hints (("Goal"
            :use ((:instance close-x-y->same-standard-part
                             (x 0)
                             (y x)))
            :in-theory (e/d (i-close)
                            (close-x-y->same-standard-part))))
   ))


(local
 (defthm standard-part-of-/-large-integer
     (equal (standard-part (/ (i-large-integer))) 0)
   :hints (("Goal"
            :use ((:instance standard-part-of-small
                             (x (/ (i-large-integer)))))))))

(local
 (defthm-std standardp-realfix
     (implies (standardp x)
              (standardp (realfix x)))))

(local
 (defthm-std standardp-realfix-open
     (implies (standardp x)
              (standardp (if (realp x) x 0)))))

(local
 (defthm-std standardp-term-inside-expt-squared
     (implies (and (standardp i)
                   (standardp x))
              (standardp (term-inside-expt-squared i x)))))

(local
 (defthm-std standardp-term-inside-expt-squared-derivative
     (implies (and (standardp i)
                   (standardp x))
              (standardp (TERM-INSIDE-EXPT-SQUARED-DERIVATIVE i x)))))


(local
 (defthmd close-to-derivative->close-differentials
     (implies (and (standardp fprime)
                   (acl2-numberp x)
                   (acl2-numberp x1)
                   (acl2-numberp x2)
                   (acl2-numberp fx1)
                   (acl2-numberp fx2)
                   (equal (standard-part (/ (- fx fx1) (- x x1))) fprime)
                   (equal (standard-part (/ (- fx fx2) (- x x2))) fprime))
              (and (i-limited (/ (- fx fx1) (- x x1)))
                   (i-close (/ (- fx fx1) (- x x1))
                            (/ (- fx fx2) (- x x2)))))
   :hints (("Goal"
            :use ((:instance standard-part-is-standard-implies-close-to-standard-part
                             (x (/ (- fx fx1) (- x x1)))
                             (stdx fprime))
                  (:instance standard-part-is-standard-implies-close-to-standard-part
                             (x (/ (- fx fx2) (- x x2)))
                             (stdx fprime))
                  (:instance close-to-standard-are-close
                             (x1 (/ (- fx fx1) (- x x1)))
                             (x2 (/ (- fx fx2) (- x x2)))
                             (stdx fprime))
                  (:instance limited-if-standard-part-close-to-standard
                             (x (/ (- fx fx1) (- x x1)))
                             (stdx fprime)))))))



(local
 (defthm standard-term-inside-expt-cubed-derivative
     (implies (and (standardp i)
                   (standardp x))
              (STANDARDP (TERM-INSIDE-EXPT-CUBED-DERIVATIVE I X)))))

(local
 (defthmd term-inside-expt-cubed-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (term-inside-expt-cubed-differential i x eps))
                     (term-inside-expt-cubed-derivative i x)))
   :otf-flg nil
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1*fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                    ;;;
                    (dc-fn1 (lambda (i x) (term-inside-expt-squared i x)))
                    (differential-dc-fn1
                     (lambda (i x eps)
                       (term-inside-expt-squared-differential i x eps)))
                    (derivative-dc-fn1
                     (lambda (i x)
                       (term-inside-expt-squared-derivative i x)))
                    ;;;
                    (dc-fn2 (lambda (i x) (term-inside-expt i x)))
                    (differential-dc-fn2 (lambda (i x eps) (/ eps eps)))
                    (derivative-dc-fn2 (lambda (i x) 1))
                    ;;;
                    (dc-fn1*fn2 term-inside-expt-cubed)
                    (differential-dc-fn1*fn2
                     (lambda (i x eps)
                       (term-inside-expt-cubed-differential i x eps)))
                    (derivative-dc-fn1*fn2
                     (lambda (i x)
                       (term-inside-expt-cubed-derivative i x)))
                    ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (e/d (inside-interval-p)
                            (term-inside-expt-cubed
                             term-inside-expt-cubed-derivative
                             term-inside-expt-squared
                             term-inside-expt-squared-derivative))
            )
           ("Subgoal 6"
            :use ((:instance
                   term-inside-expt-squared-differential-standard-part-is-derivative-eps
                   (i context1)
                   (eps (/ (i-large-integer))))))
           ("Subgoal 5"
            :in-theory (enable TERM-INSIDE-EXPT-SQUARED))
           ("Subgoal 3"
            :use ((:instance
                   term-inside-expt-squared-differential-standard-part-is-derivative
                   (i context1)
                   (x1 y1))
                  (:instance
                   term-inside-expt-squared-differential-standard-part-is-derivative
                   (i context1)
                   (x1 y2))
                  (:instance close-to-derivative->close-differentials
                             (fx (term-inside-expt-squared context1 x))
                             (fx1 (term-inside-expt-squared context1 y1))
                             (fx2 (term-inside-expt-squared context1 y2))
                             (x1 y1)
                             (x2 y2)
                             (fprime (term-inside-expt-squared-derivative context1 x))
                             ))
            :in-theory (e/d (inside-interval-p
                             i-close)
                            (term-inside-expt-cubed-differential
                             term-inside-expt-cubed-derivative
                             term-inside-expt-squared
                             TERM-INSIDE-EXPT-SQUARED-DERIVATIVE
                             TERM-INSIDE-EXPT-SQUARED-DIFFERENTIAL
                             standard-part-is-standard-implies-close-to-standard-part
                             i-small-uminus
                             standard-part-of-plus
                             standard-part-of-uminus
                             )))
           ("Subgoal 2"
            :in-theory (enable TERM-INSIDE-EXPT-SQUARED
                               TERM-INSIDE-EXPT-SQUARED-derivative
                               ))
           ("Subgoal 1"
            :in-theory (enable TERM-INSIDE-EXPT-cubed
                               TERM-INSIDE-EXPT-squared
                               ))
           )))

(local
 (defthmd term-inside-expt-cubed-differential-standard-part-is-derivative
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1))
                   )
              (equal (standard-part (/ (- (term-inside-expt-cubed i x)
                                          (term-inside-expt-cubed i x1))
                                       (- x x1)))
                     (term-inside-expt-cubed-derivative i x)))
   :hints (("Goal"
            :use ((:instance term-inside-expt-cubed-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (TERM-INSIDE-EXPT-cubed I X))
                             (fx1 (TERM-INSIDE-EXPT-cubed I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (disable STANDARD-PART-OF-PLUS
                                PREFER-POSITIVE-ADDENDS-EQUAL
                                |(equal (+ (- c) x) y)|
                                ;term-inside-expt-squared
                                term-inside-expt-cubed-derivative)
            ))))


(local
 (defun term-expt-cubed-/-6 (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (* 1/6 (term-inside-expt-cubed i x)))))

(local
 (defthm term-expt-cubed-/-6-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-expt-cubed-/-6 i x)
                     (if (realp i)
                         (* 1/6 (expt (+ (- i) 1/2) 3))
                         (if (and (realp x) (< 0 x))
                             (* 1/6 (expt (- x 1/2) 3))
                             1/48))))))

(local
 (defun term-expt-cubed-/-6-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (* 1/6 (term-inside-expt-cubed-differential i x eps)))))

(local
 (defthmd term-inside-expt-cubed-/-6-differential-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x)))
                  (not (realp eps)))
              (equal (term-expt-cubed-/-6-differential i x eps)
                     (cond ((realp i)
                            (if (realp eps)
                                (term-expt-cubed-/-6-differential i 1 eps)
                                0))
                           ((realp eps)
                            (if (and (realp x) (< 0 x))
                                (term-expt-cubed-/-6-differential 0 x eps)
                                (term-expt-cubed-/-6-differential 0 1 eps)))
                           (t 0))))))


(local
 (defun term-expt-cubed-/-6-derivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (* 1/6 (term-inside-expt-cubed-derivative i x)))))

(local
 (defthm term-expt-cubed-/-6-derivative-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (term-expt-cubed-/-6-derivative i x)
                     (if (realp i)
                         (* 1/2 (EXPT (+ (- I) 1/2) 2))
                         (if (and (realp x) (< 0 x))
                             (* 1/2 (EXPT (+ X -1/2) 2))
                             1/8))))))

(local
 (defthm-std standardp-term-inside-expt-cubed
     (implies (and (standardp i)
                   (standardp x))
              (standardp (term-inside-expt-cubed i x)))))


(local
 (defthm-std standardp-term-inside-expt-cubed-derivative
     (implies (and (standardp i)
                   (standardp x))
              (standardp (TERM-INSIDE-EXPT-cubed-DERIVATIVE i x)))))

(local
 (defthmd term-expt-cubed-/-6-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (term-expt-cubed-/-6-differential i x eps))
                     (term-expt-cubed-/-6-derivative i x)))
   :otf-flg nil
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1*fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                    ;;;
                    (dc-fn1 (lambda (i x) (term-inside-expt-cubed i x)))
                    (differential-dc-fn1
                     (lambda (i x eps)
                       (term-inside-expt-cubed-differential i x eps)))
                    (derivative-dc-fn1
                     (lambda (i x)
                       (term-inside-expt-cubed-derivative i x)))
                    ;;;
                    (dc-fn2 (lambda (i x) 1/6))
                    (differential-dc-fn2 (lambda (i x eps) 0))
                    (derivative-dc-fn2 (lambda (i x) 0))
                    ;;;
                    (dc-fn1*fn2 term-expt-cubed-/-6)
                    (differential-dc-fn1*fn2
                     (lambda (i x eps)
                       (term-expt-cubed-/-6-differential i x eps)))
                    (derivative-dc-fn1*fn2
                     (lambda (i x)
                       (term-expt-cubed-/-6-derivative i x)))
                    ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (e/d (inside-interval-p)
                            (term-expt-cubed-/-6
                             term-expt-cubed-/-6-derivative
                             term-inside-expt-cubed
                             term-inside-expt-cubed-derivative))
            )
           ("Subgoal 6000"
            :in-theory (enable standard-part-of-small
                               inside-interval-p))
           ("Subgoal 6"
            :use ((:instance
                   term-inside-expt-cubed-differential-standard-part-is-derivative-eps
                   (i context1)
                   (eps (/ (i-large-integer))))
                  )
            )
           ("Subgoal 5"
            :in-theory (e/d (inside-interval-p)
                            (PREFER-POSITIVE-ADDENDS-EQUAL
                             term-expt-cubed-/-6
                             term-expt-cubed-/-6-derivative
                             ;term-inside-expt-cubed
                             term-inside-expt-cubed-derivative)))
           ("Subgoal 4"
            :use ((:instance
                   term-inside-expt-cubed-differential-standard-part-is-derivative
                   (i context1)
                   (x1 y1))
                  (:instance
                   term-inside-expt-cubed-differential-standard-part-is-derivative
                   (i context1)
                   (x1 y2))
                  (:instance close-to-derivative->close-differentials
                             (fx (term-inside-expt-cubed context1 x))
                             (fx1 (term-inside-expt-cubed context1 y1))
                             (fx2 (term-inside-expt-cubed context1 y2))
                             (x1 y1)
                             (x2 y2)
                             (fprime (term-inside-expt-cubed-derivative context1 x))
                             )
                  )
            )
           ("Subgoal 2"
            :in-theory (enable TERM-EXPT-CUBED-/-6-DERIVATIVE))
           )
           ))

(local
 (defthmd term-expt-cubed-/-6-differential-standard-part-is-derivative
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1))
                   )
              (equal (standard-part (/ (- (term-expt-cubed-/-6 i x)
                                          (term-expt-cubed-/-6 i x1))
                                       (- x x1)))
                     (term-expt-cubed-/-6-derivative i x)))
   :hints (("Goal"
            :use ((:instance term-expt-cubed-/-6-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (TERM-EXPT-cubed-/-6 I X))
                             (fx1 (TERM-EXPT-cubed-/-6 I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (disable STANDARD-PART-OF-PLUS
                                PREFER-POSITIVE-ADDENDS-EQUAL
                                |(equal (+ (- c) x) y)|
                                term-expt-cubed-/-6-derivative)
            ))))

(local
 (defun trapezoidal-error-integrand-antiderivative-differential-local (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (- (term-expt-cubed-/-6-differential i x eps)
        (* 1/8 eps (/ eps))))))

(local
 (defthmd trapezoidal-error-integrand-antiderivativ-differential-local-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x)))
                  (not (realp eps)))
              (equal (trapezoidal-error-integrand-antiderivative-differential-local i x eps)
                     (cond ((realp i)
                            (if (realp eps)
                                (trapezoidal-error-integrand-antiderivative-differential-local i 1 eps)
                                0))
                           ((realp eps)
                            (if (and (realp x) (< 0 x))
                                (trapezoidal-error-integrand-antiderivative-differential-local 0 x eps)
                                (trapezoidal-error-integrand-antiderivative-differential-local 0 1 eps)))
                           (t 0))))))


(local
 (defthm-std standardp-term-expt-/-6-cubed
     (implies (and (standardp i)
                   (standardp x))
              (standardp (term-expt-cubed-/-6 i x)))))

(local
 (defthm-std standardp-term-expt-cubed-/-6-derivative
     (implies (and (standardp i)
                   (standardp x))
              (standardp (term-expt-cubed-/-6-derivative i x)))))

(local
 (defthmd open-trapezoidal-error-integrand
     (equal (trapezoidal-error-integrand i x)
            (- (TERM-EXPT-CUBED-/-6-derivative i x) 1/8))))

(local
 (defthmd trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-eps-lemma
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (trapezoidal-error-integrand-antiderivative-differential-local i x eps))
                     (trapezoidal-error-integrand i x)))
   :otf-flg nil
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1+fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                    ;;;
                    (dc-fn1 (lambda (i x) (term-expt-cubed-/-6 i x)))
                    (differential-dc-fn1
                     (lambda (i x eps)
                       (term-expt-cubed-/-6-differential i x eps)))
                    (derivative-dc-fn1
                     (lambda (i x)
                       (term-expt-cubed-/-6-derivative i x)))
                    ;;;
                    (dc-fn2 (lambda (i x) (- (/ (realposfix x) 8))))
                    (differential-dc-fn2 (lambda (i x eps) (- (/ (realfix eps) (* 8 (realfix eps))))))
                    (derivative-dc-fn2 (lambda (i x) -1/8))
                    ;;;
                    (dc-fn1+fn2 trapezoidal-error-integrand-ANTIDERIVATIVE)
                    (differential-dc-fn1+fn2
                     (lambda (i x eps)
                       (trapezoidal-error-integrand-antiderivative-differential-local i x eps)))
                    (derivative-dc-fn1+fn2
                     (lambda (i x)
                       (trapezoidal-error-integrand i x)))
                    ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (e/d (inside-interval-p)
                            (TRAPEZOIDAL-ERROR-INTEGRAND
                             TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE-DIFFERENTIAL-local
                             TERM-EXPT-CUBED-/-6
                             TERM-EXPT-CUBED-/-6-derivative
                             ;;TERM-EXPT-CUBED-/-6-differential
                             TERM-INSIDE-EXPT-CUBED
                             TERM-INSIDE-EXPT-CUBED-derivative
                             ;;TERM-INSIDE-EXPT-CUBED-differential
                             ))

            )
           ("Subgoal 6"
            :use ((:instance x/8-antiderative (x x) (x1 y1))
                  (:instance x/8-antiderative (x x) (x1 y2))
                  (:instance close-to-standard-are-close
                             (x1  (* (+ (- (* X 1/8)) (- (- (* Y1 1/8))))
                                     (/ (+ X (- Y1)))))
                             (x2  (* (+ (- (* X 1/8)) (- (- (* Y2 1/8))))
                                     (/ (+ X (- Y2)))))
                             (stdx -1/8))
                  (:instance i-close-limited
                             (y  (* (+ (- (* X 1/8)) (- (- (* Y1 1/8))))
                                    (/ (+ X (- Y1)))))
                             (x -1/8))
                  )
            :in-theory (e/d (inside-interval-p
                             standard-part-of-plus)
                            (term-expt-cubed-/-6
                             TERM-EXPT-CUBED-/-6-DERIVATIVE
                             TERM-EXPT-CUBED-/-6-DIFFERENTIAL)))
           ("Subgoal 5"
            :use ((:instance
                    term-expt-cubed-/-6-differential-standard-part-is-derivative
                   (i context1)
                   (x1 y1)
                   )
                  (:instance
                   term-expt-cubed-/-6-differential-standard-part-is-derivative
                   (i context1)
                   (x1 y2)
                  )
                  (:instance close-to-derivative->close-differentials
                             (fx (term-expt-cubed-/-6 context1 x))
                             (fx1 (term-expt-cubed-/-6 context1 y1))
                             (fx2 (term-expt-cubed-/-6 context1 y2))
                             (x1 y1)
                             (x2 y2)
                             (fprime (term-expt-cubed-/-6-derivative context1 x))
                             )
                  )
            :in-theory (e/d (inside-interval-p
                             ;;i-closex
                             )
                            (term-inside-expt-cubed-differential
                             term-inside-expt-cubed-derivative
                             term-inside-expt-cubed
                             term-expt-cubed-/-6
                             term-expt-cubed-/-6-differential
                             term-expt-cubed-/-6-derivative
                             standard-part-is-standard-implies-close-to-standard-part
                             i-small-uminus
                             standard-part-of-plus
                             standard-part-of-uminus
                             )))
           ("Subgoal 4"
            :use ((:instance
                   term-expt-cubed-/-6-differential-standard-part-is-derivative-eps
                   (i context1)
                   (eps (/ (i-large-integer)))))
            :in-theory (e/d (inside-interval-p)
                            (TERM-INSIDE-EXPT-CUBED
                             ))
            )
           ("Subgoal 3"
            :in-theory (e/d (inside-interval-p)
                            (TERM-INSIDE-EXPT-CUBED
                             ))
            )
           ("Subgoal 2"
            :in-theory (e/d (inside-interval-p)
                            ())
            )
           ("Subgoal 1"
            :in-theory (e/d (inside-interval-p)
                            ())
            )
           )))

(local
 (defthmd trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-lemma
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1))
                   )
              (equal (standard-part (- (* 1/6
                                          (- (term-inside-expt-cubed i x)
                                             (term-inside-expt-cubed i x1))
                                          (/ (- x x1)))
                                       1/8))
                     (trapezoidal-error-integrand i x)))
   :instructions
   ((:use (:instance i-small-uminus (x (- x1 x))))
    (:use
     (:instance
      trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-eps-lemma
      (eps (- x1 x))))
    :pro
    (:in-theory (e/d (i-close)
                     (trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-eps-lemma
                      i-small-uminus
                      trapezoidal-error-integrand
                      term-inside-expt-cubed)))
    (:forwardchain 1)
    (:contrapose 10)
    (:dv 1)
    (:dv 1)
    (:dv 1)
    :x (:dv 2)
    (:dv 2)
    (:= (* (+ (term-inside-expt-cubed (realfix i) x1)
              (- (term-inside-expt-cubed (realfix i) x)))
           (/ (+ (- x) x1))))
    (:dv 1)
    (:= (- (+ (term-inside-expt-cubed (realfix i) x)
              (- (term-inside-expt-cubed (realfix i)
                                         x1)))))
    :up (:rewrite |(* (- x) y)|)
    (:dv 1)
    (:dv 2)
    (:dv 1)
    (:= (- (+ x (- x1))))
    :up (:rewrite |(/ (- x))|)
    :up (:rewrite |(* x (- y))|)
    :up (:rewrite |(- (- x))|)
    :up :top (:casesplit (realp i))
    (:contrapose 10)
    (:= t)
    (:contrapose 10)
    (:dv 1)
    (:dv 1)
    (:dv 2)
    (:dv 2)
    (:dv 1)
    (:rewrite term-inside-expt-cubed-completion)
    :s :nx (:dv 1)
    (:rewrite term-inside-expt-cubed-completion)
    :s :top :bash (:contrapose 10)
    (:dv 1)
    (:dv 1)
    (:dv 1)
    (:dv 1)
    (:dv 2)
    :x :up :up (:dv 2)
    :up :up :up :nx (:dv 1)
    (:dv 2)
    :x :top
    (:use (:instance (:theorem (equal (+ x (- x) y) (fix y)))
                     (x (standard-part (* 1/48 (/ (+ x (- x1))))))
                     (y (+ (standard-part (* 1/8 x (/ (+ x (- x1)))))
                           (standard-part (* -1/8 x1 (/ (+ x (- x1)))))
                           (standard-part (* 1/4 (expt x1 2) (/ (+ x (- x1)))))
                           (standard-part (* -1/4 (expt x 2) (/ (+ x (- x1)))))
                           (standard-part (* 1/6 (expt x 3) (/ (+ x (- x1)))))
                           (standard-part (* -1/6 (expt x1 3)
                                             (/ (+ x (- x1)))))))))
    (:change-goal nil t)
    :bash :pro (:demote 1)
    (:use (:instance standard-part-of-uminus
                     (x (* 1/48 (/ (+ x (- x1)))))))
    :promote (:demote 1)
    (:dv 1)
    (:dv 2)
    (:dv 1)
    (:dv 1)
    :s :top :promote (:dv 1)
    (:dv 1)
    (:dv 2)
    := (:dv 1)
    (:= (* -1/48 (/ (+ x (- x1)))))
    :up :up
    :up :nx
    :s :top
    :pro :bash)))

(local
 (defthmd trapezoidal-error-integrand-antiderivative-differential-into-local
     (implies (and (realp x)
                   (< -0 x)
                   (realp eps)
                   (< 0 (+ x eps)))
              (equal (trapezoidal-error-integrand-antiderivative-differential i x eps)
                     (TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE-DIFFERENTIAL-LOCAL i x eps)))))

(defthmd trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-eps
    (implies (and (realp x)
                  (< 0 x)
                  (standardp x)
                  (standardp i)
                  (realp eps) (i-small eps) (not (= eps 0))
                  (< 0 (+ x eps)))
             (equal (standard-part (trapezoidal-error-integrand-antiderivative-differential i x eps))
                    (trapezoidal-error-integrand i x)))
  :hints (("Goal"
           :use ((:instance
                  trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-eps-lemma)
                 (:instance
                  trapezoidal-error-integrand-antiderivative-differential-into-local))
           :in-theory nil)))


(local
 (encapsulate
    () ;; start lemmas for trapezoidal-error-integrand-antiderivative-differential-open

    (local
     (defthm lemma-1
         (implies (not (realp i))
                  (equal (trapezoidal-error-integrand-antiderivative i x)
                         (trapezoidal-error-integrand-antiderivative 0 x)))
       :hints (("Goal"
                :expand ((trapezoidal-error-integrand-antiderivative i x))))))

  (defthmd trapezoidal-error-integrand-antiderivative-differential-open
      (implies (and (realp x)
                    (< 0 x)
                    (realp x1)
                    (< 0 x1))
               (equal (trapezoidal-error-integrand-antiderivative-differential i x (- x1 x))
                      (/ (- (trapezoidal-error-integrand-antiderivative i x)
                            (trapezoidal-error-integrand-antiderivative i x1))
                         (- x x1))))
    :hints (("Goal"
             :use ((:instance SWAP-DIFFERENTIAL-TERM
                              (fx (trapezoidal-error-integrand-antiderivative i x))
                              (fx1 (trapezoidal-error-integrand-antiderivative i x1))))
             :in-theory (disable trapezoidal-error-integrand-antiderivative
                                 swap-differential-term))))
  ))

(local
 (encapsulate
     () ;; start lemmas for trapezoidal-error-integrand-antiderivative-differential-into-diff-of-cubes

     (local
      (defthm lemma-1
          (implies (and (realp x)
                        (realp x1)
                        (not (= x x1)))
                   (equal (+ 1/8 (* 1/8 X1 (/ (+ X (- X1)))))
                          (* 1/8 X (/ (+ X (- X1))))))
        :INSTRUCTIONS (:PRO (:DV 1)
                            (:= (* 1/8 (+ 1 (* X1 (/ (+ X (- X1)))))))
                            (:DV 2)
                            (:DV 1)
                            (:= (/ (+ X (- X1)) (+ X (- X1))))
                            (:REWRITE |(* (+ x y) z)|)
                            :TOP :S)))

   (defthmd trapezoidal-error-integrand-antiderivative-differential-into-diff-of-cubes
       (implies (and (realp x)
                     (< 0 x)
                     (realp x1)
                     (< 0 x1)
                     (not (= x x1)))
                (equal (TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE-DIFFERENTIAL i x (+ x1 (- x)))
                       (- (* 1/6
                             (- (term-inside-expt-cubed i x)
                                (term-inside-expt-cubed i x1))
                             (/ (- x x1)))
                          1/8)))
     :hints (("Goal"
              :use ((:instance
                     trapezoidal-error-integrand-antiderivative-differential-open)
                    )
              :in-theory (disable TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE-DIFFERENTIAL))))))

(local
 (defthmd TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE-realfix-i
     (equal (TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE (realfix i) x)
            (TRAPEZOIDAL-ERROR-INTEGRAND-ANTIDERIVATIVE i x))
   ))

(defthmd trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative
    (implies (and (realp x)
                  (< 0 x)
                  (standardp x)
                  (standardp i)
                  (realp x1)
                  (< 0 x1)
                  (i-close x x1)
                  (not (= x x1))
                  )
             (equal (standard-part
                     (/ (- (trapezoidal-error-integrand-antiderivative i x)
                           (trapezoidal-error-integrand-antiderivative i x1))
                        (- x x1)))
                    (trapezoidal-error-integrand i x)))
 :instructions
 ((:use
   (:instance
    trapezoidal-error-integrand-antiderivative-differential-into-diff-of-cubes))
  (:use
   (:instance
    trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative-lemma))
  (:use (:instance trapezoidal-error-integrand-antiderivative-realfix-i))
  :pro (:forwardchain 2)
  (:forwardchain 2)
  (:demote 11)
  (:dv 1)
  (:dv 1)
  :x-dumb
  (:= (* (+ (trapezoidal-error-integrand-antiderivative i x1)
            (- (trapezoidal-error-integrand-antiderivative i x)))
         (/ (- x1 x))))
  (:rewrite swap-differential-term)
  :top :pro (:dv 1)
  (:dv 1)
  :=
  :top :s))

;;; Finished showing that trapezoidal-error-integrand-antiderivative really is
;;; the antiderivative of trapezoidal-error-integrand

;;; Begin computing the integrap of trapezoidal-error-integrand uising FTC-2

(local
 (encapsulate nil
     (local (include-book "nonstd/nsa/derivative-raise" :dir :system))

   (defthmd expt-continuous
       (implies (and (realp x)
                     (< 0 x)
                     (standardp x)
		     (realp x1)
                     (< 0 x1)
                     (standardp n)
                     (i-close x x1))
                (I-CLOSE (expt x n)
                         (expt x1 n)))
     :hints (("Goal"
              :use ((:instance
                     (:functional-instance rdfn-continuous
                                           (rdfn (lambda (context x)
                                                   (expt (realposfix x) context)))
                                           (rdfn-domain positive-domain))
                     (y x1)
                     (context n)
                     )
                    )
              :in-theory (enable interval-definition-theory)
              )
             ("Subgoal 1"
              :use ((:instance
                     expt-differentiable-using-nonstd-criterion
                     (x (realposfix x))
                     (n context))))
             ))
   ))



(defthm trapezoidal-error-integrand-continuous
    (implies (and (realp x)
                  (< 0 x)
                  (standardp x)
		  (realp x1)
                  (< 0 x1)
                  (standardp n)
                  (i-close x x1))
             (I-CLOSE (trapezoidal-error-integrand n x)
                      (trapezoidal-error-integrand n x1)))
  :hints (("Goal"
           :use ((:instance expt-continuous (n 2))
                 (:instance i-close-limited
                            (x (expt x 2))
                            (y (expt x1 2)))
                 (:instance i-close-limited
                            (x x)
                            (y x1))
                 )
           :in-theory (e/d (i-close i-small)
                           (OPEN-TRAPEZOIDAL-ERROR-INTEGRAND
                            i-close-limited))
           )))

(defun map-trapezoidal-error-integrand (i p)
  (if (consp p)
      (cons (trapezoidal-error-integrand i (car p))
            (map-trapezoidal-error-integrand i (cdr p)))
      nil))

(local
 (defthm trapezoidal-error-integrand-not-real-context
     (implies (not (realp i))
              (equal (trapezoidal-error-integrand i x)
                     (trapezoidal-error-integrand 0 x)))))

(local
 (defthm map-trapezoidal-error-integrand-not-real-context
     (implies (not (realp i))
              (equal (map-trapezoidal-error-integrand i x)
                     (map-trapezoidal-error-integrand 0 x)))))

(defun riemann-trapezoidal-error-integrand (i p)
  (dotprod (deltas p)
           (map-trapezoidal-error-integrand i (cdr p))))

(local
 (defthm riemann-trapezoidal-error-integrand-not-real-context
     (implies (not (realp i))
              (equal (riemann-trapezoidal-error-integrand i x)
                     (riemann-trapezoidal-error-integrand 0 x)))))

(defthm-std standard-trapezoidal-error-integrand
    (implies (and (standardp i)
                  (standardp x))
             (standardp (trapezoidal-error-integrand i x))))

(defthm limited-trapezoidal-error-integrand
    (implies (and (standardp i)
                  (standardp x))
             (i-limited (trapezoidal-error-integrand i x)))
  :hints (("Goal"
           :use ((:instance standards-are-limited
                            (x (trapezoidal-error-integrand i x))))
           :in-theory (disable trapezoidal-error-integrand)))
  )

(encapsulate
    nil

    (defthm limited-riemann-trapezoidal-error-integrand-antiderivative
        (implies (and (realp a) (standardp a)
		      (realp b) (standardp b)
		      (inside-interval-p a (positive-domain))
		      (inside-interval-p b (positive-domain))
		      (< a b)
                      (standardp i))
	         (i-limited (riemann-trapezoidal-error-integrand
                             i (make-small-partition a b))))
      :otf-flg t
      :hints (("Goal"
	       :use ((:instance
                      (:functional-instance limited-riemann-rcdfn-prime-small-partition
				            (rcdfn-domain positive-domain)
				            (rcdfn
                                             (lambda (context x)
                                               (trapezoidal-error-integrand-antiderivative
                                                context
                                                x)))
                                            (rcdfn-prime
                                             (lambda (context x)
                                               (trapezoidal-error-integrand
                                                context
                                                x)))
				            (map-rcdfn-prime
                                             (lambda (context p)
                                               (map-trapezoidal-error-integrand
                                                context
                                                p)))
				            (riemann-rcdfn-prime
                                             (lambda (context p)
                                               (riemann-trapezoidal-error-integrand
                                                context p))))
                      (context i)
                      ))
               :in-theory (e/d (interval-definition-theory)
                               (trapezoidal-error-integrand-antiderivative
                                   trapezoidal-error-integrand
                                   OPEN-TRAPEZOIDAL-ERROR-INTEGRAND
                                   standard-part-is-standard-implies-close-to-standard-part))
               )
              ("Subgoal 3"
               :in-theory (enable trapezoidal-error-integrand))
              ("Subgoal 1"
               :use ((:instance
                      trapezoidal-error-integrand-antiderivative-differential-standard-part-is-derivative
                      (i context))
                     (:instance
                      standard-part-is-standard-implies-close-to-standard-part
                      (x (* (+ (trapezoidal-error-integrand-antiderivative context x)
                               (- (trapezoidal-error-integrand-antiderivative context x1)))
                            (/ (+ x (- x1)))))
                      (stdx (TRAPEZOIDAL-ERROR-INTEGRAND CONTEXT X)))
                     ))
              ))

    (local (in-theory (disable riemann-trapezoidal-error-integrand)))

    (defun-std strict-int-trapezoidal-error-integrand (i a b)
      (if (and (realp a)
	       (realp b)
	       (inside-interval-p a (positive-domain))
	       (inside-interval-p b (positive-domain))
	       (< a b))
          (standard-part (riemann-trapezoidal-error-integrand i (make-small-partition a b)))
          0))
)

(defun int-trapezoidal-error-integrand (i a b)
  (if (<= a b)
      (strict-int-trapezoidal-error-integrand i a b)
      (- (strict-int-trapezoidal-error-integrand i b a))))

(local
 (defthm close-plus-same-leading-term
     (implies (and (acl2-numberp x)
                   (acl2-numberp y)
                   (acl2-numberp z))
              (equal (i-close (+ z x) (+ z y))
                     (i-close x y)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))))

(local
 (defthm close-plus-same-second-term
     (implies (and (acl2-numberp x1)
                   (acl2-numberp x2)
                   (acl2-numberp y1)
                   (acl2-numberp y2)
                   (acl2-numberp z))
              (equal (i-close (+ x1 z y1) (+ x2 z y2))
                     (i-close (+ x1 y1) (+ x2 y2))))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))))

(LOCAL
 (defthm close-triple-sum
     (implies (and (i-close x1 y1)
                   (i-close x2 y2)
                   (i-close x3 y3))
              (i-close (+ x1 x2 x3)
                       (+ y1 y2 y3)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))))

(local
 (defthmd close-scaled
     (implies (and (i-close x x1)
                   (i-limited y)
                   (i-limited x))
              (i-close (* y x) (* y x1)))
   :hints (("Goal"
            :use ((:instance I-CLOSE-LIMITED
                             (x x)
                             (y x1)))
            :in-theory (e/d (i-close i-small)
                            (i-close-limited
                             i-close-limited-2))))))

(LOCAL
 (defthmd int-trapezoidal-error-integrand-computation-lemma
     (implies (and (inside-interval-p a (positive-domain))
                   (inside-interval-p b (positive-domain))
                   (realp i))
              (equal (int-trapezoidal-error-integrand i a b)
                     (- (trapezoidal-error-integrand-antiderivative i b)
                        (trapezoidal-error-integrand-antiderivative i a))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance ftc-2
                                         (rcdfn (lambda (context x)
                                                  (trapezoidal-error-integrand-antiderivative
                                                   context
                                                   x)))
                                         (rcdfn-prime (lambda (context x)
                                                        (trapezoidal-error-integrand
                                                         context
                                                         x)))
                                         (rcdfn-domain positive-domain)
                                         (map-rcdfn-prime (lambda (context p)
                                                            (map-trapezoidal-error-integrand
                                                             context
                                                             p)))
                                         (riemann-rcdfn-prime (lambda (context p)
                                                                (riemann-trapezoidal-error-integrand
                                                                 context
                                                                 p)))
                                         (strict-int-rcdfn-prime
                                          (lambda (context a b)
                                            (strict-int-trapezoidal-error-integrand context a b)))
                                         (int-rcdfn-prime
                                          (lambda (context a b)
                                            (int-trapezoidal-error-integrand context a b)))
                                         )
                   (context i)
                   ))
            :in-theory (e/d (interval-definition-theory)
                            (ftc-2
                             trapezoidal-error-integrand-antiderivative
                             OPEN-TRAPEZOIDAL-ERROR-INTEGRAND
                             i-close-limited
                             i-close-limited-2)))
           )))

(local
 (defthmd int-trapezoidal-error-integrand-i-to-i+1-lemma
    (implies (and (integerp i)
                  (< 0 i))
             (equal (int-trapezoidal-error-integrand i i (1+ i))
                    (- (- (/ (EXPT (- (1+ i) (+ I 1/2)) 3) 6)
                          (/ (1+ i) 8))
                       (- (/ (EXPT (- i (+ I 1/2)) 3) 6)
                          (/ i 8)))))
   :hints (("Goal"
            :use ((:instance int-trapezoidal-error-integrand-computation-lemma
                             (i i)
                             (a i)
                             (b (1+ i))))
            :in-theory (enable interval-definition-theory)
            ))))

(defthmd int-trapezoidal-error-integrand-i-to-i+1
    (implies (and (integerp i)
                  (< 0 i))
             (equal (int-trapezoidal-error-integrand i i (1+ i))
                    -1/12))
   :hints (("Goal"
            :use ((:instance int-trapezoidal-error-integrand-i-to-i+1-lemma))
            )))

;;; Done with the integral of the general error term! Now we'll explore the
;;; error term that is specific to ln x

(defun trapezoidal-error-integrand-for-ln (i x)
  (let ((i (realfix i))
        (x (realposfix x)))
    (* (trapezoidal-error-integrand i x)
       (- (/ (expt x 2))))))

(local
 (defthmd trapezoidal-error-integrand-for-ln-completion
     (implies (or (not (realp i))
                  (not (and (realp x) (< 0 x))))
              (equal (trapezoidal-error-integrand-for-ln i x)
                     (if (realp i)
                         (trapezoidal-error-integrand-for-ln i 1)
                         (if (and (realp x) (< 0 x))
                             (trapezoidal-error-integrand-for-ln 0 x)
                             (trapezoidal-error-integrand-for-ln 0 1)))))))

(defun trapezoidal-error-integrand-for-ln-antiderivative (i x)
  (let ((i (realfix i))
        (x (realposfix x)))
    (* -1/2
       (+ x
          (- (* (+ (* 2 I) 1)
                (acl2-ln x)))
          (- (/ (* i (1+ i)) x ))))))

(defun trapezoidal-error-integrand-for-ln-antiderivative-differentiall (i x eps)
  (LET ((I (REALFIX I))
        (X (REALPOSFIX X))
        (EPS (REALFIX EPS)))
    (/ (- (trapezoidal-error-integrand-for-ln-antiderivative i (+ x eps))
          (trapezoidal-error-integrand-for-ln-antiderivative i x))
       eps)))

(local
 (defthmd 1/x*x-is-non-negative
     (implies (realp x)
              (<= 0 (expt x -2)))
   :instructions (:pro (:dv 2)
                       (:= (* (/ x) (/ x)))
                       :top (:claim (realp (/ x)))
                       (:generalize ((/ x) x-inv))
                       (:use (:instance (:theorem (implies (and (realp x)
                                                                (realp y)
                                                                (<= 0 x)
                                                                (<= 0 y))
                                                           (<= 0 (* x y))))
                                        (x x-inv)
                                        (y x-inv)))
                       (:use (:instance (:theorem (implies (and (realp x)
                                                                (realp y)
                                                                (<= x 0)
                                                                (<= y 0))
                                                           (<= 0 (* x y))))
                                        (x x-inv)
                                        (y x-inv)))
                       :pro (:casesplit (<= x-inv 0))
                       :bash :bash
                       :bash :bash)))

(local
 (defthmd trapezoidal-error-integrand-for-ln-is-non-negative
     (implies (and (realp x)
                   (realp i)
                   (< 0 i)
                   (<= i x)
                   (<= x (1+ i)))
              (<= 0 (trapezoidal-error-integrand-for-ln i x)))
   :hints (("Goal"
            :use ((:instance trapezoidal-error-integrand-is-negative)
                  (:instance 1/x*x-is-non-negative))
            :IN-THEORY (DISABLE trapezoidal-error-integrand
                                (:TYPE-PRESCRIPTION TRAPEZOIDAL-ERROR-INTEGRAND))
            ))))


(defun trapezoidal-error-integrand-for-ln-simplified (i x)
  (* -1/2
     (+ 1
        (- (* (+ (* 2 I) 1) (/ X)))
        (/ (* i (1+ i)) (* x x)))))

(local
 (encapsulate nil

     (local
      (defthm lemma-1
          (equal (expt (- x (+ i 1/2)) 2)
                 (+ (* x x)
                    (- (* 2 I X))
                    (- X)
                    (* I I)
                    I
                    1/4))))

   (local
      (defthm lemma-2
          (equal (+ -1/8 (/ (expt (- x (+ i 1/2)) 2) 2))
                 (/ (+ (* x x)
                       (- (* 2 I X))
                       (- X)
                       (* I I)
                       I)
                    2))))

   (local
      (defthm lemma-3
          (implies (and (realp x)
                        (< 0 x)
                        (realp i)
                        )
                   (equal (* (- (/ (expt (- x (+ i 1/2)) 2) 2) 1/8)
                             (- (/ (expt x 2))))
                          (- (/ (+ 1
                                   (- (* 2 I (/ X)))
                                   (- (/ X))
                                   (/ (* i (1+ i)) (* x x)))
                                2))))))
   (local
    (defthm lemma-4
        (implies (and (realp x)
                      (< 0 x)
                      (realp i)
                      )
                 (equal (* (- (/ (expt (- x (+ i 1/2)) 2) 2) 1/8)
                           (- (/ (expt x 2))))
                        (* -1/2
                           (+ 1
                              (- (* (+ (* 2 I) 1) (/ X)))
                              (/ (* i (1+ i)) (* x x))))))))

   (defthmd trapezoidal-error-integrand-for-ln-simplified-works
        (implies (and (realp x)
                      (< 0 x)
                      (realp i)
                      )
                 (equal (trapezoidal-error-integrand-for-ln i x)
                        (trapezoidal-error-integrand-for-ln-simplified i x))))
   ))

(local
 (defun second-term (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (- (* (+ (* 2 I) 1) (/ X))))))

(local
 (defun second-term-antiderivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (- (* (+ (* 2 I) 1) (acl2-ln X))))))

(local
 (defun second-term-antiderivative-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (second-term-antiderivative i (+ x eps))
           (second-term-antiderivative i x))
        eps))))


(local
 (encapsulate nil

     (local
      (defthm subgoal-3
          (implies (and (realp x)
                        (< 0 x)
                        (realp (+ x eps))
                        (< 0 (+ x eps)))
                   (equal 0
                          (* (+ (- (* 1 (+ (* 2 (realfix context2)) 1)))
                                (- (- (* 1 (+ (* 2 (realfix context2)) 1)))))
                             (/ eps))))
        :rule-classes nil
        :instructions (:pro (:dv 2)
                            (:dv 1)
                            (:dv 2)
                            (:rewrite |(- (- x))|)
                            :up
                            (:claim (realp (* 1 (+ (* 2 (realfix context2)) 1))))
                            :top
                            (:generalize ((* 1 (+ (* 2 (realfix context2)) 1))
                                          xx))
                            :s)))

   (defthmd second-term-antiderivative-differential-standard-part-is-derivative-eps
      (implies (and (realp x)
                    (< 0 x)
                    (standardp x)
                    (standardp i)
                    (realp eps) (i-small eps) (not (= eps 0))
                    (< 0 (+ x eps)))
               (equal (standard-part (second-term-antiderivative-differential i x eps))
                      (second-term i x)))
    :hints (("Goal"
             :use ((:instance
                    (:functional-instance
                     differential-dc-fn1*fn2-close
                     (dc-fn-domain positive-domain)
                     (dc-car-context (lambda (x) x))
                     (dc-cdr-context (lambda (x) x))
                     ;;;
                     (dc-fn1 (lambda (i x) (acl2-ln (realposfix x))))
                     (differential-dc-fn1
                      (lambda (i x eps)
                        (/ (- (acl2-ln (+ x eps))
                              (acl2-ln x))
                           (realfix eps))))
                     (derivative-dc-fn1 (lambda (i x) (/ x)))
                     ;;;
                     (dc-fn2
                      (lambda (i x)
                        (- (* (+ (* 2 (realfix I)) 1)))))
                     (differential-dc-fn2 (lambda (i x eps) 0))
                     (derivative-dc-fn2 (lambda (i x) 0))
                     ;;;
                     (dc-fn1*fn2
                      (lambda (i x)
                        (second-term-antiderivative i x)))
                     (differential-dc-fn1*fn2
                      (lambda (i x eps)
                        (second-term-antiderivative-differential i x eps)))
                     (derivative-dc-fn1*fn2
                      (lambda (i x)
                        (second-term (realfix i) x)))
                     ;;;
                     (dc-fnz (lambda (i x) 1))
                     )
                    (context i))
                   )
             :in-theory (enable inside-interval-p)
             )
            ("Subgoal 7"
             :use ((:instance acl2-ln-real-derivative
                              (x x)
                              (y (+ X (/ (I-LARGE-INTEGER)))))
                   (:instance i-close-to-small-sum
                              (x x)
                              (eps (/ (i-large-integer))))
                   (:instance close-to-standard-implies-standard-part-is-that-standard
                              (x (+ (- (* (I-LARGE-INTEGER) (ACL2-LN X)))
                                    (* (I-LARGE-INTEGER)
                                       (ACL2-LN (+ (/ (I-LARGE-INTEGER)) X)))))
                              (stdx (/ x)))
                   )
             :in-theory (e/d (inside-interval-p)
                             (acl2-ln-real-derivative
                              i-close-to-small-sum
                              STANDARD-PART-OF-PLUS
                              STANDARD-PART-OF-uminus))
             )
            ("Subgoal 4"
             :use ((:instance acl2-ln-real-derivative
                              (x x)
                              (y y1))
                   (:instance acl2-ln-real-derivative
                              (x x)
                              (y y2))
                   (:instance i-close-limited-2
                              (x (+ (* (ACL2-LN X) (/ (+ X (- Y1))))
                                    (- (* (ACL2-LN Y1) (/ (+ X (- Y1)))))))
                              (y (/ x)))
                   )
             :in-theory (e/d (inside-interval-p)
                             (acl2-ln-real-derivative
                              i-close-to-small-sum
                              STANDARD-PART-OF-PLUS
                              STANDARD-PART-OF-uminus))
             )
            ("Subgoal 3"
             :by (:instance Subgoal-3))
            )))
 )

(local
 (defthmd second-term-antiderivative-notreal-i
     (implies (not (realp i))
              (equal (SECOND-TERM-ANTIDERIVATIVE I X)
                     (SECOND-TERM-ANTIDERIVATIVE 0 X)))))

(local
 (defthmd second-term-antiderivative-differential-standard-part-is-derivative
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1))
                   )
              (equal (standard-part
                      (/ (- (second-term-antiderivative i x)
                            (second-term-antiderivative i x1))
                         (- x x1)))
                     (second-term i x)))
   :hints (("Goal"
            :use ((:instance second-term-antiderivative-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance
                   second-term-antiderivative-differential-standard-part-is-derivative-eps
                   (i 0)
                   (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (second-term-antiderivative I X))
                             (fx1 (second-term-antiderivative I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (e/d (second-term-antiderivative-notreal-i)
                            (STANDARD-PART-OF-PLUS
                             PREFER-POSITIVE-ADDENDS-EQUAL
                             |(equal (+ (- c) x) y)|
                             second-term-antiderivative
                             second-term)
                            )))))

(local
 (defun third-term (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (/ (* i (1+ i)) (* x x)))))

(local
 (defun third-term-antiderivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (- (/ (* i (1+ i)) x)))))

(local
 (defun third-term-antiderivative-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (third-term-antiderivative i (+ x eps))
           (third-term-antiderivative i x))
        eps))))

(local
 (defthm-std standard-expt
     (implies (and (standardp x)
                   (standardp n))
              (standardp (expt x n)))))

(local
 (defthm limited-expt--2
     (implies (standardp x)
              (i-limited (expt x -2)))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (expt x -2))))))
   ))

(local
 (defthmd third-term-antiderivative-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (third-term-antiderivative-differential i x eps))
                     (third-term i x)))
   :hints (("goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1*fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                     ;;;
                    (dc-fn1 (lambda (i x) (expt (realposfix x) -1)))
                    (differential-dc-fn1
                     (lambda (i x eps)
                       (/ (- (expt (+ x eps) -1)
                             (expt x -1))
                          (realfix eps))))
                    (derivative-dc-fn1 (lambda (i x) (- (expt (realposfix x) -2))))
                     ;;;
                    (dc-fn2
                     (lambda (i x)
                       (- (* (realfix i) (1+ i)))))
                    (differential-dc-fn2 (lambda (i x eps) 0))
                    (derivative-dc-fn2 (lambda (i x) 0))
                     ;;;
                    (dc-fn1*fn2
                     (lambda (i x)
                       (third-term-antiderivative i x)))
                    (differential-dc-fn1*fn2
                     (lambda (i x eps)
                       (third-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn1*fn2
                     (lambda (i x)
                       (third-term i x)))
                     ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (enable inside-interval-p)
            )
           ("subgoal 8"
            :use ((:instance derivative-expt-is-derivative
                             (n -1)
                             (x x)
                             (x1 (+ x (/ (i-large-integer)))))
                  (:instance i-close-to-small-sum
                             (x x)
                             (eps (/ (i-large-integer))))
                  (:instance close-to-standard-implies-standard-part-is-that-standard
                             (x (* (+ (/ (realposfix (+ x (/ (i-large-integer)))))
                                      (- (/ (realposfix x))))
                                   (/ (realfix (/ (i-large-integer))))))
                             (stdx (- (expt (realposfix x) -2))))
                  )
            :in-theory (e/d (inside-interval-p)
                            (derivative-expt-is-derivative
                             i-close-to-small-sum
                             standard-part-of-plus
                             standard-part-of-uminus))
            )
           ("subgoal 5"
            :use ((:instance derivative-expt-is-derivative
                             (n -1)
                             (x x)
                             (x1 y1))
                  (:instance derivative-expt-is-derivative
                             (n -1)
                             (x x)
                             (x1 y2))
                  (:instance i-close-limited-2
                             (x (+ (* (/ x) (/ (+ x (- y1))))
                                   (- (* (/ y1) (/ (+ x (- y1)))))))
                             (y (- (expt (realposfix x) -2))))
                  )
            :in-theory (e/d (inside-interval-p)
                            (acl2-ln-real-derivative
                             i-close-to-small-sum
                             standard-part-of-plus
                             standard-part-of-uminus))
            )
           )))

(local
 (defthmd third-term-antiderivative-notreal-i
     (implies (not (realp i))
              (equal (third-TERM-ANTIDERIVATIVE I X)
                     (third-TERM-ANTIDERIVATIVE 0 X)))))

(local
 (defthmd third-term-antiderivative-differential-standard-part-is-derivative
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1))
                   )
              (equal (standard-part
                      (/ (- (third-term-antiderivative i x)
                            (third-term-antiderivative i x1))
                         (- x x1)))
                     (third-term i x)))
   :hints (("Goal"
            :use ((:instance third-term-antiderivative-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance third-term-antiderivative-differential-standard-part-is-derivative-eps
                             (i 0)
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (third-term-antiderivative I X))
                             (fx1 (third-term-antiderivative I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (e/d (third-term-antiderivative-notreal-i
                             )
                            (STANDARD-PART-OF-PLUS
                             PREFER-POSITIVE-ADDENDS-EQUAL
                             |(equal (+ (- c) x) y)|
                             third-term-antiderivative
                             third-term)
                            )))))

(local
 (defun second-third-term (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (+ (- (* (+ (* 2 I) 1) (/ X)))
        (/ (* i (1+ i)) (* x x))))))

(local
 (defun second-third-term-antiderivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (+ (- (* (+ (* 2 I) 1) (acl2-ln X)))
        (- (/ (* i (1+ i)) x))))))

(local
 (defun second-third-term-antiderivative-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (second-third-term-antiderivative i (+ x eps))
           (second-third-term-antiderivative i x))
        eps))))

(local
 (defthm-std standard-third-term
     (implies (and (standardp i)
                   (standardp x))
              (standardp (third-term i x)))))
(local
 (defthm-std standard-second-term
     (implies (and (standardp i)
                   (standardp x))
              (standardp (second-term i x)))))

(local
 (defthm second-third-term-antiderivative-0-x
     (implies (and (realp x)
                   (< 0 x))
              (equal (SECOND-THIRD-TERM-ANTIDERIVATIVE 0 X)
                     (- (acl2-ln x))))))

(local
 (defthmd second-third-term-antiderivative-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (second-third-term-antiderivative-differential i x eps))
                     (second-third-term i x)))
   :hints (("goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1+fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                     ;;;
                    (dc-fn1 (lambda (i x) (second-term-antiderivative i x)))
                    (differential-dc-fn1
                     (lambda (i x eps)
                       (second-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn1 (lambda (i x) (second-term i x)))
                     ;;;
                    (dc-fn2 (lambda (i x) (third-term-antiderivative i x)))
                    (differential-dc-fn2
                     (lambda (i x eps)
                       (third-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn2 (lambda (i x) (third-term i x)))
                     ;;;
                    (dc-fn1+fn2
                     (lambda (i x)
                       (second-third-term-antiderivative i x)))
                    (differential-dc-fn1+fn2
                     (lambda (i x eps)
                       (second-third-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn1+fn2
                     (lambda (i x)
                       (second-third-term i x)))
                     ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (e/d (inside-interval-p)
                            (second-term
                             second-term-antiderivative-differential
                             second-term-antiderivative
                             third-term
                             third-term-antiderivative-differential
                             third-term-antiderivative
                             STANDARD-PART-OF-PLUS
                             STANDARD-PART-OF-UMINUS))
            )
           ("Subgoal 9"
            :use ((:instance
                   third-term-antiderivative-differential-standard-part-is-derivative-eps
                   (i context2)
                   (eps (/ (i-large-integer)))))
            )
           ("Subgoal 8"
            :in-theory (enable third-TERM-ANTIDERIVATIVE-DIFFERENTIAL))
           ("subgoal 7"
            :use ((:instance third-term-antiderivative-differential-standard-part-is-derivative
                             (i context2)
                             (x x)
                             (x1 y1))
                  (:instance third-term-antiderivative-differential-standard-part-is-derivative
                             (i context2)
                             (x x)
                             (x1 y2))
                  (:instance standard-part-is-standard-implies-limited
                             (x (+ (* (third-term-antiderivative context2 x)
                                      (/ (+ x (- y1))))
                                   (- (* (third-term-antiderivative context2 y1)
                                         (/ (+ x (- y1)))))))
                             (stdx (third-term context2 x)))
                  (:instance close-to-standard-are-close
                             (x1 (+ (* (THIRD-TERM-ANTIDERIVATIVE CONTEXT2 X)
                                       (/ (+ X (- Y1))))
                                    (- (* (THIRD-TERM-ANTIDERIVATIVE CONTEXT2 Y1)
                                          (/ (+ X (- Y1)))))))
                             (x2 (+ (* (THIRD-TERM-ANTIDERIVATIVE CONTEXT2 X)
                                       (/ (+ X (- Y2))))
                                    (- (* (THIRD-TERM-ANTIDERIVATIVE CONTEXT2 Y2)
                                          (/ (+ X (- Y2)))))))
                             (stdx (third-term context2 x)))
                  )
            :in-theory (e/d (inside-interval-p)
                            (second-term
                             second-term-antiderivative-differential
                             second-term-antiderivative
                             third-term
                             third-term-antiderivative-differential
                             third-term-antiderivative
                             i-close-to-small-sum
                             standard-part-of-plus
                             standard-part-of-uminus))
            )
           ("subgoal 6"
            :use ((:instance second-term-antiderivative-differential-standard-part-is-derivative
                             (i context1)
                             (x x)
                             (x1 y1))
                  (:instance second-term-antiderivative-differential-standard-part-is-derivative
                             (i context1)
                             (x x)
                             (x1 y2))
                  (:instance standard-part-is-standard-implies-limited
                             (x (+ (* (second-term-antiderivative context1 x)
                                      (/ (+ x (- y1))))
                                   (- (* (second-term-antiderivative context1 y1)
                                         (/ (+ x (- y1)))))))
                             (stdx (second-term context1 x)))
                  (:instance close-to-standard-are-close
                             (x1 (+ (* (SECOND-TERM-ANTIDERIVATIVE CONTEXT1 X)
                                       (/ (+ X (- Y1))))
                                    (- (* (SECOND-TERM-ANTIDERIVATIVE CONTEXT1 Y1)
                                          (/ (+ X (- Y1)))))))
                             (x2 (+ (* (SECOND-TERM-ANTIDERIVATIVE CONTEXT1 X)
                                       (/ (+ X (- Y2))))
                                    (- (* (SECOND-TERM-ANTIDERIVATIVE CONTEXT1 Y2)
                                          (/ (+ X (- Y2)))))))
                             (stdx (second-term context1 x)))
                  )
            :in-theory (e/d (inside-interval-p)
                            (second-term
                             second-term-antiderivative-differential
                             second-term-antiderivative
                             third-term
                             third-term-antiderivative-differential
                             third-term-antiderivative
                             i-close-to-small-sum
                             standard-part-of-plus
                             standard-part-of-uminus))
            )
           ("Subgoal 5"
            :in-theory (enable second-term-antiderivative))
           ("Subgoal 4"
            :use ((:instance second-term-antiderivative-differential-standard-part-is-derivative-eps
                             (i context1)
                             (x x)
                             (eps (/ (i-large-integer))))))
           ("Subgoal 3"
            :in-theory (enable second-term-antiderivative-differential))
           ("Subgoal 2"
            :in-theory (enable second-term))
           ("Subgoal 1"
            :in-theory (enable second-term-antiderivative-differential))
           )))

(local
 (defthmd second-third-term-antiderivative-notreal-i
     (implies (not (realp i))
              (equal (second-third-term-antiderivative i x)
                     (second-third-term-antiderivative 0 x)))))

(local
 (defthmd second-third-term-antiderivative-differential-standard-part-is-derivative
     (implies
      (and (realp x)
           (< 0 x)
           (standardp x)
           (standardp i)
           (realp x1)
           (< 0 x1)
           (i-close x x1)
           (not (= x x1)))
      (equal (standard-part (/ (- (second-third-term-antiderivative i x)
                                  (second-third-term-antiderivative i x1))
                               (- x x1)))
             (second-third-term i x)))
   :hints (("Goal"
            :use ((:instance second-third-term-antiderivative-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance second-third-term-antiderivative-differential-standard-part-is-derivative-eps
                             (i 0)
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (second-third-term-antiderivative I X))
                             (fx1 (second-third-term-antiderivative I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (e/d (second-third-term-antiderivative-notreal-i
                             )
                            (STANDARD-PART-OF-PLUS
                             PREFER-POSITIVE-ADDENDS-EQUAL
                             |(equal (+ (- c) x) y)|
                             second-third-term-antiderivative
                             second-third-term)
                            )))))

(local
 (defun first-second-third-term (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (+ 1
        (- (* (+ (* 2 I) 1) (/ X)))
        (/ (* i (1+ i)) (* x x))))))

(local
 (defun first-second-third-term-antiderivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (+ x
        (- (* (+ (* 2 I) 1) (acl2-ln X)))
        (- (/ (* i (1+ i)) x))))))

(local
 (defun first-second-third-term-antiderivative-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (first-second-third-term-antiderivative i (+ x eps))
           (first-second-third-term-antiderivative i x))
        eps))))

(local
 (defthm-std standard-second-third-term
     (implies (and (standardp i)
                   (standardp x))
              (standardp (second-third-term i x)))))

(local
 (defun x-minus-ln-x (x)
   (let ((x (realposfix x)))
     (+ x (- (acl2-ln x))))))

(local
 (defun x-minus-ln-x-differential (x eps)
   (let ((x (realposfix x))
         (eps (realfix eps)))
     (/ (- (x-minus-ln-x (+ x eps))
           (x-minus-ln-x x))
        eps))))

(local
 (defun x-minus-ln-x-derivative (x)
   (let ((x (realposfix x)))
     (+ 1 (- (/ x))))))

(local
 (defthm acl2-ln-real-derivative-standard-part
     (implies (and (realp x) (< 0 x)
                   (realp y) (< 0 y)
                   (standardp x)
                   (i-close x y) (not (equal x y)))
              (equal (standard-part (/ (- (acl2-ln x) (acl2-ln y))
                                       (- x y)))
                     (/ x)))
   :hints (("Goal"
            :use ((:instance acl2-ln-real-derivative)
                  (:instance close-to-standard-implies-standard-part-is-that-standard
                             (x (/ (- (acl2-ln x) (acl2-ln y))
                                   (- x y)))
                             (stdx (/ x))))))))


(local
 (encapsulate
     () ;; start lemmas for x-minus-ln-x-differential-standard-part-is-derivative-eps

     (local
      (defthmd lemma-1
          (equal (+ (* (i-large-integer) (acl2-ln x))
                    (- (* (i-large-integer)
                          (acl2-ln (+ (/ (i-large-integer)) x)))))
                 (- (+ (- (* (i-large-integer) (acl2-ln x)))
                       (* (i-large-integer)
                          (acl2-ln (+ (/ (i-large-integer)) x))))))))

   (defthmd x-minus-ln-x-differential-standard-part-is-derivative-eps
       (implies (and (realp x)
                     (< 0 x)
                     (standardp x)
                     (realp eps) (i-small eps) (not (= eps 0))
                     (< 0 (+ x eps)))
                (equal (standard-part (x-minus-ln-x-differential x eps))
                       (x-minus-ln-x-DERIVATIVE x)))
     :hints (("goal"
              :use ((:instance
                     (:functional-instance
                      differential-dc-fn1+fn2-close
                      (dc-fn-domain positive-domain)
                      (dc-car-context (lambda (x) x))
                      (dc-cdr-context (lambda (x) x))
                      ;;;
                      (dc-fn1 (lambda (i x) (realfix x)))
                      (differential-dc-fn1
                       (lambda (i x eps)
                         (/ (realfix eps) (realfix eps))))
                      (derivative-dc-fn1 (lambda (i x) 1))
                      ;;;
                      (dc-fn2 (lambda (i x) (- (acl2-ln (REALPOSFIX x)))))
                      (differential-dc-fn2
                       (lambda (i x eps)
                         (/ (- (- (ACL2-LN  (+ (REALPOSFIX x) EPS)))
                               (- (ACL2-LN  (REALPOSFIX x))))
                            EPS)))
                      (derivative-dc-fn2 (lambda (i x) (- (/ (REALposFIX X)))))
                      ;;;
                      (dc-fn1+fn2
                       (lambda (i x)
                         (x-minus-ln-x x)))
                      (differential-dc-fn1+fn2
                       (lambda (i x eps)
                         (x-minus-ln-x-differential x eps)))
                      (derivative-dc-fn1+fn2
                       (lambda (i x)
                         (x-minus-ln-x-derivative x)))
                      ;;;
                      (dc-fnz (lambda (i x) 1))
                      )
                     (context 0))
                    )
              :in-theory (e/d (inside-interval-p)
                              (STANDARD-PART-OF-PLUS
                               STANDARD-PART-OF-UMINUS))
              )
             ("Subgoal 7"
              :use ((:instance acl2-ln-real-derivative-standard-part
                               (x x)
                               (y (+ x (/ (i-large-integer)))))
                    (:instance i-close-to-small-sum
                               (x x)
                               (eps (/ (i-large-integer))))
                    (:INSTANCE LEMMA-1)
                    )
              :IN-THEORY (E/D (INSIDE-INTERVAL-P)
                              (|(- (+ x y))|))
              )
             ("subgoal 5"
              :use ((:instance acl2-ln-real-derivative
                               (x x)
                               (Y Y1))
                    (:instance acl2-ln-real-derivative
                               (x x)
                               (Y Y2))
                    (:INSTANCE acl2-ln-real-derivative-standard-part
                               (Y Y1))
                    (:INSTANCE acl2-ln-real-derivative-standard-part
                               (Y Y2))
                    (:INSTANCE I-LARGE-UMINUS
                               (X (+ (* (ACL2-LN X) (/ (+ X (- Y1))))
                                     (- (* (ACL2-LN Y1) (/ (+ X (- Y1))))))))
                    (:INSTANCE I-LARGE-UMINUS
                               (X (+ (* (ACL2-LN X) (/ (+ X (- Y2))))
                                     (- (* (ACL2-LN Y1) (/ (+ X (- Y2))))))))
                    (:instance standard-part-is-standard-implies-limited
                               (x (/ (- (ACL2-LN X) (ACL2-LN Y1)) (- X Y1)))
                               (stdx (/ x)))
                    (:instance close-to-standard-are-close
                               (x1 (/ (- (ACL2-LN X) (ACL2-LN Y1)) (- X Y1)))
                               (x2 (/ (- (ACL2-LN X) (ACL2-LN Y2)) (- X Y2)))
                               (stdx (/ x)))
                    (:INSTANCE I-CLOSE-TRANSITIVE
                               (X (* (+ (ACL2-LN X) (- (ACL2-LN Y1)))
                                     (/ (+ X (- Y1)))))
                               (Y (/ X))
                               (Z (* (+ (ACL2-LN X) (- (ACL2-LN Y2)))
                                     (/ (+ X (- Y2))))))
                    (:INSTANCE CLOSE-UMINUS
                               (X (+ (- (* (ACL2-LN X) (/ (+ X (- Y1)))))
                                     (* (ACL2-LN Y1) (/ (+ X (- Y1))))))
                               (Y (+ (- (* (ACL2-LN X) (/ (+ X (- Y2)))))
                                     (* (ACL2-LN Y2) (/ (+ X (- Y2)))))))
                    )
              :in-theory (e/d (inside-interval-p)
                              (i-close-to-small-sum
                               I-LARGE-UMINUS
                               I-CLOSE-TRANSITIVE
                               CLOSE-UMINUS
                               standard-part-of-plus
                               standard-part-of-uminus))
              )
             ))
   ))

(local
 (defthmd first-second-third-term-antiderivative-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (first-second-third-term-antiderivative-differential i x eps))
                     (first-second-third-term i x)))
   :hints (("goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1+fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                     ;;;
                    (dc-fn1 (lambda (i x) (realfix x)))
                    (differential-dc-fn1
                     (lambda (i x eps)
                       (/ (realfix eps) (realfix eps))))
                    (derivative-dc-fn1 (lambda (i x) 1))
                     ;;;
                    (dc-fn2 (lambda (i x) (second-third-term-antiderivative i x)))
                    (differential-dc-fn2
                     (lambda (i x eps)
                       (second-third-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn2 (lambda (i x) (second-third-term i x)))
                     ;;;
                    (dc-fn1+fn2
                     (lambda (i x)
                       (first-second-third-term-antiderivative i x)))
                    (differential-dc-fn1+fn2
                     (lambda (i x eps)
                       (first-second-third-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn1+fn2
                     (lambda (i x)
                       (first-second-third-term i x)))
                     ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (e/d (inside-interval-p)
                            (second-third-term
                             second-third-term-antiderivative-differential
                             second-third-term-antiderivative
                             second-third-term
                             second-third-term-antiderivative-differential
                             second-third-term-antiderivative
                             STANDARD-PART-OF-PLUS
                             STANDARD-PART-OF-UMINUS))
            )
           ("Subgoal 7"
            :use ((:instance
                   second-third-term-antiderivative-differential-standard-part-is-derivative-eps
                   (i context2)
                   (eps (/ (i-large-integer)))))
            )
           ("Subgoal 6"
            :in-theory (enable second-third-TERM-ANTIDERIVATIVE-DIFFERENTIAL))
           ("subgoal 5"
            :use ((:instance second-third-term-antiderivative-differential-standard-part-is-derivative
                             (i context2)
                             (x x)
                             (x1 y1))
                  (:instance second-third-term-antiderivative-differential-standard-part-is-derivative
                             (i context2)
                             (x x)
                             (x1 y2))
                  (:instance standard-part-is-standard-implies-limited
                             (x (+ (* (second-third-term-antiderivative context2 x)
                                      (/ (+ x (- y1))))
                                   (- (* (second-third-term-antiderivative context2 y1)
                                         (/ (+ x (- y1)))))))
                             (stdx (second-third-term context2 x)))
                  (:instance close-to-standard-are-close
                             (x1 (+ (* (second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 X)
                                       (/ (+ X (- Y1))))
                                    (- (* (second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 Y1)
                                          (/ (+ X (- Y1)))))))
                             (x2 (+ (* (second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 X)
                                       (/ (+ X (- Y2))))
                                    (- (* (second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 Y2)
                                          (/ (+ X (- Y2)))))))
                             (stdx (second-third-term context2 x)))
                  )
            :in-theory (e/d (inside-interval-p)
                            (second-third-term
                             second-third-term-antiderivative-differential
                             second-third-term-antiderivative
                             i-close-to-small-sum
                             standard-part-of-plus
                             standard-part-of-uminus))
            )
           ("Subgoal 3"
            :in-theory (enable second-third-term-antiderivative))
           ("Subgoal 2"
            :in-theory (enable second-third-term))
           ("Subgoal 1"
            :in-theory (enable second-third-term-antiderivative-differential))
           )))


(local
 (defthmd first-second-third-term-antiderivative-notreal-i
     (implies (not (realp i))
              (equal (first-second-third-term-antiderivative i x)
                     (first-second-third-term-antiderivative 0 x)))))

(local
 (defthmd first-second-third-term-antiderivative-differential-standard-part-is-derivative
     (implies
      (and (realp x)
           (< 0 x)
           (standardp x)
           (standardp i)
           (realp x1)
           (< 0 x1)
           (i-close x x1)
           (not (= x x1)))
      (equal (standard-part (/ (- (first-second-third-term-antiderivative i x)
                                  (first-second-third-term-antiderivative i x1))
                               (- x x1)))
             (first-second-third-term i x)))
   :hints (("Goal"
            :use ((:instance first-second-third-term-antiderivative-differential-standard-part-is-derivative-eps
                             (eps (- x1 x)))
                  (:instance first-second-third-term-antiderivative-differential-standard-part-is-derivative-eps
                             (i 0)
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (first-second-third-term-antiderivative I X))
                             (fx1 (first-second-third-term-antiderivative I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (e/d (first-second-third-term-antiderivative-notreal-i
                             )
                            (STANDARD-PART-OF-PLUS
                             PREFER-POSITIVE-ADDENDS-EQUAL
                             |(equal (+ (- c) x) y)|
                             first-second-third-term-antiderivative
                             first-second-third-term)
                            )))))

#|
(defun trapezoidal-error-integrand-for-ln-simplified (i x)
  (* -1/2
     (+ 1
        (- (* (+ (* 2 I) 1) (/ X)))
        (/ (* i (1+ i)) (* x x)))))
|#

(local
 (defun whole-term (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (* -1/2 (first-second-third-term i x)))))

(local
 (defun whole-term-antiderivative (i x)
   (let ((i (realfix i))
         (x (realposfix x)))
     (* -1/2 (first-second-third-term-antiderivative i x)))))

(local
 (defun whole-term-antiderivative-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (whole-term-antiderivative i (+ x eps))
           (whole-term-antiderivative i x))
        eps))))

(local
 (defthm-std standard-first-second-third
     (implies (and (standardp i)
                   (standardp x))
              (standardp (first-second-third-term i x)))))

(local
 (defthmd whole-term-antiderivative-differential-standard-part-is-derivative-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (whole-term-antiderivative-differential i x eps))
                     (whole-term i x)))
   :hints (("goal"
            :use ((:instance
                   (:functional-instance
                    differential-dc-fn1*fn2-close
                    (dc-fn-domain positive-domain)
                    (dc-car-context (lambda (x) x))
                    (dc-cdr-context (lambda (x) x))
                     ;;;
                    (dc-fn1 (lambda (i x) -1/2))
                    (differential-dc-fn1 (lambda (i x eps) 0))
                    (derivative-dc-fn1 (lambda (i x) 0))
                     ;;;
                    (dc-fn2 (lambda (i x) (first-second-third-term-antiderivative i x)))
                    (differential-dc-fn2
                     (lambda (i x eps)
                       (first-second-third-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn2 (lambda (i x) (first-second-third-term i x)))
                     ;;;
                    (dc-fn1*fn2
                     (lambda (i x)
                       (whole-term-antiderivative i x)))
                    (differential-dc-fn1*fn2
                     (lambda (i x eps)
                       (whole-term-antiderivative-differential i x eps)))
                    (derivative-dc-fn1*fn2
                     (lambda (i x)
                       (whole-term i x)))
                     ;;;
                    (dc-fnz (lambda (i x) 1))
                    )
                   (context i))
                  )
            :in-theory (e/d (inside-interval-p)
                            (first-second-third-term
                             first-second-third-term-antiderivative-differential
                             first-second-third-term-antiderivative
                             STANDARD-PART-OF-PLUS
                             STANDARD-PART-OF-UMINUS))
            )
           ("subgoal 6"
            :use ((:instance first-second-third-term-antiderivative-differential-standard-part-is-derivative
                             (i context2)
                             (x x)
                             (x1 y1))
                  (:instance first-second-third-term-antiderivative-differential-standard-part-is-derivative
                             (i context2)
                             (x x)
                             (x1 y2))
                  (:instance standard-part-is-standard-implies-limited
                             (x (+ (* (first-second-third-term-antiderivative context2 x)
                                      (/ (+ x (- y1))))
                                   (- (* (first-second-third-term-antiderivative context2 y1)
                                         (/ (+ x (- y1)))))))
                             (stdx (first-second-third-term context2 x)))
                  (:instance close-to-standard-are-close
                             (x1 (+ (* (first-second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 X)
                                       (/ (+ X (- Y1))))
                                    (- (* (first-second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 Y1)
                                          (/ (+ X (- Y1)))))))
                             (x2 (+ (* (first-second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 X)
                                       (/ (+ X (- Y2))))
                                    (- (* (first-second-THIRD-TERM-ANTIDERIVATIVE CONTEXT2 Y2)
                                          (/ (+ X (- Y2)))))))
                             (stdx (first-second-third-term context2 x)))
                  )
            :in-theory (e/d (inside-interval-p)
                            (first-second-third-term
                             first-second-third-term-antiderivative-differential
                             first-second-third-term-antiderivative
                             i-close-to-small-sum
                             standard-part-of-plus
                             standard-part-of-uminus))
            )
           ("Subgoal 5"
            :in-theory (enable FIRST-second-third-term-antiderivative))
           ("Subgoal 4"
            :use ((:instance
                   first-second-third-term-antiderivative-differential-standard-part-is-derivative-eps
                   (i context2)
                   (eps (/ (i-large-integer)))))
            )
           ("Subgoal 3"
            :in-theory (enable FIRST-second-third-term-antiderivative-differential))
           ("Subgoal 2"
            :in-theory (enable first-second-third-term))
           ("Subgoal 1"
            :in-theory (enable first-second-third-term-antiderivative-differential))
           )))

(local
 (defthmd trapezoidal-error-integrand-for-ln->whole-term
     (equal (trapezoidal-error-integrand-for-ln i x)
            (whole-term i x))))

(local
 (defthmd trapezoidal-error-integrand-for-ln-antiderivative->whole-term-antiderivative
     (equal (trapezoidal-error-integrand-for-ln-antiderivative i x)
            (whole-term-antiderivative i x))))

(local
 (defun trapezoidal-error-integrand-for-ln-antiderivative-differential (i x eps)
   (let ((i (realfix i))
         (x (realposfix x))
         (eps (realfix eps)))
     (/ (- (trapezoidal-error-integrand-for-ln-antiderivative i (+ x eps))
           (trapezoidal-error-integrand-for-ln-antiderivative i x))
        eps))))

(local
 (defthmd trapezoidal-error-integrand-for-ln-antiderivative-works-eps
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp eps) (i-small eps) (not (= eps 0))
                   (< 0 (+ x eps)))
              (equal (standard-part (trapezoidal-error-integrand-for-ln-antiderivative-differential i x eps))
                     (trapezoidal-error-integrand-for-ln i x)))
   :hints (("Goal"
            :use ((:instance
                   whole-term-antiderivative-differential-standard-part-is-derivative-eps))
            :in-theory (e/d (trapezoidal-error-integrand-for-ln->whole-term
                             trapezoidal-error-integrand-for-ln-antiderivative->whole-term-antiderivative
                             )
                            (whole-term
                             whole-term-antiderivative
                             trapezoidal-error-integrand-for-ln
                             trapezoidal-error-integrand-for-ln-antiderivative))))))

(local
 (defthmd trapezoidal-error-integrand-for-ln-antiderivative-notreal-i
     (implies (not (realp i))
              (equal (trapezoidal-error-integrand-for-ln-antiderivative i x)
                     (trapezoidal-error-integrand-for-ln-antiderivative 0 x)))))

(local
 (defthmd trapezoidal-error-integrand-for-ln-antiderivative-works
     (implies (and (realp x)
                   (< 0 x)
                   (standardp x)
                   (standardp i)
                   (realp x1)
                   (< 0 x1)
                   (i-close x x1)
                   (not (= x x1)))
              (equal (standard-part (/ (- (trapezoidal-error-integrand-for-ln-antiderivative i x)
                                          (trapezoidal-error-integrand-for-ln-antiderivative i x1))
                                       (- x x1)))
                     (trapezoidal-error-integrand-for-ln i x)))
   :hints (("Goal"
            :use ((:instance trapezoidal-error-integrand-for-ln-antiderivative-works-eps
                             (eps (- x1 x)))
                  (:instance trapezoidal-error-integrand-for-ln-antiderivative-works-eps
                             (i 0)
                             (eps (- x1 x)))
                  (:instance swap-differential-term
                             (fx (trapezoidal-error-integrand-for-ln-antiderivative I X))
                             (fx1 (trapezoidal-error-integrand-for-ln-antiderivative I X1))
                             (x x)
                             (x1 x1))
                  )
            :in-theory (e/d (trapezoidal-error-integrand-for-ln-antiderivative-notreal-i
                             )
                            (STANDARD-PART-OF-PLUS
                             PREFER-POSITIVE-ADDENDS-EQUAL
                             |(equal (+ (- c) x) y)|
                             trapezoidal-error-integrand-for-ln-antiderivative
                             trapezoidal-error-integrand-for-ln)
                            )))
   ))

;;; Now we use the FTC-2 to show what the integral of the error term is

(defun map-trapezoidal-error-integrand-for-ln (i p)
  (if (consp p)
      (cons (trapezoidal-error-integrand-for-ln i (car p))
            (map-trapezoidal-error-integrand-for-ln i (cdr p)))
      nil))

(local
 (defthm trapezoidal-error-integrand-for-ln-not-real-context
     (implies (not (realp i))
              (equal (trapezoidal-error-integrand-for-ln i x)
                     (trapezoidal-error-integrand-for-ln 0 x)))))

(defthm map-trapezoidal-error-integrand-for-ln-not-real-context
    (implies (not (realp i))
             (equal (map-trapezoidal-error-integrand-for-ln i x)
                    (map-trapezoidal-error-integrand-for-ln 0 x))))

(defun riemann-trapezoidal-error-integrand-for-ln (i p)
  (dotprod (deltas p)
           (map-trapezoidal-error-integrand-for-ln i (cdr p))))

(local
 (defthm riemann-trapezoidal-error-integrand-for-ln-not-real-context
     (implies (not (realp i))
              (equal (riemann-trapezoidal-error-integrand-for-ln i x)
                     (riemann-trapezoidal-error-integrand-for-ln 0 x)))))

(local
 (defthm-std standard-trapezoidal-error-integrand-for-ln
     (implies (and (standardp i)
                   (standardp x))
              (standardp (trapezoidal-error-integrand-for-ln i x)))))

(local
 (defthm limited-trapezoidal-error-integrand-for-ln
     (implies (and (standardp i)
                   (standardp x))
              (i-limited (trapezoidal-error-integrand-for-ln i x)))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (trapezoidal-error-integrand-for-ln i x))))
            :in-theory (disable trapezoidal-error-integrand-for-ln)))
   ))


(local
 (defthm trapezoidal-error-integral-non-positive-x
     (implies (not (and (realp x) (< 0 x)))
              (equal (TRAPEZOIDAL-ERROR-INTEGRAND CONTEXT X)
                     (TRAPEZOIDAL-ERROR-INTEGRAND CONTEXT 1)))))

(local
 (defthm trapezoidal-error-integrand-for-ln-continuous
     (implies (and (standardp x)
                   (standardp context)
                   (realp x)
                   (< 0 x)
                   (i-close x x1)
                   (realp x1)
                   (< 0 x1))
              (i-close (trapezoidal-error-integrand-for-ln context x)
                       (trapezoidal-error-integrand-for-ln context x1)))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    prod-f1*f2-continuous
                    (prod-domain positive-domain)
                    (prod-car-context (lambda (context) context))
                    (prod-cdr-context (lambda (context) context))
                    (prod-f1 trapezoidal-error-integrand)
                    (prod-f2 (lambda (i x) (- (expt (realposfix x) -2))))
                    (prod-f1*f2 trapezoidal-error-integrand-for-ln))
                   (x x)
                   (y x1)))
            :in-theory (e/d (inside-interval-p)
                            (trapezoidal-error-integrand
                             expt))
            )
           ("Subgoal 4"
            :use ((:instance expt-continuous (x x) (x1 y) (n -2))))
           )
   ))

(encapsulate
    nil

    (defthm limited-riemann-trapezoidal-error-integrand-for-ln-antiderivative
     (implies (and (realp a) (standardp a)
		   (realp b) (standardp b)
		   (inside-interval-p a (positive-domain))
		   (inside-interval-p b (positive-domain))
		   (< a b)
                   (standardp i))
	      (i-limited (riemann-trapezoidal-error-integrand-for-ln
                          i (make-small-partition a b))))
     :otf-flg nil
     :hints (("Goal"
	      :use ((:instance
                     (:functional-instance limited-riemann-rcdfn-prime-small-partition
				           (rcdfn-domain positive-domain)
				           (rcdfn
                                            (lambda (context x)
                                              (trapezoidal-error-integrand-for-ln-antiderivative
                                               context
                                               x)))
                                           (rcdfn-prime
                                            (lambda (context x)
                                              (trapezoidal-error-integrand-for-ln
                                               context
                                               x)))
				           (map-rcdfn-prime
                                            (lambda (context p)
                                              (map-trapezoidal-error-integrand-for-ln
                                               context
                                               p)))
				           (riemann-rcdfn-prime
                                            (lambda (context p)
                                              (riemann-trapezoidal-error-integrand-for-ln
                                               context p))))
                     (context i)
                     ))
              :in-theory (e/d (interval-definition-theory)
                              (trapezoidal-error-integrand-for-ln-antiderivative
                               trapezoidal-error-integrand-for-ln
                               OPEN-TRAPEZOIDAL-ERROR-INTEGRAND
                               standard-part-is-standard-implies-close-to-standard-part))
              )
             ("Subgoal 2"
              :use ((:instance
                     trapezoidal-error-integrand-for-ln-antiderivative-works
                     (i context))
                    (:instance
                     standard-part-is-standard-implies-close-to-standard-part
                     (x (* (+ (trapezoidal-error-integrand-for-ln-antiderivative context x)
                              (- (trapezoidal-error-integrand-for-ln-antiderivative context x1)))
                           (/ (+ x (- x1)))))
                     (stdx (TRAPEZOIDAL-ERROR-INTEGRAND-for-ln CONTEXT X)))
                    ))
             ("Subgoal 1"
              :in-theory (enable trapezoidal-error-integrand-for-ln-antiderivative))
             ))

  (local (in-theory (disable riemann-trapezoidal-error-integrand-for-ln)))

  (defun-std strict-int-trapezoidal-error-integrand-for-ln (i a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (positive-domain))
	     (inside-interval-p b (positive-domain))
	     (< a b))
        (standard-part (riemann-trapezoidal-error-integrand-for-ln i (make-small-partition a b)))
        0))
  )

(defun int-trapezoidal-error-integrand-for-ln (i a b)
  (if (<= a b)
      (strict-int-trapezoidal-error-integrand-for-ln i a b)
      (- (strict-int-trapezoidal-error-integrand-for-ln i b a))))

(local
 (defthmd int-trapezoidal-error-integrand-for-ln-computation
     (implies (and (inside-interval-p a (positive-domain))
                   (inside-interval-p b (positive-domain))
                   (realp i))
              (equal (int-trapezoidal-error-integrand-for-ln i a b)
                     (- (trapezoidal-error-integrand-for-ln-antiderivative i b)
                        (trapezoidal-error-integrand-for-ln-antiderivative i a))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance ftc-2
                                         (rcdfn (lambda (context x)
                                                  (trapezoidal-error-integrand-for-ln-antiderivative
                                                   context
                                                   x)))
                                         (rcdfn-prime (lambda (context x)
                                                        (trapezoidal-error-integrand-for-ln
                                                         context
                                                         x)))
                                         (rcdfn-domain positive-domain)
                                         (map-rcdfn-prime (lambda (context p)
                                                            (map-trapezoidal-error-integrand-for-ln
                                                             context
                                                             p)))
                                         (riemann-rcdfn-prime (lambda (context p)
                                                                (riemann-trapezoidal-error-integrand-for-ln
                                                                 context
                                                                 p)))
                                         (strict-int-rcdfn-prime
                                          (lambda (context a b)
                                            (strict-int-trapezoidal-error-integrand-for-ln context a b)))
                                         (int-rcdfn-prime
                                          (lambda (context a b)
                                            (int-trapezoidal-error-integrand-for-ln context a b)))
                                         )
                   (context i)
                   ))
            :in-theory (e/d (interval-definition-theory)
                            (ftc-2
                             trapezoidal-error-integrand-for-ln-antiderivative
                             trapezoidal-error-integrand-for-ln
                             i-close-limited
                             i-close-limited-2)))
           )))

;;; Now let's connect this to the integreal of ln

(local
 (defthmd int-trapezoidal-error-integrand-for-ln-computationa-rhs-lemma
     (implies (and (realp i)
                   (< 0 i))
             (equal (- (trapezoidal-error-integrand-for-ln-antiderivative i (1+
 i))
                       (trapezoidal-error-integrand-for-ln-antiderivative i i))
                    (+ (* 1/2 (1+ (* 2 i)) (acl2-ln (1+ i)))
                       (- (* 1/2 (1+ (* 2 i)) (acl2-ln i)))
                       -1)))
   ))

(local
 (defthmd int-trapezoidal-error-integrand-for-ln-computationa-rhs
     (implies (and (realp i)
                   (< 0 i))
              (equal (+ (int-trapezoidal-error-integrand-for-ln i i (1+ i))
                        (/ (+ (acl2-ln (1+ i)) (acl2-ln i)) 2))
                     (+ (* (1+ i) (acl2-ln (1+ i)))
                        (- (* i (acl2-ln i)))
                        -1)))
   :hints (("Goal"
            :use ((:instance int-trapezoidal-error-integrand-for-ln-computation
                             (a i)
                             (b (1+ i)))
                  (:instance int-trapezoidal-error-integrand-for-ln-computationa-rhs-lemma))
            :in-theory (e/d (inside-interval-p)
                            (int-trapezoidal-error-integrand-for-ln
                             trapezoidal-error-integrand-for-ln-antiderivative))))))

(defun ln-trapezoid-step (i)
  (let ((i (realfix i)))
    (/ (+ (acl2-ln (1+ i)) (acl2-ln i)) 2)))

(defun ln-trapezoid-step-error (i)
  (let ((i (realfix i)))
    (int-trapezoidal-error-integrand-for-ln i i (1+ i))))

(local
 (defthmd int-ln-trapezoid-error-step
     (implies (and (realp i)
                   (< 0 i))
              (equal (int-ln i (1+ i))
                     (+ (ln-trapezoid-step i)
                        (ln-trapezoid-step-error i))))
   :hints (("Goal"
            :use ((:instance int-ln-computation
                             (a i)
                             (b (1+ i)))
                  (:instance
                   int-trapezoidal-error-integrand-for-ln-computationa-rhs))
            :in-theory (e/d (inside-interval-p)
                            (int-trapezoidal-error-integrand-for-ln
                             trapezoidal-error-integrand-for-ln-antiderivative))
            ))))


;;; Now let's get some bounds on this integral. We'll do the easy one
;;; first. The integrand is non-negative, so the integral is non-negative as
;;; well.

(local
 (defun all-xs-in-integer-range-p (i p)
   (if (null p)
       t
       (and (realp i)
            (< 0 i)
            (realp (car p))
            (<= i (car p))
            (<= (car p) (1+ i))
            (all-xs-in-integer-range-p i (cdr p))))))

(local
 (defthm all-xs-in-integer-range-make-partition-rec
     (implies (and (realp i)
                   (< 0 i)
                   (realp ii)
                   (<= i ii)
                   (natp n)
                   (realp delta)
                   (<= 0 delta)
                   (<= (+ ii (* (nfix n) delta)) (1+ i)))
              (all-xs-in-integer-range-p i (make-partition-rec ii delta n)))))

(local
 (defthm all-xs-in-integer-range-make-partition
     (implies (and (realp i)
                   (< 0 i)
                   (natp n))
              (all-xs-in-integer-range-p i (make-partition i (1+ i) n)))
   :hints (("Goal"
            :use ((:instance all-xs-in-integer-range-make-partition-rec
                             (delta (/ n))
                             (ii i)))
            :in-theory (disable all-xs-in-integer-range-make-partition-rec
                                make-partition-rec
                                all-xs-in-integer-range-p)))))

(local
 (defun all-elements-non-negative (p)
   (if (consp p)
       (and (<= 0 (car p))
            (all-elements-non-negative (cdr p)))
       t)))

(local
 (defthmd map-trapezoidal-error-integrand-for-ln-is-non-negative
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p))
              (all-elements-non-negative (map-trapezoidal-error-integrand-for-ln i p)))
   :hints (("Goal"
            :in-theory (disable TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN)))
   ))

(local
 (defthmd map-trapezoidal-error-integrand-for-ln-is-real
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p))
              (real-listp (map-trapezoidal-error-integrand-for-ln i p)))
   :hints (("Goal"
            :in-theory (disable TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN)))
   ))

(local
 (defthmd dotprod-non-negative-elements
     (implies (and (all-elements-non-negative xs)
                   (all-elements-non-negative ys)
                   (real-listp xs)
                   (real-listp ys))
              (<= 0 (dotprod xs ys)))))

(local
 (defun increasing-p (xs)
   (if (endp xs)
       t
       (if (endp (cdr xs))
           t
           (and (<= (car xs) (cadr xs))
                (increasing-p (cdr xs)))))))

(local
 (defthmd all-elements-non-negative-deltas
     (implies (and (increasing-p xs)
                   (real-listp xs))
              (all-elements-non-negative (deltas xs)))
   :hints (("Goal"
            :in-theory (enable deltas)))
   ))

(local
 (defthm real-listp-deltas
     (implies (real-listp xs)
              (real-listp (deltas xs)))
   :hints (("Goal"
            :in-theory (enable deltas)))
   ))

(local
 (defthmd increasing-make-partition-rec
     (implies (and (realp delta)
                   (<= 0 delta)
                   (realp a))
              (increasing-p (make-partition-rec a delta n)))
   :instructions
   (:induct (:change-goal nil t)
            :bash :pro (:casesplit (= n 1))
            :bash (:demote 2)
            (:dv 1)
            (:dv 1)
            :s :up
            (:= (increasing-p (make-partition-rec (+ a delta)
                                                  delta (+ -1 n))))
            :up :pro (:dv 1)
            :x (:dv 2)
            (:= (cons (+ a delta)
                      (make-partition-rec (+ a (* 2 delta))
                                          delta (+ -2 n))))
            :up
            :up :bash))
 )

(local
 (defthmd increasing-make-partition
     (implies (and (realp a)
                   (realp b)
                   (< a b)
                   (natp n))
              (increasing-p (make-partition a b n)))
   :hints (("Goal"
            :use ((:instance increasing-make-partition-rec
                             (delta (/ (- b a) n)))
                  )
            :in-theory (e/d (make-partition)
                            (make-partition-rec))))))

(local
 (defthmd real-listp-make-partition-rec
     (implies (and (realp delta)
                   (<= 0 delta)
                   (realp a))
              (real-listp (make-partition-rec a delta n)))
   ))

(local
 (defthm dotprod-xs-nil
     (equal (dotprod xs nil) 0)))

(local
 (defthmd riemann-trapezoidal-error-integrand-for-ln-is-non-negative
     (implies (and (realp i)
                   (< 0 i)
                   (real-listp p)
                   (increasing-p p)
                   (all-elements-non-negative p)
                   (all-xs-in-integer-range-p i p))
              (<= 0 (riemann-trapezoidal-error-integrand-for-ln i p)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance dotprod-non-negative-elements
                             (xs (deltas p))
                             (ys (MAP-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN I (CDR P))))
                  (:instance all-elements-non-negative-deltas
                             (xs p))
                  (:instance map-trapezoidal-error-integrand-for-ln-is-non-negative
                             (p (cdr p)))
                  )
            :in-theory (disable TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                                deltas
                                dotprod
                                )))
   ))

(local
 (defthm make-partition-i-i+1
     (implies (realp i)
              (equal (MAKE-PARTITION I (+ 1 I)
                                     (I-LARGE-INTEGER))
                     (make-partition-rec i (/ (I-LARGE-INTEGER))
                                         (I-LARGE-INTEGER))))))

(local
 (defthmd all-elements-non-negative-make-partition
     (implies (and (realp i)
                   (<= 0 i)
                   (realp delta)
                   (<= 0 delta))
              (all-elements-non-negative (make-partition-rec i delta n)))))


(local
 (defthmd riemann-trapezoidal-error-integrand-for-ln-of-make-partition-is-non-negative
     (implies (and (realp i)
                   (< 0 i))
              (<= 0 (riemann-trapezoidal-error-integrand-for-ln i (make-small-partition i (1+ i)))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance riemann-trapezoidal-error-integrand-for-ln-is-non-negative
                             (p (make-small-partition i (1+ i))))
                  (:instance real-listp-make-partition-rec
                             (a i)
                             (delta (/ (i-large-integer)))
                             (n (i-large-integer)))
                  (:instance increasing-make-partition-rec
                             (a i)
                             (delta (/ (i-large-integer)))
                             (n (i-large-integer)))
                  (:instance all-xs-in-integer-range-make-partition
                             (n (i-large-integer)))
                  (:instance all-elements-non-negative-make-partition
                             (delta (/ (i-large-integer)))
                             (n (i-large-integer)))
                  )
            :in-theory (e/d (make-small-partition
                             make-partition)
                            (TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                             riemann-trapezoidal-error-integrand-for-ln
                             make-partition)
                            ))
           )))

(local
 (defthm realp-dotprod
     (implies (and (real-listp xs)
                   (real-listp ys))
              (realp (dotprod xs ys)))))

(local
 (defthm realp-riemann-trapezoidal-error-integrand-for-ln
     (implies (and (realp i)
                   (< 0 I)
                   (real-listp p))
              (REALP (RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN i p)))
   ))


(local
 (defthm-std int-trapezoidal-error-integrand-for-ln-of-make-partition-is-non-negative
     (implies (and (realp i)
                   (< 0 i))
              (<= 0 (int-trapezoidal-error-integrand-for-ln i i (1+ i))))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance
                   riemann-trapezoidal-error-integrand-for-ln-of-make-partition-is-non-negative)
                  (:instance STANDARD-PART-<=
                             (x 0)
                             (y (RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                                 I (MAKE-SMALL-PARTITION i (1+ i)))))
                  )
            :in-theory (e/d (strict-int-trapezoidal-error-integrand-for-ln
                             int-trapezoidal-error-integrand-for-ln)
                            (riemann-trapezoidal-error-integrand-for-ln
                             RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN)))))
 )

;;; Now that we have a lower bound for the integral, let's find an upper bound

(defun trapezoidal-error-integrand-for-ln-alt (i x)
  (let ((i (realfix i))
        (x (realposfix x)))
    (* (- (trapezoidal-error-integrand i x))
       (/ (expt x 2)))))

(local
 (defthmd
     trapezoidal-error-integrand-for-ln-alt>-trapezoidal-error-integrand-for-ln
     (equal (trapezoidal-error-integrand-for-ln-alt i x)
            (trapezoidal-error-integrand-for-ln i x))))

(local
 (defthmd ln-2nd-deriv-decreasing
     (implies (and (realp x1)
                   (< 0 x1)
                   (realp x2)
                   (<= x1 x2))
              (<= (expt x2 -2)
                  (expt x1 -2)))
   ))

(local
 (defthmd upper-bound-for-ln-2nd-deriv-lemma
     (implies (and (realp i)
                   (< 0 i)
                   (realp x)
                   (<= i x)
                   (<= x (1+ i)))
              (<= (expt x -2)
                  (expt i -2)))
   ))

(local
 (defthmd lower-bound-for-ln-2nd-deriv-lemma
     (implies (and (realp i)
                   (< 0 i)
                   (realp x)
                   (<= i x)
                   (<= x (1+ i)))
              (<= (expt (1+ i) -2)
                  (expt x -2)))
   :hints (("Goal"
            :use ((:instance ln-2nd-deriv-decreasing
                             (x1 x)
                             (x2 (1+ i))))))
   ))

(local
 (defthmd upper-bound-for-ln-2nd-deriv
     (implies (and (realp i)
                   (< 0 i)
                   (realp x)
                   (<= i x)
                   (<= x (1+ i))
                   )
              (<= (trapezoidal-error-integrand-for-ln i x)
                  (* (- (trapezoidal-error-integrand i x))
                     (expt i -2))))
   :hints (("Goal"
            :use ((:instance
                   trapezoidal-error-integrand-for-ln-alt>-trapezoidal-error-integrand-for-ln)
                  (:instance upper-bound-for-ln-2nd-deriv-lemma))
            :in-theory (disable trapezoidal-error-integrand)))
   ))

(local
 (defthmd lower-bound-for-ln-2nd-deriv
     (implies (and (realp i)
                   (< 0 i)
                   (realp x)
                   (<= i x)
                   (<= x (1+ i))
                   )
              (<= (* (- (trapezoidal-error-integrand i x))
                     (expt (1+ i) -2))
                  (trapezoidal-error-integrand-for-ln i x)))
   :hints (("Goal"
            :use ((:instance
                   trapezoidal-error-integrand-for-ln-alt>-trapezoidal-error-integrand-for-ln)
                  (:instance lower-bound-for-ln-2nd-deriv-lemma))
            :in-theory (disable trapezoidal-error-integrand)))
   ))

(local
 (defun pairwise-<= (xs ys)
   (if (endp xs)
       (and (= xs nil)
            (= ys nil))
       (and (<= (car xs) (car ys))
            (pairwise-<= (cdr xs) (cdr ys))))))

(local
 (defun scale-list (k xs)
   (if (endp xs)
       nil
       (cons (* k (car xs))
             (scale-list k (cdr xs))))))

(local
 (defun all-elements-in-unit-range (i p)
   (if (consp p)
       (and (realp (car p))
            (<= i (car p))
            (<= (car p) (1+ i))
            (all-elements-in-unit-range i (cdr p)))
       (eq p nil))))


(local
 (defthmd map-times-pairwise-<=
     (implies (and (all-elements-non-negative xs)
                   (pairwise-<= ys1 ys2)
                   (real-listp xs)
                   (real-listp ys1)
                   (real-listp ys2))
              (pairwise-<= (map-times xs ys1)
                           (map-times xs ys2)))
   :INSTRUCTIONS (:INDUCT :BASH :PRO (:FORWARDCHAIN 2)
                          (:DV 1)
                          :X
                          (:= (CONS (* (CAR XS) (CAR YS1))
                                    (MAP-TIMES (CDR XS) (CDR YS1))))
                          :NX :X
                          (:= (CONS (* (CAR XS) (CAR YS2))
                                    (MAP-TIMES (CDR XS) (CDR YS2))))
                          :UP :X-DUMB
                          (:= (<= (* (CAR XS) (CAR YS1))
                                  (* (CAR XS) (CAR YS2))))
                          (:CLAIM (<= 0 (CAR XS)))
                          (:CASESPLIT (= 0 (CAR XS)))
                          :BASH :BASH)))

(local
 (defthmd real-listp-if-all-xs-in-integer-range-p
     (implies (all-xs-in-integer-range-p i p)
              (real-listp p))))

(local
 (defthmd map-trapezoidal-error-integrand-for-ln-upper-bound-1
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p)
                   (real-listp p)
                   )
              (pairwise-<= (map-trapezoidal-error-integrand-for-ln i p)
                           (scale-list (expt i -2)
                                       (scale-list -1 (map-trapezoidal-error-integrand i p)))))
   :hints (("Goal"
            :in-theory (disable trapezoidal-error-integrand-for-ln
                                trapezoidal-error-integrand))
           ("Subgoal *1/3"
            :use ((:instance upper-bound-for-ln-2nd-deriv
                             (x (car p)))))
           )
   ))

(local
 (defthmd map-trapezoidal-error-integrand-for-ln-lower-bound-1
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p)
                   (real-listp p)
                   )
              (pairwise-<= (scale-list (expt (1+ i) -2)
                                       (scale-list -1 (map-trapezoidal-error-integrand i p)))
                           (map-trapezoidal-error-integrand-for-ln i p)))
   :hints (("Goal"
            :in-theory (disable trapezoidal-error-integrand-for-ln
                                trapezoidal-error-integrand))
           ("Subgoal *1/3"
            :use ((:instance lower-bound-for-ln-2nd-deriv
                             (x (car p)))))
           )
   ))

(local
 (defthmd map-trapezoidal-error-integrand-for-ln-upper-bound-2
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p)
                   )
              (pairwise-<= (map-trapezoidal-error-integrand-for-ln i p)
                           (scale-list (expt i -2)
                                       (scale-list -1 (map-trapezoidal-error-integrand i p)))))
   :hints (("Goal"
            :use ((:instance
                   map-trapezoidal-error-integrand-for-ln-upper-bound-1)
                  (:instance real-listp-if-all-xs-in-integer-range-p))
            :in-theory (disable trapezoidal-error-integrand-for-ln
                                trapezoidal-error-integrand))
           )
   ))

(local
 (defthmd map-trapezoidal-error-integrand-for-ln-lower-bound-2
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p)
                   )
              (pairwise-<= (scale-list (expt (1+ i) -2)
                                       (scale-list -1 (map-trapezoidal-error-integrand i p)))
                           (map-trapezoidal-error-integrand-for-ln i p)))
   :hints (("Goal"
            :use ((:instance
                   map-trapezoidal-error-integrand-for-ln-lower-bound-1)
                  (:instance real-listp-if-all-xs-in-integer-range-p))
            :in-theory (disable trapezoidal-error-integrand-for-ln
                                trapezoidal-error-integrand))
           )
   ))

(local
 (defthm sumlist-scale
     (implies (and (real-listp xs)
                   (realp k))
              (equal (sumlist (scale-list k xs))
                     (* k (sumlist xs))))))

(local
 (defthm map-times-scale-2
     (implies (and (real-listp xs)
                   (real-listp ys)
                   (realp k))
              (equal (map-times xs (scale-list k ys))
                     (scale-list k (map-times xs ys))))
   :hints (("Goal"
            :induct (map-times xs ys)))))

(local
 (defthm pairwise-<=-sumlist
     (implies (pairwise-<= xs ys)
              (<= (sumlist xs)
                  (sumlist ys)))))

(local
 (defthm real-listp-scale
     (implies (and (realp k)
                   (real-listp xs))
              (real-listp (scale-list k xs)))))

(local
 (defthm map-trapezoidal-eror-integrand-nil
     (equal (map-trapezoidal-error-integrand i nil)
            nil)))

(local
 (defthm map-trapezoidal-eror-integrand-for-ln-nil
     (equal (map-trapezoidal-error-integrand-for-ln i nil)
            nil)))

(local
 (defthm real-listp-map-trapezoidal-error-integrand
     (implies (and (realp i)
                   (real-listp p))
              (real-listp (map-trapezoidal-error-integrand i p)))))

(local
 (defthm real-listp-map-trapezoidal-error-integrand-for-ln
     (implies (and (realp i)
                   (real-listp p))
              (real-listp (map-trapezoidal-error-integrand-for-ln i p)))))

(local
 (defthm deltas-singleton
     (implies (not (cdr xs))
              (equal (deltas xs) nil))))

(local
 (defthm real-listp-map-times
     (implies (and (real-listp xs)
                   (real-listp ys))
              (real-listp (map-times xs ys)))))

(local
 (defthmd riemann-trapezoidal-error-integrand-for-ln-upper-bound-lemma
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p)
                   (increasing-p p)
                   (real-listp p)
                   )
              (<= (riemann-trapezoidal-error-integrand-for-ln i p)
                  (* (expt i -2)
                     -1 (riemann-trapezoidal-error-integrand i p))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance pairwise-<=-sumlist
                             (xs (MAP-TIMES (DELTAS p)
                                            (MAP-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                                             I (CDR P))))
                             (ys (MAP-TIMES (DELTAS p)
                                            (scale-list (expt i -2)
                                                        (scale-list -1
                                                                    (map-trapezoidal-error-integrand i (cdr p)))))))
                  (:instance
                   map-trapezoidal-error-integrand-for-ln-upper-bound-2
                   (p (cdr p)))
                  (:instance map-times-pairwise-<=
                             (xs (deltas p))
                             (ys1 (MAP-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN I (cdr P)))
                             (ys2 (SCALE-LIST (EXPT I -2)
                                              (SCALE-LIST -1
                                                          (MAP-TRAPEZOIDAL-ERROR-INTEGRAND I (CDR P))))))
                  (:instance all-elements-non-negative-deltas
                             (xs p)
                             )
                  )
            :in-theory (disable map-trapezoidal-error-integrand-for-ln
                                map-trapezoidal-error-integrand
                                deltas
                                map-times
                                sumlist
                                pairwise-<=
                                pairwise-<=-sumlist)))))

(local
 (defthmd riemann-trapezoidal-error-integrand-for-ln-lower-bound-lemma
     (implies (and (realp i)
                   (< 0 i)
                   (all-xs-in-integer-range-p i p)
                   (increasing-p p)
                   (real-listp p)
                   )
              (<= (* (expt (1+ i) -2)
                     -1 (riemann-trapezoidal-error-integrand i p))
                  (riemann-trapezoidal-error-integrand-for-ln i p)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance pairwise-<=-sumlist
                             (ys (MAP-TIMES (DELTAS p)
                                            (MAP-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                                             I (CDR P))))
                             (xs (MAP-TIMES (DELTAS p)
                                            (scale-list (expt (1+ i) -2)
                                                        (scale-list -1
                                                                    (map-trapezoidal-error-integrand i (cdr p)))))))
                  (:instance
                   map-trapezoidal-error-integrand-for-ln-lower-bound-2
                   (p (cdr p)))
                  (:instance map-times-pairwise-<=
                             (xs (deltas p))
                             (ys2 (MAP-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN I (cdr P)))
                             (ys1 (SCALE-LIST (EXPT (1+ I) -2)
                                              (SCALE-LIST -1
                                                          (MAP-TRAPEZOIDAL-ERROR-INTEGRAND I (CDR P))))))
                  (:instance all-elements-non-negative-deltas
                             (xs p)
                             )
                  )
            :in-theory (disable map-trapezoidal-error-integrand-for-ln
                                map-trapezoidal-error-integrand
                                deltas
                                map-times
                                sumlist
                                pairwise-<=
                                pairwise-<=-sumlist)))))

(local
 (defthmd riemann-trapezoidal-error-integrand-for-ln-upper-bound
     (implies (and (realp i)
                   (< 0 i)
                   )
              (<= (riemann-trapezoidal-error-integrand-for-ln i (make-small-partition i (1+ i)))
                  (* (expt i -2)
                     -1 (riemann-trapezoidal-error-integrand i (make-small-partition i (1+ i))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance
                   riemann-trapezoidal-error-integrand-for-ln-upper-bound-lemma
                   (p (make-small-partition i (1+ i))))
                  (:instance all-xs-in-integer-range-make-partition
                             (n (i-large-integer)))
                  (:instance increasing-make-partition
                             (a i)
                             (b (1+ i))
                             (n (i-large-integer)))
                  (:instance real-listp-make-partition-rec
                             (a i)
                             (delta (/ (i-large-integer)))
                             (n (i-large-integer)))
                  )
            :in-theory (e/d (make-small-partition)
                            (riemann-trapezoidal-error-integrand-for-ln
                             riemann-trapezoidal-error-integrand))))))

(local
 (defthmd riemann-trapezoidal-error-integrand-for-ln-lower-bound
     (implies (and (realp i)
                   (< 0 i)
                   )
              (<= (* (expt (1+ i) -2)
                     -1 (riemann-trapezoidal-error-integrand i (make-small-partition i (1+ i))))
                  (riemann-trapezoidal-error-integrand-for-ln i (make-small-partition i (1+ i)))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance
                   riemann-trapezoidal-error-integrand-for-ln-lower-bound-lemma
                   (p (make-small-partition i (1+ i))))
                  (:instance all-xs-in-integer-range-make-partition
                             (n (i-large-integer)))
                  (:instance increasing-make-partition
                             (a i)
                             (b (1+ i))
                             (n (i-large-integer)))
                  (:instance real-listp-make-partition-rec
                             (a i)
                             (delta (/ (i-large-integer)))
                             (n (i-large-integer)))
                  )
            :in-theory (e/d (make-small-partition)
                            (riemann-trapezoidal-error-integrand-for-ln
                             riemann-trapezoidal-error-integrand))))))

(local
 (defthm real-riemann-trapezoidal-error-integrand
     (implies (and (realp i)
                   (real-listp p))
              (realp (riemann-trapezoidal-error-integrand i p)))))

(local
 (defthm-std strict-int-trapezoidal-error-integrand-for-ln-upper-bound
     (implies (and (realp i)
                   (< 0 i)
                   )
              (<= (strict-int-trapezoidal-error-integrand-for-ln i i (1+ i))
                  (* (expt i -2)
                     -1 (strict-int-trapezoidal-error-integrand i i (1+ i)))))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance
                   riemann-trapezoidal-error-integrand-for-ln-upper-bound)
                  (:instance standard-part-<=
                             (x (RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                                 I (MAKE-SMALL-PARTITION I (+ 1 I))))
                             (y (- (* (EXPT I -2)
                                      (RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND
                                       I (MAKE-SMALL-PARTITION I (+ 1 I)))))))
                  )
            :in-theory (disable RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND
                                RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-for-ln
                                standard-part-<=
                                )
            ))
   ))

(local
 (defthm-std strict-int-trapezoidal-error-integrand-for-ln-lower-bound
     (implies (and (realp i)
                   (< 0 i)
                   )
              (<= (* (expt (1+ i) -2)
                     -1 (strict-int-trapezoidal-error-integrand i i (1+ i)))
                  (strict-int-trapezoidal-error-integrand-for-ln i i (1+ i))))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance
                   riemann-trapezoidal-error-integrand-for-ln-lower-bound)
                  (:instance standard-part-<=
                             (y (RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                                 I (MAKE-SMALL-PARTITION I (+ 1 I))))
                             (x (- (* (EXPT (1+ I) -2)
                                      (RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND
                                       I (MAKE-SMALL-PARTITION I (+ 1 I)))))))
                  )
            :in-theory (disable RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND
                                RIEMANN-TRAPEZOIDAL-ERROR-INTEGRAND-for-ln
                                standard-part-<=
                                )
            ))
   ))

(local
 (defthm-std int-trapezoidal-error-integrand-for-ln-upper-bound-lemma
     (implies (and (realp i)
                   (< 0 i)
                   )
              (<= (int-trapezoidal-error-integrand-for-ln i i (1+ i))
                  (* (expt i -2)
                     -1 (int-trapezoidal-error-integrand i i (1+ i)))))
   :hints (("Goal"
            :use ((:instance
                   strict-int-trapezoidal-error-integrand-for-ln-upper-bound))
            :in-theory (e/d (int-trapezoidal-error-integrand
                             int-trapezoidal-error-integrand-for-ln)
                            (strict-int-trapezoidal-error-integrand
                             strict-int-trapezoidal-error-integrand-for-ln))

            ))
   ))

(local
 (defthm-std int-trapezoidal-error-integrand-for-ln-lower-bound-lemma
     (implies (and (realp i)
                   (< 0 i)
                   )
              (<= (* (expt (1+ i) -2)
                     -1 (int-trapezoidal-error-integrand i i (1+ i)))
                  (int-trapezoidal-error-integrand-for-ln i i (1+ i))))
   :hints (("Goal"
            :use ((:instance
                   strict-int-trapezoidal-error-integrand-for-ln-lower-bound))
            :in-theory (e/d (int-trapezoidal-error-integrand
                             int-trapezoidal-error-integrand-for-ln)
                            (strict-int-trapezoidal-error-integrand
                             strict-int-trapezoidal-error-integrand-for-ln))

            ))
   ))

(defthm int-trapezoidal-error-integrand-for-ln-upper-bound
    (implies (posp i)
             (<= (int-trapezoidal-error-integrand-for-ln i i (1+ i))
                 (* 1/12 (expt i -2))))
  :hints (("Goal"
           :use ((:instance
                  int-trapezoidal-error-integrand-for-ln-upper-bound-lemma)
                 (:instance int-trapezoidal-error-integrand-i-to-i+1)))))

(defthm int-trapezoidal-error-integrand-for-ln-lower-bound
    (implies (posp i)
             (<= (* 1/12 (expt (1+ i) -2))
                 (int-trapezoidal-error-integrand-for-ln i i (1+ i))))
  :hints (("Goal"
           :use ((:instance
                  int-trapezoidal-error-integrand-for-ln-lower-bound-lemma)
                 (:instance int-trapezoidal-error-integrand-i-to-i+1)))))

;;; Now we can lift this to a region from 1 to n instead of i to i+1

(defun ln-trapezoid-approximation (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (ln-trapezoid-step i)
         (ln-trapezoid-approximation (1+ i) n))
      ))

(defun ln-trapezoid-approximation-error (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (ln-trapezoid-step-error i)
         (ln-trapezoid-approximation-error (1+ i) n))
      ))

(defun sum-int-ln (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (int-ln i (1+ i))
         (sum-int-ln (1+ i) n))
      ))

(local
 (defun fix-acl2-ln (x)
   (let ((x (realposfix x)))
     (acl2-ln x))))

(local
 (defthmd fix-acl2-ln-for-valid-args
     (implies (and (realp x)
                   (< 0 x))
              (equal (fix-acl2-ln x)
                     (acl2-ln x)))))

(local
 (defun map-fix-acl2-ln (i p)
   (declare (ignorable i))
   (if (consp p)
       (cons (fix-acl2-ln (car p))
             (map-fix-acl2-ln i (cdr p)))
       nil)))

(local
 (defun all-elements-are-positive (p)
   (if (consp p)
       (and (realp (car p))
            (< 0 (car p))
            (all-elements-are-positive (cdr p)))
       t)))

(local
 (defthmd map-fix-acl2-ln-for-valid-args
     (equal (map-fix-acl2-ln i x)
            (map-ln x))))

(local
 (defun riemann-fix-ln (i p)
   (dotprod (deltas p)
            (map-fix-acl2-ln i (cdr p)))))

(local
 (defthmd riemann-fix-acl2-ln-for-valid-args
     (implies (all-elements-are-positive p)
              (equal (riemann-fix-ln i p)
                     (riemann-ln p)))
  :INSTRUCTIONS (:PRO (:DV 1)
                      :X-DUMB
                      (:= (DOTPROD (DELTAS P)
                                   (MAP-FIX-ACL2-LN I (CDR P))))
                      (:DV 2)
                      (:REWRITE MAP-FIX-ACL2-LN-FOR-VALID-ARGS)
                      :TOP (:DV 2)
                      :X-DUMB (:= (DOTPROD (DELTAS P) (MAP-LN (CDR P))))
                      :TOP :S)
  ))

(local
 (defthm all-elements-positive-make-partition-rec
     (implies (and (realp a)
                   (< 0 a)
                   (realp delta)
                   (< 0 delta)
                   (natp n))
              (all-elements-are-positive (make-partition-rec a delta n)))))

(local
 (defthm all-elements-positive-make-partition
     (implies (and (realp a)
                   (< 0 a)
                   (realp b)
                   (< a b)
                   (posp n))
              (all-elements-are-positive (make-partition a b n)))
   :hints (("Goal"
            :use ((:instance all-elements-positive-make-partition-rec
                             (delta (/ (- b a) n)))
                  )
            :in-theory (disable make-partition-rec)))
   ))

(local
 (defthm all-elements-positive-make-small-partition
     (implies (and (realp a)
                   (< 0 a)
                   (realp b)
                   (< a b))
              (all-elements-are-positive (make-small-partition a b)))
   :hints (("Goal"
            :use ((:instance all-elements-positive-make-partition
                             (n (i-large-integer)))
                  )
            :in-theory (e/d (make-small-partition)
                            (make-partition))))
   ))



(local
 (encapsulate
     () ;; start lemmas for sum-int-ln-=-int-ln-lemma

     (local (in-theory (disable MAP-FIX-ACL2-LN
                                MAP-LN
                                RIEMANN-FIX-LN
                                RIEMANN-LN
                                )))

   (local
    (defthm lemma-1
        (implies (and (realp a)
                      (realp b)
                      (standardp a)
                      (standardp b)
                      (< a b))
                 (acl2-numberp (car (map-fix-acl2-ln context
                                                     (cdr (make-small-partition
                                                           a b))))))
      :instructions
      (:pro (:dv 1)
            (:dv 1)
            (:dv 2)
            (:dv 1)
            :x :x (:dv 2)
            :x
            (:= (cons (+ a (- (* (/ (i-large-integer)) a))
                         (* (/ (i-large-integer)) b))
                      (make-partition-rec (+ a (* 2 (/ (i-large-integer)) b)
                                             (* -2 (/ (i-large-integer)) a))
                                          (+ (- (* (/ (i-large-integer)) a))
                                             (* (/ (i-large-integer)) b))
                                          (+ -2 (i-large-integer)))))
            :up
            :up :s
            :up :x
            :up :s
            :up :s)))

   (local
    (defthm lemma-2
        (implies (and (realp a)
                      (realp b)
                      (standardp a)
                      (standardp b)
                      (< a b))
                 (acl2-numberp (car (map-ln (cdr (make-small-partition a b))))))
      :instructions
      (:pro (:dv 1)
            (:dv 1)
            (:dv 1)
            (:dv 1)
            :x :x (:dv 2)
            :x
            (:= (cons (+ a (- (* (/ (i-large-integer)) a))
                         (* (/ (i-large-integer)) b))
                      (make-partition-rec (+ a (* 2 (/ (i-large-integer)) b)
                                             (* -2 (/ (i-large-integer)) a))
                                          (+ (- (* (/ (i-large-integer)) a))
                                             (* (/ (i-large-integer)) b))
                                          (+ -2 (i-large-integer)))))
            :up
            :up :s
            :up :x
            :up :s
            :up :s)))

   (local
    (defthm lemma-3
        (implies (and (realp a)
                      (< 0 a)
                      (realp b)
                      (< a b))
                 (equal (MAP-FIX-ACL2-LN CONTEXT
                                         (CDR (MAKE-SMALL-PARTITION A B)))
                        (MAP-LN (CDR (MAKE-SMALL-PARTITION A B)))))
      :hints (("Goal"
               :in-theory (enable MAP-FIX-ACL2-LN-FOR-VALID-ARGS)))
      ))


   (local
    (defthm-std lemma-4
        (implies (and (realp a)
                      (< 0 a))
                 (equal (int-ln a a) 0))))

   (local
    (defthm lemma-5
        (implies
         (and (standardp context)
              (standardp a)
              (standardp b)
              (realp a)
              (realp b)
              (< 0 a)
              (< 0 b)
              (< a b))
         (equal (standard-part (riemann-fix-ln context (make-small-partition a b)))
                (standard-part (riemann-ln (make-small-partition a b)))))
      :instructions (:pro (:dv 1)
                          (:dv 1)
                          (:rewrite riemann-fix-acl2-ln-for-valid-args)
                          :top
                          :s :bash)))

   (local
    (defthm lemma-6
        (implies
         (and (standardp context)
              (standardp a)
              (standardp b)
              (inside-interval-p a '((0)))
              (inside-interval-p b '((0)))
              (< a b))
         (equal
          (standard-part (riemann-fix-ln context (make-small-partition a b)))
          (standard-part (riemann-ln (make-small-partition a b)))))
      :instructions (:pro (:dv 1)
                          (:dv 1)
                          (:rewrite riemann-fix-acl2-ln-for-valid-args)
                          :top :s (:demote 4)
                          (:dv 1)
                          :x :top
                          :pro :bash)))

   (local
    (defthm lemma-7
        (implies (not (consp p))
                 (equal (riemann-fix-ln context p) 0))
      :hints (("Goal"
               :in-theory (enable riemann-fix-ln)))
      ))

   (local
    (defthmd lemma-8
        (equal (map-fix-acl2-ln context p)
               (and (consp p)
                    (cons (acl2-ln (realposfix (car p)))
                          (map-fix-acl2-ln context (cdr p)))))
      :instructions ((:dv 1) :x :top :s)))

   (local
    (defthm lemma-9
        (equal (riemann-fix-ln context p)
               (sumlist (map-times (deltas p)
                                   (map-fix-acl2-ln context (cdr p)))))
      :instructions ((:dv 1) :x :nx :top :s)))

   (local
    (defthm lemma-10
        (implies
         (and (standardp context)
              (standardp a)
              (standardp b))
         (equal
          (strict-int-ln a b)
          (if (and (realp a)
                   (realp b)
                   (inside-interval-p a '((0)))
                   (inside-interval-p b '((0)))
                   (< a b))
              (standard-part (riemann-fix-ln context (make-small-partition a b)))
              0)))
      :instructions (:pro (:dv 1)
                          (:rewrite strict-int-ln)
                          :nx (:dv 2)
                          (:dv 1)
                          (:rewrite riemann-fix-acl2-ln-for-valid-args)
                          :top :s
                          (:rewrite all-elements-positive-make-small-partition)
                          (:in-theory (enable inside-interval-p))
                          :bash)))

   (defthmd sum-int-ln-=-int-ln-lemma
       (implies (and (posp a)
                     (posp b)
                     (<= a b))
                (equal (sum-int-ln a b)
                       (int-ln a b)))
     :otf-flg nil
     :hints (("Goal"
              :do-not-induct t
              :induct (sum-int-ln a b)
              :in-theory (e/d (inside-interval-p)
                              (int-ln))
              )
             ("Subgoal *1/2"
              :use ((:instance
                     (:functional-instance split-rcfn-integral-by-subintervals
                                           (rcfn (lambda (i x)
                                                   (fix-acl2-ln x)))
                                           (map-rcfn map-fix-acl2-ln)
                                           (riemann-rcfn riemann-fix-ln)
                                           (strict-int-rcfn
                                            (lambda (i a b)
                                              (strict-int-ln a b)))
                                           (int-rcfn
                                            (lambda (i a b)
                                              (int-ln a b)))
                                           (rcfn-domain positive-domain))
                     (a a)
                     (b b)
                     (c (1+ a)))))
             ("Subgoal *1/2.5"
              :in-theory (disable strict-int-ln))
             ("Subgoal *1/2.4"
              :by lemma-10)
             ("Subgoal *1/2.2"
              :by lemma-8)
             ))
   )
)


(local
 (defthmd int-ln-trapezoid-approximation-lemma
     (implies (and (posp i)
                   (posp n))
              (equal (sum-int-ln i n)
                     (+ (ln-trapezoid-approximation i n)
                        (ln-trapezoid-approximation-error i n))))
   :hints (("Goal"
            :induct (sum-int-ln i n)
            :in-theory (disable int-ln
                                LN-TRAPEZOID-STEP
                                LN-TRAPEZOID-STEP-ERROR
                                ))
           ("Subgoal *1/2"
            :use ((:instance int-ln-trapezoid-error-step)))
           )))


(local
 (defthm ln-trapezoid-approximation-as-sum-ln-lemma
     (implies (and (posp i)
                   (posp n)
                   (< i n))
              (equal (ln-trapezoid-approximation i n)
                     (+ (* -1/2 (acl2-ln i))
                        (sum-ln i n)
                        (* -1/2 (acl2-ln n)))))
   :rule-classes nil
   :instructions ((:induct (ln-trapezoid-approximation i n))
                  (:change-goal nil t)
                  :bash (:casesplit (= (+ 1 i) n))
                  :bash :pro (:forwardchain 2)
                  (:dv 1)
                  :x (:dv 3)
                  :=
                  :up (:= (+ (sum-ln (+ 1 i) n)
                             (* -1/2 (acl2-ln n))))
                  :top :bash)
   ))

(local
 (defthm int-ln-trapezoid-approximation-lemma-for-1-to-n
     (implies (and (integerp n)
                   (< 1 n))
              (equal (int-ln 1 n)
                     (+ (sum-ln 1 n)
                        (* -1/2 (acl2-ln n))
                        (ln-trapezoid-approximation-error 1 n))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance sum-int-ln-=-int-ln-lemma
                             (a 1)
                             (b n))
                  (:instance ln-trapezoid-approximation-as-sum-ln-lemma
                             (i 1)
                             (n n))
                  (:instance int-ln-trapezoid-approximation-lemma
                             (i 1)
                             (n n))
                  )
            :in-theory (disable int-ln
                                sum-ln
                                ln-trapezoid-approximation
                                ln-trapezoid-approximation-error)
            ))
   ))

(local
 (defthm ln-factorial-as-stirling-term-lemma-1
     (implies (and (integerp n)
                   (< 1 n))
              (equal (acl2-ln (factorial n))
                     (+ (int-ln 1 n)
                        (* 1/2 (acl2-ln n))
                        (- (ln-trapezoid-approximation-error 1 n)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance int-ln-trapezoid-approximation-lemma-for-1-to-n)
                  (:instance ln-factorial)
                  )
            :in-theory (disable int-ln
                                sum-ln
                                ln-trapezoid-approximation-error)))))

(local
 (defthm ln-factorial-as-stirling-term-lemma-2
     (implies (and (integerp n)
                   (< 1 n))
              (equal (acl2-ln (factorial n))
                     (+ (* n (acl2-ln n))
                        (- n)
                        1
                        (* 1/2 (acl2-ln n))
                        (- (ln-trapezoid-approximation-error 1 n)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance ln-factorial-as-stirling-term-lemma-1)
                  (:instance int-ln-computation
                             (a 1)
                             (b n))
                  )
            :in-theory (e/d (inside-interval-p)
                            (int-ln
                             sum-ln
                             ln-trapezoid-approximation-error))))))

(local
 (defthm ln-factorial-as-stirling-term-lemma
     (implies (and (integerp n)
                   (< 1 n))
              (equal (acl2-ln (factorial n))
                     (+ (acl2-ln (expt n n))
                        (- n)
                        (acl2-ln (acl2-sqrt n))
                        (- 1 (ln-trapezoid-approximation-error 1 n)))))
   :rule-classes nil
   :instructions ((:use (:instance ln-factorial-as-stirling-term-lemma-2))
                  :pro (:forwardchain 1)
                  (:dv 1)
                  := :top (:drop 3)
                  :s (:dv 2)
                  (:dv 2)
                  (:dv 1)
                  (:= (raise n 1/2))
                  :up (:rewrite ln-of-powers-positive)
                  :nx (:dv 1)
                  (:= (raise n n))
                  :up (:rewrite ln-of-powers-positive)
                  :top :s)))

(local
 (defthm factorial-as-stirling-term-lemma-1
     (implies (and (integerp n)
                   (< 1 n))
              (equal (factorial n)
                     (acl2-exp (+ (acl2-ln (expt n n))
                                  (- n)
                                  (acl2-ln (acl2-sqrt n))
                                  (- 1 (ln-trapezoid-approximation-error 1 n))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance ln-factorial-as-stirling-term-lemma)
                  (:instance exp-ln
                             (y (factorial n)))
                  (:instance (:theorem (implies (equal x y)
                                                (equal (acl2-exp x)
                                                       (acl2-exp y))))
                             (x (acl2-ln (factorial n)))
                             (y (+ (acl2-ln (expt n n))
                                   (- n)
                                   (acl2-ln (acl2-sqrt n))
                                   (- 1 (ln-trapezoid-approximation-error 1 n))))))
            :in-theory (e/d (inside-interval-p)
                            (exp-ln
                             int-ln
                             sum-ln
                             ln-trapezoid-approximation-error))))))

(local
 (defthm factorial-as-stirling-term-lemma-2
     (implies (and (integerp n)
                   (< 1 n))
              (equal (factorial n)
                     (* (expt n n)
                        (/ (acl2-exp n))
                        (acl2-sqrt n)
                        (acl2-exp (- 1 (ln-trapezoid-approximation-error 1 n))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance factorial-as-stirling-term-lemma-1)
                  )
            :in-theory (e/d (inside-interval-p)
                            (ln-trapezoid-approximation-error))))))

(local
 (defthm factorial-as-stirling-term-lemma
     (implies (and (integerp n)
                   (< 1 n))
              (equal (/ (factorial n)
                        (* (expt n n)
                           (/ (acl2-exp n))
                           (acl2-sqrt n)))
                     (acl2-exp (- 1 (ln-trapezoid-approximation-error 1 n)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance factorial-as-stirling-term-lemma-2)
                  )
            :in-theory (e/d (inside-interval-p)
                            (ln-trapezoid-approximation-error))))))

;;; Now is time to work on the term (ln-trapezoid-approximation-error i n).
;;; From what we've done, we should see that this is non-negative and the
;;; it is bounded by the Basel series. We also want to show that this i
;;; small when n is large, so we will look at what happens when both i and n
;;; are large, in which case this term should be small.

(local
 (defthmd ln-trapezoid-step-error-non-negative
     (implies (and (realp i)
                   (< 0 i))
              (<= 0 (ln-trapezoid-step-error i)))
   :hints (("Goal"
            :use ((:instance
                   int-trapezoidal-error-integrand-for-ln-of-make-partition-is-non-negative))
            ))))

(defthmd ln-trapezoid-approximation-error-trivial-lower-bound
    (implies (and (posp i)
                  (posp n))
             (<= 0 (ln-trapezoid-approximation-error i n)))
  :instructions
  ((:in-theory (disable ln-trapezoid-step-error
                        int-trapezoidal-error-integrand-for-ln))
   (:induct (ln-trapezoid-approximation-error i n))
   (:change-goal nil t)
   :bash :pro (:forwardchain 2)
   (:dv 2)
   :x
   (:= (+ (ln-trapezoid-step-error i)
          (ln-trapezoid-approximation-error (+ 1 i)
                                            n)))
   :top
   (:use
    (:instance
     int-trapezoidal-error-integrand-for-ln-of-make-partition-is-non-negative))
   :pro (:forwardchain 1)
   (:dv 2)
   (:dv 1)
   :x
   :top :bash))

(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt i -2)
         (basel-series (1+ i) n))))

(defthmd ln-trapezoid-approximation-error-upper-bound-lemma
    (implies (and (posp i)
                  (posp n))
             (<= (ln-trapezoid-approximation-error i n)
                 (* 1/12 (basel-series i n))))
  :hints (("Goal"
           :induct (ln-trapezoid-approximation-error i n))
          ("Subgoal *1/2"
           :use ((:instance
                  int-trapezoidal-error-integrand-for-ln-upper-bound))
           :in-theory (e/d (LN-TRAPEZOID-STEP-ERROR
                            basel-series)
                           (INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                            int-trapezoidal-error-integrand-for-ln-upper-bound)))
           ("Subgoal *1/1"
            :in-theory (enable basel-series)))
  )

(defthmd ln-trapezoid-approximation-error-lower-bound-lemma
    (implies (and (posp i)
                  (posp n))
             (<= (* 1/12 (basel-series (1+ i) (1+ n)))
                 (ln-trapezoid-approximation-error i n)))
  :hints (("Goal"
           :induct (ln-trapezoid-approximation-error i n))
          ("Subgoal *1/2"
           :use ((:instance
                  int-trapezoidal-error-integrand-for-ln-lower-bound))
           :in-theory (e/d (LN-TRAPEZOID-STEP-ERROR
                            basel-series)
                           (INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                            int-trapezoidal-error-integrand-for-ln-lower-bound)))
           ("Subgoal *1/1"
            :in-theory (enable basel-series))
           ))

(local
 (defthmd ln-trapezoid-approximation-error-split
     (implies (and (posp m)
                   (posp n)
                   (posp i)
                   (<= i m)
                   (<= m n))
              (equal (- (ln-trapezoid-approximation-error i n)
                        (ln-trapezoid-approximation-error i m))
                     (ln-trapezoid-approximation-error m n)))))

(local
 (defthmd ln-trapezoid-approximation-error-split-bound
     (implies (and (posp m)
                   (posp n)
                   (<= m n))
              (and (<= (* 1/12 (basel-series (1+ m) (1+ n)))
                       (ln-trapezoid-approximation-error m n))
                   (<= (ln-trapezoid-approximation-error m n)
                       (* 1/12 (basel-series m n)))))
   :hints (("Goal"
            :use ((:instance ln-trapezoid-approximation-error-upper-bound-lemma
                             (i m)
                             (n n))
                  (:instance ln-trapezoid-approximation-error-lower-bound-lemma
                             (i m)
                             (n n)))))))

(local
 (defthm real-listp-map-trapezzoidal-error-integrand-for-ln
     (implies (and (realp i)
                   (real-listp p))
              (real-listp (map-trapezoidal-error-integrand-for-ln i p)))))

(local
 (defthm real-listp-partition-rec
     (implies (and (realp a)
                   (realp delta)
                   )
              (real-listp (make-partition-rec a delta n)))))

(local
 (defthm real-listp-make-partition
     (implies (and (realp a)
                   (realp b)
                   (realp n)
                   )
              (real-listp (make-partition a b n)))
   :hints (("Goal"
            :use ((:instance real-listp-partition-rec
                             (a a)
                             (delta (/ (- b a) n))
                             (n n)))))))

(local
 (defthm real-listp-make-small-partition
     (implies (and (realp a)
                   (realp b)
                   )
              (real-listp (make-small-partition a b)))
   :hints (("Goal"
            :use ((:instance real-listp-make-partition
                             (a a)
                             (b b)
                             (n (i-large-integer))))
            :in-theory (enable make-small-partition)))))

(local
 (encapsulate nil

     (local
      (defthm lemma-1
          (implies (realp x)
                   (realp (standard-part x)))))

   (local
    (defthm lemma-2
        (implies (and (realp i) (< 0 i) (standardp i)
                      (realp m) (< 0 m) (standardp m)
                      (realp n) (< 0 n) (standardp n))
                 (realp (STRICT-INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN i M n)))
      :INSTRUCTIONS
      (:PRO (:DV 1)
            :S
            (:IN-THEORY (ENABLE INSIDE-INTERVAL-P))
            :S (:CASESPLIT (<= N M))
            :TOP :BASH :S :UP (:REWRITE LEMMA-1)
            (:REWRITE REALP-SUMLIST)
            (:REWRITE REAL-LISTP-MAP-TIMES)
            :BASH
            (:USE (:INSTANCE REAL-LISTP-MAP-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                             (P (CDR (MAKE-SMALL-PARTITION M N)))))
            :PRO
            (:USE (:INSTANCE REAL-LISTP-MAKE-SMALL-PARTITION (A M)
                             (B N)))
            :PRO (:FORWARDCHAIN 1)
            (:USE (:INSTANCE (:THEOREM (IMPLIES (REAL-LISTP P)
                                                (REAL-LISTP (CDR P))))
                             (P (MAKE-SMALL-PARTITION M N))))
            :BASH)))


   (defthm-std realp-strict-int-trapezoidal-error-integrand-for-ln
       (implies (and (realp i) (< 0 i)
                     (realp m) (< 0 m)
                     (realp n) (< 0 n))
                (realp (STRICT-INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN i M n)))
     :hints (("Goal'"
              :by lemma-2))
     )
 ))

(local
 (defthm realp-int-trapezoidal-error-integrand-for-ln
     (implies (and (realp i) (< 0 i)
                   (realp m) (< 0 m)
                   (realp n) (< 0 n))
              (realp (INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN i M n)))
   :hints (("Goal'"
            :in-theory (disable STRICT-INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN)))))


(local
 (defthm realp-ln-trapezoid-approximation-error
     (implies (and (realp m) (< 0 m)
                   (realp n) (< 0 n))
              (realp (ln-trapezoid-approximation-error m n)))
   :hints (("Goal"
            :induct (ln-trapezoid-approximation-error m n)
            :in-theory (e/d (interval-definition-theory
                             LN-TRAPEZOID-APPROXIMATION-ERROR)
                            (INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN)))
)))

(defun ln-stirling-constant-n (n)
  (- 1 (ln-trapezoid-approximation-error 1 (if (posp n) n (i-large-integer)))))

(defun stirling-constant-n (n)
  (acl2-exp (ln-stirling-constant-n n)))

(local
 (defthmd ln-trapezoid-approximation-error-gross-bounds
     (implies (and (posp m)
                   (posp n)
                   (<= m n))
              (and (<= 0
                       (ln-trapezoid-approximation-error m n))
                   (<= (ln-trapezoid-approximation-error m n)
                       1/6)))
   :hints (("Goal"
            :use ((:instance basel-series-gross-bounds
                             (i m)
                             (n n))
                  (:instance basel-series-gross-bounds
                             (i (1+ m))
                             (n (1+ n)))
                  (:instance ln-trapezoid-approximation-error-split-bound))))))

(defthmd ln-stirling-constant-n-bounds
    (and (<= 5/6 (ln-stirling-constant-n n))
         (<= (ln-stirling-constant-n n) 1))
  :hints (("Goal"
           :use ((:instance ln-trapezoid-approximation-error-gross-bounds
                            (m 1))
                 (:instance ln-trapezoid-approximation-error-gross-bounds
                            (m 1)
                            (n (i-large-integer)))
                 ))))

(defthm real-ln-stirling-constant-n
    (and (realp (ln-stirling-constant-n n))
         (< 0 (ln-stirling-constant-n n)))
  :hints (("Goal"
           :use ((:instance realp-ln-trapezoid-approximation-error
                            (m 1)
                            (n n))
                 (:instance ln-stirling-constant-n-bounds))))
  :rule-classes (:rewrite :type-prescription))

(defthm real-stirling-constant-n
    (and (realp (stirling-constant-n n))
         (< 0 (stirling-constant-n n)))
  :hints (("Goal"
           :use ((:instance realp-exp
                            (x (ln-stirling-constant-n n))))
           :in-theory (disable exp-sum
                               realp-exp
                               )))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthmd stirling-constant-n-bounds
     (and (<= (acl2-exp 5/6)
              (stirling-constant-n n))
          (<= (stirling-constant-n n)
              (acl2-exp 1)))
   :hints (("Goal"
            :use ((:instance ln-stirling-constant-n-bounds)
                  (:instance acl2-exp-is-non-decreasing
                             (x 5/6)
                             (y (ln-stirling-constant-n n)))
                  (:instance acl2-exp-is-non-decreasing
                             (x (ln-stirling-constant-n n))
                             (y 1)))
            :in-theory (disable ln-stirling-constant-n
                                acl2-exp-is-non-decreasing
                                ACL2-EXP-IS-NON-DECREASING-FOR-NON-NEGATIVES
                                exp-sum)
            ))))

(defthm limited-ln-stirling-constant-n
    (i-limited (ln-stirling-constant-n n))
  :hints (("Goal"
           :use ((:instance large-if->-large
                            (x (ln-stirling-constant-n n))
                            (y 1))
                 (:instance ln-stirling-constant-n-bounds))
           :in-theory (disable large-if->-large))))

(defthm limited-stirling-constant-n
    (i-limited (stirling-constant-n n))
  :hints (("Goal"
           :use ((:instance large-if->-large
                            (x (stirling-constant-n n))
                            (y (acl2-exp 1)))
                 (:instance stirling-constant-n-bounds)
                 )
           :in-theory (disable large-if->-large
                               ln-stirling-constant-n
                               ))))

(defthm not-small-ln-stirling-constant-n
    (not (i-small (ln-stirling-constant-n n)))
  :hints (("Goal"
           :use ((:instance small-if-<-small
                            (x (ln-stirling-constant-n n))
                            (y 5/6))
                 (:instance ln-stirling-constant-n-bounds))
           :in-theory (disable small-if-<-small))))

(defthm not-small-stirling-constant-n
    (not (i-small (stirling-constant-n n)))
  :hints (("Goal"
           :use ((:instance small-if-<-small
                            (x (stirling-constant-n n))
                            (y (acl2-exp 5/6)))
                 (:instance stirling-constant-n-bounds)
                 )
           :in-theory (disable small-if-<-small
                               ln-stirling-constant-n
                               ))))

(encapsulate nil
    (local
     (defthmd lemma-1
         (implies (and (posp m)
                       (posp n)
                       (<= m n)
                       (i-large m)
                       (i-large n))
                  (i-small (basel-series m n)))
       :hints (("Goal"
                :use ((:instance basel-series-close-for-large-values (i 1))
                      (:instance basel-series-split (i 1)))
                :in-theory (enable i-close)
                ))))

  (local
   (defthmd lemma-2
       (implies (and (posp m)
                     (posp n)
                     (<= m n)
                     (i-large m)
                     (i-large n))
                (i-small (basel-series (1+ m) (1+ n))))
     :hints (("Goal"
              :use ((:instance lemma-1
                               (m (1+ m))
                               (n (1+ n))))
              ))))

  (local
   (defthmd lemma-3
       (implies (and (posp m)
                     (posp n)
                     (<= m n)
                     (i-large m)
                     (i-large n))
                (i-small (* 1/12 (basel-series m n))))
     :hints (("Goal"
              :use ((:instance limited*small->small
                               (x 1/12)
                               (y (basel-series m n)))
                    (:instance lemma-1))
              :in-theory (disable limited*small->small)
              ))))

  (local
   (defthmd lemma-4
       (implies (and (posp m)
                     (posp n)
                     (<= m n)
                     (i-large m)
                     (i-large n))
                (i-small (* 1/12 (basel-series (1+ m) (1+ n)))))
     :hints (("Goal"
              :use ((:instance limited*small->small
                               (x 1/12)
                               (y (basel-series (1+ m) (1+ n))))
                    (:instance lemma-2))
              :in-theory (disable limited*small->small)
              ))))

  (local
   (defthmd ln-trapezoid-approximation-error-small-for-large-values
       (implies (and (posp m)
                     (posp n)
                     (<= m n)
                     (i-large m)
                     (i-large n))
                (i-small (ln-trapezoid-approximation-error m n)))
     :hints (("Goal"
              :use ((:instance STANDARD-PART-SQUEEZE
                               (x (* 1/12 (basel-series (1+ m) (1+ n))))
                               (y (ln-trapezoid-approximation-error m n))
                               (z (* 1/12 (basel-series m n))))
                    (:instance ln-trapezoid-approximation-error-split-bound)
                    (:instance lemma-3)
                    (:instance lemma-4))
              :in-theory (e/d (i-small)
                              (INT-TRAPEZOIDAL-ERROR-INTEGRAND-FOR-LN
                               LN-TRAPEZOID-APPROXIMATION-ERROR
                               LN-TRAPEZOID-STEP-ERROR)
                              )))))

  (local
   (defthmd close-ln-stirling-constant-n-lemma
       (implies (and (i-large m)
                     (i-large n)
                     (<= (if (posp m) m (i-large-integer))
                         (if (posp n) n (i-large-integer))))
                (i-close (ln-stirling-constant-n m)
                         (ln-stirling-constant-n n)))
     :hints (("Goal"
              :use ((:instance
                     ln-trapezoid-approximation-error-small-for-large-values
                     (m (if (posp m) m (i-large-integer)))
                     (n (if (posp n) n (i-large-integer))))
                    (:instance ln-trapezoid-approximation-error-split
                               (i 1)
                               (m (if (posp m) m (i-large-integer)))
                               (n (if (posp n) n (i-large-integer)))
                               )
                    (:instance
                     ln-trapezoid-approximation-error-small-for-large-values
                     (m (if (posp m) m (i-large-integer)))
                     (n (if (posp n) n (i-large-integer))))
                    )))))

  (defthmd close-ln-stirling-constant-n
      (implies (and (i-large m)
                    (i-large n))
               (i-close (ln-stirling-constant-n m)
                        (ln-stirling-constant-n n)))
    :hints (("Goal"
             :use ((:instance close-ln-stirling-constant-n-lemma
                              (m m)
                              (n n))
                   (:instance close-ln-stirling-constant-n-lemma
                              (m n)
                              (n m))
                   ))))
  )

(defthm ln-factorial-as-stirling-term
    (implies (and (integerp n)
                  (< 1 n))
             (equal (acl2-ln (factorial n))
                    (+ (acl2-ln (expt n n))
                       (- n)
                       (acl2-ln (acl2-sqrt n))
                       (ln-stirling-constant-n n))))
  :hints (("Goal" :use ((:instance ln-factorial-as-stirling-term-lemma)))))

(defthm factorial-as-stirling-term
    (implies (and (integerp n)
                  (< 1 n))
             (equal (/ (factorial n)
                       (* (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                    (stirling-constant-n n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance factorial-as-stirling-term-lemma)
                 )
           :in-theory (e/d (inside-interval-p)
                           (ln-trapezoid-approximation-error)))))

(in-theory (disable ln-stirling-constant-n
                    stirling-constant-n))

(defun-std ln-stirling-constant ()
    (standard-part (ln-stirling-constant-n (i-large-integer))))

(defthmd close-ln-stirling-constant
      (implies (i-large n)
               (i-close (ln-stirling-constant-n n)
                        (ln-stirling-constant)))
  :hints (("Goal"
           :use ((:instance close-ln-stirling-constant-n
                            (m (i-large-integer))
                            (n n))
                 (:instance i-close-transitive
                            (x (LN-STIRLING-CONSTANT-N N))
                            (y (LN-STIRLING-CONSTANT-N (I-LARGE-INTEGER)))
                            (z (STANDARD-PART (LN-STIRLING-CONSTANT-N (I-LARGE-INTEGER)))))
                 (:instance standard-part-close
                            (x (LN-STIRLING-CONSTANT-N (I-LARGE-INTEGER)))))
           :in-theory (disable i-close-transitive
                               standard-part-close))))

(defun stirling-constant ()
  (acl2-exp (ln-stirling-constant)))

(defthm-std standard-ln-stirling-constant
  (standardp (ln-stirling-constant)))

(defthm-std standard-stirling-constant
  (standardp (stirling-constant)))

(defthmd close-stirling-constant
      (implies (i-large n)
               (i-close (stirling-constant-n n)
                        (stirling-constant)))
  :hints (("Goal"
           :use ((:instance exp-continuous
                            (x (ln-stirling-constant))
                            (y (ln-stirling-constant-n n)))
                 (:instance close-ln-stirling-constant))
           :in-theory (enable stirling-constant-n))))

(defthmd close-stirling-constant-n
    (implies (and (i-large m)
                  (i-large n))
             (i-close (stirling-constant-n m)
                      (stirling-constant-n n)))
  :hints (("Goal"
           :use ((:instance close-stirling-constant (n n))
                 (:instance close-stirling-constant (n m))
                 (:instance i-close-transitive
                            (x (stirling-constant-n m))
                            (y (stirling-constant))
                            (z (stirling-constant-n n)))))))


(defthm realp-stirling-constant
    (and (realp (stirling-constant))
         (< 0 (stirling-constant))))

(defthm acl2-ln-of-stirling-constant
    (equal (acl2-ln (stirling-constant))
           (ln-stirling-constant))
  :instructions ((:dv 1)
                 (:dv 1)
                 :x-dumb (:= (acl2-exp (ln-stirling-constant)))
                 :up (:rewrite ln-exp)
                 :top :s))

(local (in-theory (disable ln-stirling-constant
                           stirling-constant
                           (ln-stirling-constant)
                           (stirling-constant)
                           )))
