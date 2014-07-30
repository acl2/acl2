(in-package "ACL2")

(include-book "composition-helpers")
(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "nsa-ex")

;;;;;;;;;;;;;;;;;;;;;;;
;                     
; constant
;
;;;;;;;;;;;;;;;;;;;;;;;

; Constants are wrapped in elem-id to prevent them from being
; rewritten. There are some built in arithmetic operations
; that ACL2 does that cannot be disabled, but wrapping all the
; numbers in an opaque function does the trick.
(defun elem-id (c)
  c)

(defthm constant-close
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (not (equal x y))
                (acl2-numberp c))
           (i-close (/ (- (elem-id c) (elem-id c))
                       (- x y))
                    (elem-id 0)))
  :rule-classes nil)

; constant-number and constant-standard are by assumption.

(defthm constant-continuous
  (implies (acl2-numberp c)
           (i-close (elem-id c) (elem-id c)))
  :rule-classes nil)

(defthm constant-prime-continuous
  (i-close (elem-id 0) (elem-id 0))
  :rule-classes nil)

(defthm constant-prime-number
  (acl2-numberp (elem-id 0))
  :rule-classes nil)

(defthm constant-prime-standard
  (standardp (elem-id 0))
  :rule-classes nil)
                    
; The first elementary function is x
(defthm eks-close
  (implies (and (acl2-numberp x) (standardp x)
                (acl2-numberp y)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- x y)
                       (- x y))
                    (elem-id 1))))

(defthm eks-number
  (implies (acl2-numberp x)
           (acl2-numberp x))
  :rule-classes nil)

(defthm eks-standard
  (implies (and (standardp x)
                (acl2-numberp x))
           (standardp x))
  :rule-classes nil)

(defthm eks-continuous
  (implies (and (acl2-numberp x) (standardp x)
                (acl2-numberp y)
                (i-close x y))
           (i-close x y))
  :rule-classes nil)

(defthm eks-prime-number
  (implies (acl2-numberp x)
           (acl2-numberp (elem-id 1)))
  :rule-classes nil)

(defthm eks-prime-standard
  (implies (and (standardp x)
                (acl2-numberp x))
           (standardp (elem-id 1)))
  :rule-classes nil)

(defthm eks-prime-continuous
  (implies (and (acl2-numberp x) (standardp x)
                (acl2-numberp y)
                (i-close x y))
           (i-close (elem-id 1) (elem-id 1)))
  :rule-classes nil)


;;;;;;;;;;;;;;;;;;;;;;;
;                     
; unary-/
;
;;;;;;;;;;;;;;;;;;;;;;;
(local
 (defthmd common-denominator
   (implies (and (acl2-numberp x)
                 (acl2-numberp y)
                 (not (equal x 0))
                 (not (equal y 0)))
            (equal (- (unary-/ x) (unary-/ y))
                   (- (/ (- x y)
                         (* x y)))))))

(local
 (defthm elem-unary-/-close-lemma
   (implies (and (acl2-numberp x) (not (equal x 0))
                 (acl2-numberp y) (not (equal y 0))
                 (standardp x)
                 (i-close x y) (not (equal x y)))
            (equal (/ (- (unary-/ x) (unary-/ y))
                      (- x y))
                   (- (/ (* x y)))))
   :hints (("Goal"
            :in-theory (disable distributivity)
            :use (:instance common-denominator)))))

(defthm elem-unary-/-close
  (implies (and (acl2-numberp x) (not (equal x 0))
                (acl2-numberp y) (not (equal y 0))
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (unary-/ x) (unary-/ y))
                       (- x y))
                    (- (/ (* x x)))))
  :hints (("Goal"
           :in-theory (enable i-small i-close)
           :use ((:instance elem-unary-/-close-lemma)
                 (:instance close-/ (x (* x y)) (y (* x x)))
                 (:instance i-close-limited (x x) (y y))))))

(differentiable-criteria-expr
 elem-unary-/
 (unary-/ x)
 (and (acl2-numberp x) (not (equal x 0)))
 :continuous-hints (("Goal" 
                     :in-theory (enable i-small)
                     :use (:instance close-/))))

(differentiable-criteria-expr
 elem-unary-/-prime
 (- (/ (* x x)))
 (and (acl2-numberp x) (not (equal x 0)))
 :continuous-hints (("Goal" 
                     :in-theory (enable i-close i-small)
                     :use ((:instance i-close-limited (x x) (y y))
                           (:instance close-/ (x (* x x)) (y (* y y)))))))
 


;;;;;;;;;;;;;;;;;;;;;;;
;                     
; unary--
;
;;;;;;;;;;;;;;;;;;;;;;;
(local
 (defthmd elem-unary---close-lemma
  (implies (and (acl2-numberp x)
                (not (equal x 0)))
           (equal (/ x (- x))
                  -1))))

(defthm elem-unary---close
  (implies (and (acl2-numberp x) (standardp x)
                (acl2-numberp y)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (unary-- x) (unary-- y))
                       (- x y))
                    (elem-id -1)))
  :hints (("Goal" 
           :in-theory (disable EQUAL-*-/-1)
           :use ((:instance elem-unary---close-lemma (x (- y x)))))))

(differentiable-criteria-expr
 elem-unary--
 (unary-- x)
 (acl2-numberp x))

(differentiable-criteria-expr
 elem-unary---prime
 (elem-id -1)
 (acl2-numberp x))

(defun elem-const (name arg)
  (fix (cdr (assoc-equal name arg))))

(defthm-std car-standard
  (implies (standardp x)
           (standardp (car x))))

(defthm-std cdr-standard
  (implies (standardp x)
           (standardp (cdr x))))

(defthm elem-const-standard
  (implies (standardp arg)
           (standardp (elem-const name arg))))

(defthm elem-const-number
  (acl2-numberp (elem-const name arg)))

(defthm elem-const-continuous
  (i-close (elem-const name arg)
           (elem-const name arg)))

(defthm elem-const-close
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (not (equal x y)))
           (i-close (/ (- (elem-const name arg) (elem-const name arg))
                       (- x y))
                    (elem-id 0))))


(in-theory (disable elem-const
                    (:type-prescription elem-const)
                    (:executable-counterpart elem-const)))
                    
(in-theory (disable elem-id
                    (:type-prescription elem-id)
                    (:executable-counterpart elem-id)))


