(in-package "ACL2")
(include-book "nsa/trig" :dir :system)
(include-book "exp-minimal")

(local
 (defderivative sin-eqn-deriv 
   (/ (- (acl2-exp (* #c(0 1) x))
         (acl2-exp (* #c(0 -1) x)))
      #c(0 2))))


(defthm acl2-sine-derivative
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (standardp x)
                (i-close x y)
                (not (equal x y)))
           (i-close (/ (- (acl2-sine x) (acl2-sine y))
                       (- x y))
                    (acl2-cosine x)))
  :hints (("Goal" :use (:instance sin-eqn-deriv)
           :in-theory (enable acl2-sine acl2-cosine))))
   
(local
 (defderivative cos-eqn-deriv 
   (/ (+ (ACL2-EXP (* #C(0 1) X))
         (ACL2-EXP (* #C(0 -1) X)))
      2)))

(defthm acl2-cosine-derivative
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (standardp x)
                (i-close x y)
                (not (equal x y)))
           (i-close (/ (- (acl2-cosine x) (acl2-cosine y))
                       (- x y))
                    (- (acl2-sine x))))
  :hints (("Goal" :use (:instance cos-eqn-deriv)
           :in-theory (enable acl2-sine acl2-cosine))))
   
; Now to integrate sine and cosine into the differentiator. First
; we make the -close theorems.

(defthmd elem-sine-close
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (standardp x)
                (i-close x y)
                (not (equal x y)))
           (i-close (/ (- (acl2-sine x) (acl2-sine y))
                       (- x y))
                    (acl2-cosine x)))
  :hints (("Goal" :use (:instance acl2-sine-derivative))))

(defthmd elem-cosine-close
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (standardp x)
                (i-close x y)
                (not (equal x y)))
           (i-close (/ (- (acl2-cosine x) (acl2-cosine y))
                       (- x y))
                    (- (acl2-sine x))))
  :hints (("Goal" :use (:instance acl2-cosine-derivative))))

;
(defthm-std acl2-exp-standard
  (implies (standardp x)
           (standardp (acl2-exp x))))

(defthm acl2-sine-standard
  (implies (standardp x)
           (standardp (acl2-sine x)))
  :hints (("Goal" :in-theory (enable acl2-sine))))

(defthm acl2-cosine-standard
  (implies (standardp x)
           (standardp (acl2-cosine x)))
  :hints (("Goal" :in-theory (enable acl2-cosine))))

(differentiable-criteria-expr 
 elem-sine
 (acl2-sine x)
 (acl2-numberp x))

(differentiable-criteria-expr 
 elem-sine-prime
 (acl2-cosine x)
 (acl2-numberp x))

(def-elem-derivative acl2-sine 
  elem-sine
  (acl2-numberp x)
  (acl2-cosine x))

(differentiable-criteria-expr 
 elem-cosine
 (acl2-cosine x)
 (acl2-numberp x))

(differentiable-criteria-expr 
 elem-cosine-prime
 (- (acl2-sine x))
 (acl2-numberp x))

(def-elem-derivative acl2-cosine 
  elem-cosine
  (acl2-numberp x)
  (- (acl2-sine x)))




(local
 (defderivative tangent-derivative-lemma 
   (acl2-tangent x)))

(local
 (defthm 1+tan*tan
  (implies (not (equal (acl2-cosine x) 0))
           (equal (+ 1 (* (/ (acl2-cosine x))
                          (/ (acl2-cosine x))
                          (acl2-sine x)
                          (acl2-sine x)))
                  (/ (* (acl2-cosine x) (acl2-cosine x)))))
  :hints (("goal" 
           :in-theory (disable sin**2+cos**2)
           :use (:instance sin**2+cos**2)))))

(defthm tangent-derivative
  (implies (and (acl2-numberp x)
                (not (equal (acl2-cosine x) 0))
                (acl2-numberp y)
                (not (equal (acl2-cosine y) 0))
                (standardp x)
                (i-close x y)
                (not (equal x y)))
           (i-close (/ (- (acl2-tangent x)
                          (acl2-tangent y))
                       (- x y))
                    (/ (* (acl2-cosine x) (acl2-cosine x)))))
  :hints (("Goal" 
           :use ((:instance tangent-derivative-lemma)))))

; No point making the differentiator aware of tangent -- it just expands to
; sin/cos anyway.