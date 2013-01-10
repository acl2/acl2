(in-package "ACL2")

(include-book "nsa/sqrt" :dir :system)
(include-book "ln-derivative-real")
(include-book "nsa/raise" :dir :system)

(local
 (defderivative sqrt-expr 
   (acl2-exp (* 1/2 (acl2-ln x)))))


(local (in-theory (disable raise-sqrt)))

(encapsulate
 nil
 (local 
  (defthm sqrt-to-raise
    (implies (and (realp x) (< 0 x))
             (equal (acl2-sqrt x)
                    (acl2-exp (* 1/2 (acl2-ln x)))))
    :hints (("Goal"
             :use (:instance raise-sqrt (x x))))))

 (local
  (defthmd sqrt-x-/-x
    (implies (and (realp x) (< 0 x))
             (equal (/ (acl2-sqrt x) x)
                    (/ (acl2-sqrt x))))
    :hints (("Goal" :use (:instance exp-sum 
                                    (x (* 1/2 (ACL2-LN X)))
                                    (y (* 1/2 (ACL2-LN X))))))))
  

 (defthm acl2-sqrt-derivative
   (implies (and (realp x) (< 0 x)
                 (realp y) (< 0 y)
                 (standardp x)
                 (i-close x y)
                 (not (equal x y)))
            (i-close (/ (- (acl2-sqrt x)
                           (acl2-sqrt y))
                        (- x y))
                     (/ 1/2 (acl2-sqrt x))))
   :hints (("Goal" :use ((:instance sqrt-expr)
                         (:instance sqrt-x-/-x))))))


 
(defthm-std sqrt-standard
  (implies (standardp x)
           (standardp (acl2-sqrt x))))

(differentiable-criteria-expr 
 elem-acl2-sqrt
 (acl2-sqrt x)
 (and (realp x) (< 0 x)))

(local
 (defthmd close-*-1/2
  (implies (and (acl2-numberp x)
                (i-limited x)
                (acl2-numberp y)
                (i-limited y)
                (i-close x y))
           (i-close (* 1/2 x) (* 1/2 y)))
  :hints (("Goal" :in-theory (enable i-close i-small)))))

(local
 (defthm i-limited-1/sqrt
   (implies (and (realp x)
                 (< 0 x)
                 (not (i-small x)))
            (i-limited (/ (acl2-sqrt x))))
   :hints (("Goal" :in-theory (enable i-small i-large)))))

(local
 (defthm close-to-positive-standard-not-small
   (implies (and (realp x) (< 0 x)
                 (standardp x)
                 (i-close x y))
            (not (i-small y)))
   :hints (("Goal" :in-theory (enable i-close i-small)))))

(differentiable-criteria-expr 
 elem-acl2-sqrt-prime
 (/ 1/2 (acl2-sqrt x))
 (and (realp x) (< 0 x))
 :continuous-hints (("Goal"
                     :in-theory (disable close-/)
                     :use ((:instance close-/ (x (acl2-sqrt x)) (y (acl2-sqrt  y)))
                           (:instance close-*-1/2 
                                      (x (/ (acl2-sqrt x)))
                                      (y (/ (acl2-sqrt y))))))))

(defthmd elem-acl2-sqrt-close
   (implies (and (realp x) (< 0 x)
                 (realp y) (< 0 y)
                 (standardp x)
                 (i-close x y)
                 (not (equal x y)))
            (i-close (/ (- (acl2-sqrt x)
                           (acl2-sqrt y))
                        (- x y))
                     (/ 1/2 (acl2-sqrt x))))
   :hints (("Goal" :use (:instance acl2-sqrt-derivative))))

(def-elem-derivative acl2-sqrt
  elem-acl2-sqrt
  (and (realp x) (< 0 x))
  (/ 1/2 (acl2-sqrt x)))


