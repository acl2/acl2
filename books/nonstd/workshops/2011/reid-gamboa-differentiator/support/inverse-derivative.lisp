(in-package "ACL2")

(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "composition-helpers")

; F maps domain a to domain b
; F-1 maps domain b to domain a

(encapsulate
 (( inverse-f (x) t )
  ( inverse-f-domain-p (x) t)
  ( inverse-f-prime (x) t )
  
  ( inverse-g (x) t )
  ( inverse-g-domain-p (x) t))

 (local (defun inverse-f (x) x))
 (local (defun inverse-f-domain-p (x) (acl2-numberp x)))
 (local (defun inverse-f-prime (x) (declare (ignore x)) 1))
 (local (defun inverse-g (x) x))
 (local (defun inverse-g-domain-p (x) (acl2-numberp x)))
 
 (defthm inverse-f-inversion
   (implies (inverse-f-domain-p x)
            (equal (inverse-g (inverse-f x))
                   x)))

 (defthm inverse-g-inversion
   (implies (inverse-g-domain-p x)
            (equal (inverse-f (inverse-g x))
                   x)))

 (defthm inverse-g-mapping
   (implies (inverse-g-domain-p x)
            (inverse-f-domain-p (inverse-g x))))

 (defthm inverse-f-close
   (implies (and (inverse-f-domain-p x) (standardp x)
                 (inverse-f-domain-p y) 
                 (i-close x y) (not (equal x y)))
            (i-close (/ (- (inverse-f x) (inverse-f y))
                        (- x y))
                     (inverse-f-prime x))))

 (differentiable-criteria inverse-f inverse-f-domain-p)
 (differentiable-criteria inverse-g inverse-g-domain-p)
)

                 
(include-book "nsa-ex")    
        
(defthm inverse-g-is-1-1
  (implies (and (inverse-g-domain-p x)
                (inverse-g-domain-p y)
                (not (equal x y)))
           (not (equal (inverse-g x) (inverse-g y))))
  :hints (("Goal" :use (:theorem 
                        (implies (and (inverse-g-domain-p x)
                                      (inverse-g-domain-p y)
                                      (equal (inverse-f (inverse-g x))
                                             (inverse-f (inverse-g y))))
                                 (equal x y))))))

(defthm-std inverse-g-is-standard
  (implies (standardp x)
           (standardp (inverse-g x))))

(defthm-std inverse-f-prime-is-standard
  (implies (standardp x)
           (standardp (inverse-f-prime x))))

(defthm standard-nonzero-not-small
  (implies (and (standardp x)
                (not (equal x 0)))
           (not (i-small x)))
  :hints (("Goal" :in-theory (enable nsa-theory))))
                
(defthm inverse-g-close
  (implies (and (inverse-g-domain-p x)
                (standardp x)
                (not (equal (inverse-f-prime (inverse-g x)) 0))
                (i-close x y)
                (not (equal x y))
                (inverse-g-domain-p y))
           (i-close (/ (- (inverse-g x) (inverse-g y))
                       (- x y))
                    (/ (inverse-f-prime (inverse-g x)))))
  :hints (("Goal" :use ((:instance close-/
                                   (y (/ (- (inverse-f (inverse-g x))
                                            (inverse-f (inverse-g y)))
                                         (- (inverse-g x)
                                            (inverse-g y))))
                                   (x (inverse-f-prime (inverse-g x))))
                        (:instance inverse-f-close
                                   (x (inverse-g x))
                                   (y (inverse-g y)))
                        (:instance inverse-g-continuous (x x) (y y))))))
            
