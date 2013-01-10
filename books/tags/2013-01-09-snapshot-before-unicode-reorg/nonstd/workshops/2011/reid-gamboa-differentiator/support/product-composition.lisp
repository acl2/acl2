(in-package "ACL2")

(include-book "nsa/nsa" :dir :system)
(include-book "composition-helpers")

(encapsulate
 (( product-fn1 (x arg) t)
  ( product-fn1-prime (x arg) t)
  ( product-fn1-domain-p (x arg) t)

  ( product-fn2 (x arg) t)
  ( product-fn2-prime (x arg) t)
  ( product-fn2-domain-p (x arg) t)

  ( product-fn1*2 (x arg) t )
  ( product-fn1*2-prime (x arg) t)
  ( product-fn1*2-domain-p (x arg) t))

 (local (defun product-fn1 (x arg) (declare (ignore arg)) x))
 (local (defun product-fn1-prime (x arg) (declare (ignore x arg)) 1))
 (local (defun product-fn1-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (local (defun product-fn2 (x arg) (declare (ignore arg)) x))
 (local (defun product-fn2-prime (x arg) (declare (ignore x arg)) 1))
 (local (defun product-fn2-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (local (defun product-fn1*2 (x arg) (declare (ignore arg)) (* x x)))
 (local (defun product-fn1*2-prime (x arg) (declare (ignore arg)) (+ (* x 1) (* x 1))))
 (local (defun product-fn1*2-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (defthm product-fn1-domain-subsumed
   (implies (product-fn1*2-domain-p x arg)
            (product-fn1-domain-p x arg)))

 (defthm product-fn2-domain-subsumed
   (implies (product-fn1*2-domain-p x arg)
            (product-fn2-domain-p x arg)))

 (defthm product-fn-relation
   (implies (product-fn1*2-domain-p x arg)
            (equal (product-fn1*2 x arg)
                   (* (product-fn1 x arg) (product-fn2 x arg)))))

 (defthm product-d/dx-fn-relation
   (implies (product-fn1*2-domain-p x arg)
            (equal (product-fn1*2-prime x arg)
                   (+ (* (product-fn1 x arg) (product-fn2-prime x arg))
                      (* (product-fn2 x arg) (product-fn1-prime x arg))))))

 
 (derivative-hyps-arg product-fn1 arg)
 (derivative-hyps-arg product-fn2 arg)
 )

(local 
 (defthm i-close-sum
   (implies (and (i-close a b)
                 (i-close c d))
            (i-close (+ a c) (+ b d)))
   :hints (("Goal" :in-theory (enable i-close i-small)))))

(local
 (defthm i-close-product
   (implies (and (i-limited a)
                 (i-close a b)
                 (i-limited c)
                 (i-close c d))
            (i-close (* a c) (* b d)))
   :hints (("Goal" :in-theory (enable i-close i-small)
            :use ((:instance STANDARD-PART-OF-TIMES (x a) (y c))
                  (:instance STANDARD-PART-OF-TIMES (x b) (y d)))))))

(defthm product-fn1*2-close
  (implies (and (product-fn1*2-domain-p x arg) (standardp x)
                (standardp arg)
                (product-fn1*2-domain-p y arg) 
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (product-fn1*2 x arg) (product-fn1*2 y arg))
                       (- x y))
                    (product-fn1*2-prime x arg)))
  :hints (("Goal" :use ((:instance standards-are-limited
                                   (x (product-fn1-prime x arg)))
                        (:instance standards-are-limited
                                   (x (product-fn2-prime x arg)))
                        (:instance standards-are-limited
                                   (x (product-fn1 x arg)))
                        (:instance standards-are-limited
                                   (x (product-fn2 x arg)))
                        
                        (:instance i-close-limited
                                   (x (product-fn2 x arg))
                                   (y (product-fn2 y arg)))
                        (:instance product-fn1-close (x x) (y y))
                        (:instance i-close-product
                                   (c (product-fn2 y arg))
                                   (d (product-fn2 y arg))
                                   (b (product-fn1-prime x arg))
                                   (a (/ (- (product-fn1 x arg) (product-fn1 y arg))
                                         (- x y))))
                                     
                        (:instance product-fn2-close (x x) (y y))
                        (:instance i-close-product
                                  (c (product-fn1 x arg))
                                  (d (product-fn1 x arg))
                                  (b (/ (- (product-fn2 x arg) (product-fn2 y arg))
                                        (- x y)))
                                  (a (product-fn2-prime x arg)))

                        (:instance i-close-limited 
                                   (x (product-fn1-prime x arg))
                                   (y (/ (- (product-fn1 x arg) (product-fn1 y arg))
                                         (- x y))))

                        (:instance i-close-sum
                                   (a (* (product-fn1 x arg)
                                         (/ (- (product-fn2 x arg) (product-fn2 y arg))
                                            (- x y))))
                                   (b (* (product-fn1 x arg)
                                         (product-fn2-prime x arg)))
                                   (c (* (product-fn2 y arg)
                                         (/ (- (product-fn1 x arg) (product-fn1
                                                                    y arg))
                                            (- x y))))
                                   (d (* (product-fn2 y arg)
                                         (product-fn1-prime x arg))))))))
      
(defthm product-fn1*2-number
  (implies (product-fn1*2-domain-p x arg)
           (acl2-numberp (product-fn1*2 x arg))))
  
(defthm product-fn1*2-standard
  (implies (and (standardp x)
                (standardp arg)
                (product-fn1*2-domain-p x arg))
           (standardp (product-fn1*2 x arg))))

(defthm product-fn1*2-continuous
  (implies (and (product-fn1*2-domain-p x arg) (standardp x)
                (product-fn1*2-domain-p y arg) 
                (standardp arg)
                (i-close x y))
            (i-close (product-fn1*2 x arg) (product-fn1*2 y arg)))
  :hints (("Goal"
           :use ((:instance standards-are-limited (x (product-fn1 x arg)))
                 (:instance standards-are-limited (x (product-fn2 x arg)))
                 (:instance i-close-product
                           (a (PRODUCT-FN1 X arg))
                           (b (PRODUCT-FN1 y arg))
                           (c (PRODUCT-FN2 X arg))
                           (d (PRODUCT-FN2 y arg)))))))
                           
(defthm product-fn1*2-prime-number
  (implies (product-fn1*2-domain-p x arg)
           (acl2-numberp (product-fn1*2-prime x arg))))

(defthm-std product-fn1*2-prime-standard
  (implies (and (standardp x)
                (product-fn1*2-domain-p x arg)
                (standardp arg))
           (standardp (product-fn1*2-prime x arg))))

(defthm product-fn1*2-prime-continuous
  (implies (and (product-fn1*2-domain-p x arg) (standardp x)
                (product-fn1*2-domain-p y arg) 
                (standardp arg)
                (i-close x y))
            (i-close (product-fn1*2-prime x arg) (product-fn1*2-prime y arg)))
  :hints (("Goal"
           :use ((:instance standards-are-limited (x (product-fn1-prime x arg)))
                 (:instance standards-are-limited (x (product-fn1 x arg)))
                 (:instance standards-are-limited (x (product-fn2 x arg)))
                 (:instance standards-are-limited (x (product-fn2-prime x arg)))
                 (:instance i-close-product
                            (a (product-fn1-prime x arg))
                            (b (product-fn1-prime y arg))
                            (c (product-fn2 x arg))
                            (d (product-fn2 y arg)))
                 (:instance i-close-product 
                            (a (product-fn2-prime x arg))
                            (b (product-fn2-prime y arg))
                            (c (product-fn1 x arg))
                            (d (product-fn1 y arg)))
                 (:instance i-close-sum
                            (a (* (product-fn1-prime x arg) (product-fn2 x arg)))
                            (b (* (product-fn1-prime y arg) (product-fn2 y arg)))
                            (c (* (product-fn2-prime x arg)
                                  (product-fn1 x arg)))
                            (d (* (product-fn2-prime y arg)
                                  (product-fn1 y arg))))))))

(defun product-composition-apply-fn 
  (fn1 
   fn1-derivative fn1-domain fn1-symbol            
   fn2 
   fn2-derivative fn2-domain fn2-symbol
   fn1*2-symbol)

  (let ((instantiation-fns `((product-fn1 (lambda (x arg) ,fn1))
                             (product-fn1-domain-p (lambda (x arg) ,fn1-domain))
                             (product-fn1-prime (lambda (x arg) ,fn1-derivative))
                             (product-fn2 (lambda (x arg) ,fn2))
                             (product-fn2-domain-p (lambda (x arg) ,fn2-domain))
                             (product-fn2-prime (lambda (x arg) ,fn2-derivative))
                             (product-fn1*2 (lambda (x arg) (* ,fn1 ,fn2)))
                             (product-fn1*2-domain-p (lambda (x arg) 
                                                       (and ,fn1-domain
                                                            ,fn2-domain)))
                             (product-fn1*2-prime (lambda (x arg) 
                                                    (+ (* ,fn1 ,fn2-derivative)
                                                       (* ,fn2 ,fn1-derivative)))))))
        
  
    `( (encapsulate 
        nil

        (local
         (in-theory '(,@(deriv-symbols fn1-symbol)
                      ,@(deriv-symbols fn2-symbol))))

        ,@(use-deriv fn1*2-symbol 'product-fn1*2 
                     `(* ,fn1 ,fn2) 
                     `(+ (* ,fn1 ,fn2-derivative)
                            (* ,fn2 ,fn1-derivative))
                     `(and ,fn1-domain ,fn2-domain)
                     instantiation-fns)
        
        )
       (+ (* ,fn1 ,fn2-derivative)
          (* ,fn2 ,fn1-derivative)) ; compound derivative
       (and ,fn1-domain ,fn2-domain) ; compound domain
       
  )))
    