(in-package "ACL2")

(include-book "nsa/nsa" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "composition-helpers")



(encapsulate
 (( sum-f (x arg1) t)
  ( sum-f-prime (x arg) t)
  ( sum-f-domain-p (x arg) t)

  ( sum-g (x arg) t)
  ( sum-g-prime (x arg) t)
  ( sum-g-domain-p (x arg) t)

  ( sum-f+g (x arg) t )
  ( sum-f+g-prime (x arg) t)
  ( sum-f+g-domain-p (x arg) t))

 (local (defun sum-f (x arg) (declare (ignore arg)) x))
 (local (defun sum-f-prime (x arg) (declare (ignore arg x)) 1))
 (local (defun sum-f-domain-p (x arg) (declare (ignore arg))(acl2-numberp x)))

 (local (defun sum-g (x arg) (declare (ignore arg)) x))
 (local (defun sum-g-prime (x arg) (declare (ignore x arg)) 1))
 (local (defun sum-g-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (local (defun sum-f+g (x arg) (declare (ignore arg)) (+ x x)))
 (local (defun sum-f+g-prime (x arg) (declare (ignore arg)) (declare (ignore x)) 2))
 (local (defun sum-f+g-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (defthm sum-f-domain-subsumed
   (implies (sum-f+g-domain-p x arg)
            (sum-f-domain-p x arg)))

 (defthm sum-g-domain-subsumed
   (implies (sum-f+g-domain-p x arg)
            (sum-g-domain-p x arg)))

 (defthm sum-fn-relation
   (implies (sum-f+g-domain-p x arg)
            (equal (sum-f+g x arg)
                   (+ (sum-f x arg) (sum-g x arg)))))

 (defthm sum-d/dx-fn-relation
   (implies (sum-f+g-domain-p x arg)
            (equal (sum-f+g-prime x arg)
                   (+ (sum-f-prime x arg) (sum-g-prime x arg)))))

 (derivative-hyps-arg sum-f arg)
 (derivative-hyps-arg sum-g arg)
 )

(local 
 (defthm i-close-sum
   (implies (and (i-close a b)
                 (i-close c d))
            (i-close (+ a c) (+ b d)))
   :hints (("Goal" :in-theory (enable i-close i-small)))))


(derivative-hyps-arg 
 sum-f+g arg
 :close-hints (("Goal" :use ((:instance sum-f-close)
                             (:instance sum-g-close)
                             (:instance i-close-sum
                                        (a (/ (- (sum-f x arg) (sum-f y arg)) (- x y)))
                                        (b (sum-f-prime x arg))
                                        (c (/ (- (sum-g x arg) (sum-g y arg)) (- x y)))
                                        (d (sum-g-prime x arg))))))
 )


; Basic steps here:
;  define functions to wrap the raw expresiions
;  show that the functions do indeed wrap the expressions
;  apply functional instantiation to those functions
;  unwrap the results, getting the theorems we need

; fnX, fnX-derivative, fnX-domain are expressions
(defun sum-d/dx-apply-fn 
  (fn1 
   fn1-derivative fn1-domain fn1-symbol            
   fn2 
   fn2-derivative fn2-domain fn2-symbol
   fn1+2-symbol)

  (let ((instantiation-fns `((sum-f (lambda (x arg) ,fn1))
                             (sum-f-domain-p (lambda (x arg) ,fn1-domain))
                             (sum-f-prime (lambda (x arg) ,fn1-derivative))
                             (sum-g (lambda (x arg) ,fn2))
                             (sum-g-domain-p (lambda (x arg) ,fn2-domain))
                             (sum-g-prime (lambda (x arg) ,fn2-derivative))
                             (sum-f+g (lambda (x arg) (+ ,fn1 ,fn2)))
                             (sum-f+g-domain-p (lambda (x arg) (and ,fn1-domain ,fn2-domain)))
                             (sum-f+g-prime (lambda (x arg) (+ ,fn1-derivative ,fn2-derivative))))))

  
    `( (encapsulate 
        nil

        (local
         (in-theory '(,@(deriv-symbols fn1-symbol)
                      ,@(deriv-symbols fn2-symbol))))

        ,@(use-deriv fn1+2-symbol 'sum-f+g 
                     `(+ ,fn1 ,fn2) 
                     `(+ ,fn1-derivative ,fn2-derivative)
                     `(and ,fn1-domain ,fn2-domain)
                     instantiation-fns)
        
        )
       (+ ,fn1-derivative ,fn2-derivative) ; compound derivative
       (and ,fn1-domain ,fn2-domain)       ; compound domain
       
       )
    
    ))
    

;(sum-d/dx-apply-fn 'x '(elem-id 1) '(acl2-numberp x) 'leftstuff
;                   'x '(elem-id 1) '(acl2-numberp x) 'rightstuff
;                   'bothstuff)