(in-package "ACL2")
(include-book "nsa/nsa" :dir :system)
(include-book "composition-helpers")

(encapsulate
 (( chain-f (x arg) t)
  ( chain-f-prime (x arg) t)
  ( chain-f-domain-p (x arg) t)

  ( chain-g (x arg) t)
  ( chain-g-prime (x arg) t)
  ( chain-g-domain-p (x arg) t)

  ( chain-fog (x arg) t )
  ( chain-fog-prime (x arg) t)
  ( chain-fog-domain-p (x arg) t))

 (local (defun chain-f (x arg) (declare (ignore arg)) x))
 (local (defun chain-f-prime (x arg) (declare (ignore x arg)) 1))
 (local (defun chain-f-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (local (defun chain-g (x arg) (declare (ignore arg)) x))
 (local (defun chain-g-prime (x arg) (declare (ignore x arg)) 1))
 (local (defun chain-g-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (local (defun chain-fog (x arg) (declare (ignore arg)) x))
 (local (defun chain-fog-prime (x arg) (declare (ignore x arg)) 1))
 (local (defun chain-fog-domain-p (x arg) (declare (ignore arg)) (acl2-numberp x)))

 (defthm chain-g-domain-subsumed
   (implies (chain-fog-domain-p x arg)
            (chain-g-domain-p x arg)))

 (defthm chain-f-domain-subsumed
   (implies (chain-fog-domain-p x arg)
            (chain-f-domain-p (chain-g x arg) arg)))

 (defthm chain-fog-relation
   (implies (chain-fog-domain-p x arg)
            (equal (chain-fog x arg)
                   (chain-f (chain-g x arg) arg))))

 (defthm chain-fog-prime-relation
   (implies (chain-fog-domain-p x arg)
            (equal (chain-fog-prime x arg)
                   (* (chain-f-prime (chain-g x arg) arg)
                      (chain-g-prime x arg)))))

 
 (derivative-hyps-arg chain-f arg)
 (derivative-hyps-arg chain-g arg)
 )

(local
 (defthm lemma1
   (implies (and (acl2-numberp a)
                 (acl2-numberp b)
                 (acl2-numberp c)
                 (not (equal c 0))
                 (not (equal b 0)))
            (equal (* (/ a b)
                      (/ b c))
                   (/ a c)))))
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

(local
 (defthm lemma2
   (implies (and (i-close 0 x)
                 (i-limited y))
            (i-close 0 (* x y)))
   :hints (("Goal" :in-theory (enable i-close i-small)))))

(derivative-hyps-arg 
 chain-fog arg
 :prime-continuous-hints
 (("Goal"
   :use ((:instance standards-are-limited
                    (x (chain-g-prime x arg)))
         (:instance standards-are-limited
                    (x (CHAIN-F-PRIME (CHAIN-G X arg) arg)))
         (:instance i-close-product
                    (a (CHAIN-G-PRIME X arg))
                    (b (CHAIN-G-PRIME Y arg))
                    (c (CHAIN-F-PRIME (CHAIN-G X arg) arg))
                    (d (CHAIN-F-PRIME (CHAIN-G Y arg) arg))))))
 :close-hints
 (("Goal"
           :cases ((= (chain-g x arg) (chain-g y arg))
                   (not (= (chain-g x arg) (chain-g y arg)))))
          ("Subgoal 2"
           :use ((:instance chain-g-close (x x) (y y))
                 (:instance lemma2 
                            (x (chain-g-prime x arg))
                            (y (chain-f-prime (chain-g x arg) arg)))
                 (:instance standards-are-limited 
                            (x (chain-f-prime (chain-g x arg) arg)))))
          ("Subgoal 1"
           :use ((:instance lemma1 
                           (a (- (chain-f (chain-g x arg) arg) 
                                 (chain-f (chain-g y arg) arg)))
                           (b (- (chain-g x arg) (chain-g y arg)))
                           (c (- x y)))
                 (:instance i-close-product
                            (b (/ (- (chain-f (chain-g x arg) arg) 
                                     (chain-f (chain-g y arg) arg))
                                  (- (chain-g x arg) (chain-g y arg))))
                            (a (chain-f-prime (chain-g x arg) arg))
                            (d (/ (- (chain-g x arg) (chain-g y arg))
                                  (- x y)))
                            (c (chain-g-prime x arg)))
                 (:instance standards-are-limited
                            (x (chain-f-prime (chain-g x arg) arg)))
                 (:instance standards-are-limited
                            (x (chain-g-prime x arg)))
                 (:instance chain-g-close (x x) (y y))
                 (:instance chain-f-close 
                            (x (chain-g x arg))
                            (y (chain-g y arg))))))
 )

; The outer function is already wrapped and has theorems proved
; about it
(defun chain-composition-apply-fn 
  (f-expr f-derivative f-domain f-symbol
          g-expr g-derivative g-domain g-symbol fog-symbol)

  (let* ((fog-expr (subst g-expr 'x f-expr))
         (fog-prime-expr `(* ,(subst g-expr 'x f-derivative) ,g-derivative))
         (fog-domain-p-expr `(and ,g-domain
                                  ,(subst g-expr 'x f-domain)))
         (instantiation-fns `((chain-f (lambda (x arg) ,f-expr))
                              (chain-f-domain-p (lambda (x arg) ,f-domain))
                              (chain-f-prime (lambda (x arg) ,f-derivative))
                              (chain-g (lambda (x arg) ,g-expr))
                              (chain-g-domain-p (lambda (x arg) ,g-domain))
                              (chain-g-prime (lambda (x arg) ,g-derivative))
                              (chain-fog (lambda (x arg) ,fog-expr))
                              (chain-fog-domain-p (lambda (x arg) ,fog-domain-p-expr))
                              (chain-fog-prime (lambda (x arg) ,fog-prime-expr)))))

    
    `( (encapsulate 
        nil

        
        (local
         (in-theory '(,@(deriv-symbols f-symbol)
                      ,@(deriv-symbols g-symbol))))
        
        ,@(use-deriv fog-symbol 'chain-fog
                     fog-expr
                     fog-prime-expr
                     fog-domain-p-expr
                     instantiation-fns)
        
        
        )
       ,fog-prime-expr    ; compound derivative
       ,fog-domain-p-expr ; compound domain
       
       )
    
    ))
