(in-package "ACL2")

;(include-book "data-structures/utilities" :dir :system)


(defun symbol-append (s1 s2)
  (intern (string-append (symbol-name s1) 
                         (string-append "-" (symbol-name s2))) "ACL2"))

;(defun symbol-append (s1 s2)
;  (u::pack-intern 'symbol-append s1 '- s2))

(defmacro differentiable-criteria (fn domain &key number-hints standard-hints
                                      continuous-hints create-rules)
  (let* ((number-thm (symbol-append fn 'number))
         (standard-thm (symbol-append fn 'standard))
         (continuous-thm (symbol-append fn 'continuous))
         (rule-classes-expr (if create-rules nil '(:rule-classes nil))))
    `(progn
     (defthm ,number-thm
       (implies (,domain x)
                (acl2-numberp (,fn x)))
       :hints (,@number-hints)
       ,@rule-classes-expr);:rule-classes nil)

     (defthm ,standard-thm
       (implies (and (standardp x)
                     (,domain x))
                (standardp (,fn x)))
       :hints (,@standard-hints)
       ,@rule-classes-expr);:rule-classes nil)

     (defthm ,continuous-thm
       (implies (and (,domain x) (standardp x)
                     (,domain y) 
                     (i-close x y))
                (i-close (,fn x) (,fn y)))
       :hints (,@continuous-hints)
       ,@rule-classes-expr))));:rule-classes nil))))

(defun derivative-hyps-arg-fn (fn arg domain number-hints standard-hints continuous-hints)
  (let* ((number-thm (symbol-append fn 'number))
         (standard-thm (symbol-append fn 'standard))
         (continuous-thm (symbol-append fn 'continuous)))
    `( (defthm ,number-thm
         (implies (,domain x ,arg)
                  (acl2-numberp (,fn x ,arg)))
         :hints (,@number-hints))

       (defthm ,standard-thm
         (implies (and (standardp x)
                       (standardp ,arg)
                       (,domain x ,arg))
                  (standardp (,fn x ,arg)))
         :hints (,@standard-hints))

       (defthm ,continuous-thm
         (implies (and (,domain x ,arg) (standardp x)
                       (,domain y ,arg)
                       (standardp ,arg)
                       (i-close x y))
                  (i-close (,fn x ,arg) (,fn y ,arg)))
         :hints (,@continuous-hints)))))



(defmacro derivative-hyps-arg (fn arg
                                  &key
                                  close-hints
                                  number-hints standard-hints continuous-hints
                                  prime-number-hints prime-standard-hints prime-continuous-hints)
  (let* ((domain (symbol-append fn 'domain-p))
         (fn-prime (symbol-append fn 'prime))
         (close-thm (symbol-append fn 'close)))
    `(progn
       ,@(derivative-hyps-arg-fn fn arg domain number-hints standard-hints continuous-hints)
       ,@(derivative-hyps-arg-fn fn-prime arg domain prime-number-hints
                                 prime-standard-hints prime-continuous-hints)

       (defthm ,close-thm
         (implies (and (,domain x ,arg) (standardp x)
                       (,domain y ,arg)
                       (standardp ,arg)
                       (i-close x y) (not (equal x y)))
                  (i-close (/ (- (,fn x ,arg) (,fn y ,arg))
                              (- x y))
                           (,fn-prime x ,arg)))
         :hints (,@close-hints)))))

(defun derivative-hyps-fn (fn domain number-hints standard-hints continuous-hints)
  (let* ((number-thm (symbol-append fn 'number))
         (standard-thm (symbol-append fn 'standard))
         (continuous-thm (symbol-append fn 'continuous)))
    `( (defthm ,number-thm
         (implies (,domain x)
                  (acl2-numberp (,fn x)))
         :hints (,@number-hints))

       (defthm ,standard-thm
         (implies (and (standardp x)
                       (,domain x))
                  (standardp (,fn x)))
         :hints (,@standard-hints))

       (defthm ,continuous-thm
         (implies (and (,domain x) (standardp x)
                       (,domain y)
                       (i-close x y))
                  (i-close (,fn x) (,fn y)))
         :hints (,@continuous-hints)))))

(defmacro derivative-hyps (fn
                                  &key
                                  close-hints
                                  number-hints standard-hints continuous-hints
                                  prime-number-hints prime-standard-hints prime-continuous-hints)
  (let* ((domain (symbol-append fn 'domain-p))
         (fn-prime (symbol-append fn 'prime))
         (close-thm (symbol-append fn 'close)))
    `(progn
       ,@(derivative-hyps-fn fn domain number-hints standard-hints continuous-hints)
       ,@(derivative-hyps-fn fn-prime domain prime-number-hints
			     prime-standard-hints prime-continuous-hints)

       (defthm ,close-thm
         (implies (and (,domain x) (standardp x)
                       (,domain y)
                       (i-close x y) (not (equal x y)))
                  (i-close (/ (- (,fn x) (,fn y))
                              (- x y))
                           (,fn-prime x)))
         :hints (,@close-hints)))))

(defmacro differentiable-criteria-expr 
  (theorem-prefix 
   fn domain 
   &key number-hints standard-hints continuous-hints)
  (let* ((number-thm (symbol-append theorem-prefix 'number))
         (standard-thm (symbol-append theorem-prefix 'standard))
         (continuous-thm (symbol-append theorem-prefix 'continuous)))
    `(progn
     (defthmd ,number-thm
       (implies ,domain
                (acl2-numberp ,fn))
       :hints (,@number-hints))

     (defthm-std ,standard-thm
       (implies (and (standardp x)
                     ,domain x)
                (standardp ,fn))
       :hints (,@standard-hints))
     (in-theory (disable ,standard-thm))

     (defthmd ,continuous-thm
       (implies (and ,domain (standardp x)
                     ,(subst 'y 'x domain) 
                     (i-close x y))
                (i-close ,fn ,(subst 'y 'x fn)))
       :hints (,@continuous-hints)))))


; Prove number, standard, and continuous. There are theorems
; starting with thm-base-symbol that prove all these things
; in expanded-out form.
(defun symbolwrap-diff (base-symbol domain-p thm-base)
  `((defthm ,(symbol-append base-symbol 'number)
      (implies (,domain-p x)
               (acl2-numberp (,base-symbol x)))
      :hints (("Goal" ;:in-theory '(,domain-p ,base-symbol)
               :use (:instance ,(symbol-append thm-base 'number)))))
      
    (defthm-std ,(symbol-append base-symbol 'standard)
      (implies (and (standardp x)
                    (,domain-p x))
               (standardp (,base-symbol x)))
      :hints (("Goal" ;:in-theory 
              ; '(,domain-p ,base-symbol)
               :use (:instance ,(symbol-append thm-base 'standard)))))
      
    (defthm ,(symbol-append base-symbol 'continuous)
      (implies (and (,domain-p x) (standardp x)
                    (,domain-p y)
                    (i-close x y) )
               (i-close (,base-symbol x)
                        (,base-symbol y)))
      :hints (("Goal" :in-theory '(,domain-p
                                   ,base-symbol))
              ("Goal'"
               ;:in-theory (enable)
               :use ((:instance ,(symbol-append thm-base 'continuous))
                     (:instance ,(symbol-append thm-base 'number))))))))
              
      
; Prove number,s tandard, and continuous for a function and its
; derivative. Also prove that the differential is close to the
; derivative.
(defun symbolwrap-deriv (base-symbol thm-base)
  (let ((domain-p (symbol-append base-symbol 'domain-p)))
    `(,@(symbolwrap-diff base-symbol domain-p thm-base)
      ,@(symbolwrap-diff (symbol-append base-symbol 'prime)
                         domain-p
                         (symbol-append thm-base 'prime))

      (defthm ,(symbol-append base-symbol 'close)
        (implies (and (,domain-p x) 
                      (,domain-p y)
                      (standardp x)
                      (i-close x y) (not (equal x y)))
                 (i-close (/ (- (,base-symbol x) (,base-symbol y))
                             (- x y))
                          (,(symbol-append base-symbol 'prime) x)))
        :hints (("Goal" ;:in-theory
; '( ,domain-p ,base-symbol ,(symbol-append base-symbol 'prime)))
              
                 :use (:instance ,(symbol-append thm-base 'close))
             
                 :in-theory (enable)))))))
              
(defun instantiate-diff (fn domain-p thm-symbol instantiation-fns)
  `((defthm ,(symbol-append fn 'number)
      (implies (,domain-p x)
               (acl2-numberp (,fn x)))
      :hints (("Goal"
               :use ((:functional-instance ,(symbol-append thm-symbol 'number)
                                         ,@instantiation-fns)))))

        
    (defthm ,(symbol-append fn 'standard)
      (implies (and (standardp x)
                    (,domain-p x))
               (standardp (,fn x)))
      :hints (("Goal"
               :use ((:functional-instance ,(symbol-append thm-symbol 'standard)
                                         ,@instantiation-fns)))))

        
    (defthm ,(symbol-append fn 'continuous)
      (implies (and (,domain-p x)
                    (standardp x)
                    (,domain-p y)
                    (i-close x y))
               (i-close (,fn x) (,fn y)))
      :hints (("Goal"
               :use ((:functional-instance ,(symbol-append thm-symbol 'continuous)
                                         ,@instantiation-fns)))))))
       
(defun instantiate-deriv (fn thm-symbol instantiation-fns)
  (let ((domain-p (symbol-append fn 'domain-p)))

    `(,@(instantiate-diff fn domain-p thm-symbol instantiation-fns)
      ,@(instantiate-diff (symbol-append fn 'prime)
                          domain-p
                          (symbol-append thm-symbol 'prime)
                          instantiation-fns)

      (defthm ,(symbol-append fn 'close)
           (implies (and (,domain-p x) (standardp x)
                         (,domain-p y)
                         (i-close x y) (not (equal x y)))
                    (i-close (/ (- (,fn x) (,fn y))
                                (- x y))
                             (,(symbol-append fn 'prime) x)))
           :hints (("Goal"
                    :use ((:functional-instance ,(symbol-append thm-symbol 'close)
                                              ,@instantiation-fns))))))))


(defun unwrap-diff (out-thm wrapped fn-expr domain-expr)
  `((defthmd ,(symbol-append out-thm 'number)
      (implies ,domain-expr
               (acl2-numberp ,fn-expr))
      :hints (("Goal"
               :use (:instance ,(symbol-append wrapped 'number))))
      )

    (defthmd ,(symbol-append out-thm 'standard)
      (implies (and ,domain-expr
                    (standardp x))
               (standardp ,fn-expr))
      :hints (("Goal"
                :use (:instance ,(symbol-append wrapped 'standard))))
      )

    (defthmd ,(symbol-append out-thm 'continuous)
      (implies (and ,domain-expr
                    (standardp x)
                    ,(subst 'y 'x domain-expr)
                    (i-close x y)  )
               (i-close ,fn-expr ,(subst 'y 'x fn-expr)))
      :hints (("Goal"
               :use (:instance ,(symbol-append wrapped 'continuous))))
      )))

(defun unwrap-deriv (out-thm wrapped fn-expr fn-prime-expr domain-expr)
  `(,@(unwrap-diff out-thm wrapped  
                   fn-expr domain-expr)
    ,@(unwrap-diff (symbol-append out-thm 'prime)
                   (symbol-append wrapped 'prime)
                   
                   fn-prime-expr domain-expr)

    (defthmd ,(symbol-append out-thm 'close)
      (implies (and ,domain-expr
                    (standardp x)                      
                    ,(subst 'y 'x domain-expr)
                    (i-close x y) (not (equal x y)))
               (i-close (/ (- ,fn-expr  ,(subst 'y 'x fn-expr))
                           (- x y))
                        ,fn-prime-expr))
      :hints (("Goal"
                :use (:instance ,(symbol-append wrapped 'close))))
      )))
                 
    

(defun use-diff (out-thm in-thm fn-expr domain-expr instantiation-fns)
  `((defthmd ,(symbol-append out-thm 'number)
      (implies ,domain-expr
               (acl2-numberp ,fn-expr))
      :hints (("Goal"
               :use ((:functional-instance 
                    ,(symbol-append in-thm 'number)
                    ,@instantiation-fns)))))
      

    (defthmd ,(symbol-append out-thm 'standard)
      (implies (and ,domain-expr
                    (standardp x)
                    (standardp arg))
               (standardp ,fn-expr))
      :hints (("Goal"
               :use ((:functional-instance 
                    ,(symbol-append in-thm 'standard)
                    ,@instantiation-fns)))))
      

    (defthmd ,(symbol-append out-thm 'continuous)
      (implies (and ,domain-expr
                    (standardp x)
                    ,(subst 'y 'x domain-expr)
                    (standardp arg)
                    (i-close x y)  )
               (i-close ,fn-expr ,(subst 'y 'x fn-expr)))
      :hints (("Goal"
               :use ((:functional-instance 
                    ,(symbol-append in-thm 'continuous)
                    ,@instantiation-fns)))))
      ))

(defun use-deriv (out-thm in-thm fn-expr fn-prime-expr domain-expr instantiation-fns)
  `(,@(use-diff out-thm in-thm  
                fn-expr domain-expr instantiation-fns)
    ,@(use-diff (symbol-append out-thm 'prime)
                (symbol-append in-thm 'prime)
                
                fn-prime-expr domain-expr instantiation-fns)

    (defthmd ,(symbol-append out-thm 'close)
      (implies (and ,domain-expr
                    (standardp x)    
                    (standardp arg)
                    ,(subst 'y 'x domain-expr)
                    (i-close x y) (not (equal x y)))
               (i-close (/ (- ,fn-expr  ,(subst 'y 'x fn-expr))
                           (- x y))
                        ,fn-prime-expr))
      :hints (("Goal"
               :use ((:functional-instance 
                    ,(symbol-append in-thm 'close)
                    ,@instantiation-fns)))))))

(defun use-diff-unary (out-thm in-thm fn-expr domain-expr instantiation-fns)
  `((defthmd ,(symbol-append out-thm 'number)
      (implies ,domain-expr
               (acl2-numberp ,fn-expr))
      :hints (("Goal"
               :use ((:functional-instance 
		      ,(symbol-append in-thm 'number)
		      ,@instantiation-fns)))))
      

    (defthmd ,(symbol-append out-thm 'standard)
      (implies (and ,domain-expr
                    (standardp x))
               (standardp ,fn-expr))
      :hints (("Goal"
               :use ((:functional-instance 
		      ,(symbol-append in-thm 'standard)
		      ,@instantiation-fns)))))
      

    (defthmd ,(symbol-append out-thm 'continuous)
      (implies (and ,domain-expr
                    (standardp x)
                    ,(subst 'y 'x domain-expr)
                    (i-close x y)  )
               (i-close ,fn-expr ,(subst 'y 'x fn-expr)))
      :hints (("Goal"
               :use ((:functional-instance 
		      ,(symbol-append in-thm 'continuous)
		      ,@instantiation-fns)))))
      ))

(defun use-deriv-unary (out-thm in-thm fn-expr fn-prime-expr domain-expr instantiation-fns)
  `(,@(use-diff-unary out-thm in-thm  
		      fn-expr domain-expr instantiation-fns)
      ,@(use-diff-unary (symbol-append out-thm 'prime)
			(symbol-append in-thm 'prime)
			fn-prime-expr domain-expr instantiation-fns)

      (defthmd ,(symbol-append out-thm 'close)
	  (implies (and ,domain-expr
			(standardp x)    
			,(subst 'y 'x domain-expr)
			(i-close x y) (not (equal x y)))
		   (i-close (/ (- ,fn-expr  ,(subst 'y 'x fn-expr))
			       (- x y))
			    ,fn-prime-expr))
	:hints (("Goal"
		 :use ((:functional-instance 
			,(symbol-append in-thm 'close)
			,@instantiation-fns)))))))
      
                 
(defun diff-symbols (symbol-base)
  (list (symbol-append symbol-base 'number)
        (symbol-append symbol-base 'standard)
        (symbol-append symbol-base 'continuous)))

(defun deriv-symbols (symbol-base)
  (cons (symbol-append symbol-base 'close)
        (append 
         (diff-symbols symbol-base)
         (diff-symbols (symbol-append symbol-base 'prime)))))

(defun inverse-symbols (symbol-base)
  (list (symbol-append symbol-base 'inverse-in-range)
	(symbol-append symbol-base 'domain-is-number)
	(symbol-append symbol-base 'inverse-relation)
	(symbol-append symbol-base 'd/dx-f-relation)
	(symbol-append symbol-base 'prime-not-zero)
	(symbol-append symbol-base 'preserves-not-close)))


(defmacro inverse-hyps (fn &key inverse-hints domain-hints inverse-relation-hints dx-hints not-zero-hints not-close-hints)
  (let* ((fn-prime (symbol-append fn 'prime))
	 (fn-domain-p (symbol-append fn 'domain-p))
	 (fn-inverse (symbol-append fn 'inverse))
	 (fn-inverse-prime (symbol-append fn 'inverse-prime))
	 (fn-inverse-domain-p (symbol-append fn 'inverse-domain-p))
	 
	 (inverse-in-range-thm (symbol-append fn 'inverse-in-range))
         (domain-is-number (symbol-append fn 'domain-is-number))
         (inverse-relation (symbol-append fn 'inverse-relation))
         (d/dx-f-relation (symbol-append fn 'd/dx-f-relation))
         (prime-not-zero (symbol-append fn 'prime-not-zero))
         (preserves-not-close (symbol-append fn 'preserves-not-close))
	 )

    `(progn
       (defthm ,inverse-in-range-thm
	   (implies (,fn-inverse-domain-p x)
		    (,fn-domain-p (,fn-inverse x)))
         :hints (,@inverse-hints))

       (defthm ,domain-is-number
	   (implies (,fn-domain-p x)
		    (acl2-numberp x))
         :hints (,@domain-hints))

       
       (defthm ,inverse-relation
	   (implies (,fn-inverse-domain-p x)
		    (equal (,fn (,fn-inverse x))
			   x))
	 :hints (,@inverse-relation-hints))

       (defthm ,d/dx-f-relation
	   (implies (,fn-inverse-domain-p x)
		    (equal (,fn-inverse-prime x)
			   (/ (,fn-prime (,fn-inverse x)))))
	 :hints (,@dx-hints))

       (defthm ,prime-not-zero
	   (implies (,fn-domain-p x)
		    (not (equal (,fn-prime x) 0)))
	 :hints (,@not-zero-hints))

       (defthm ,preserves-not-close
	   (implies (and (,fn-domain-p x)
			 (,fn-domain-p y)
			 (i-limited x)
			 (not (i-close x y)))
		    (not (i-close (,fn x) (,fn y))))
	 :hints (,@not-close-hints))
       )))

