(in-package "ACL2")

(include-book "sum-composition")
(include-book "product-composition")
(include-book "chain-composition")
(include-book "inverse-composition")
(include-book "composition-helpers")
(include-book "composition-elem")
;EXPR:
; #
; (binary-+ EXPR EXPR)
; (binary-* EXPR EXPR)
; (unary-- EXPR)
; (unary-/ EXPR)
; (acl2-exp EXPR)
; x

(defun differentiate-x (f-name)
  (let* ((close-thm (symbol-append f-name 'close))
         (number-thm (symbol-append f-name 'number))
         (standard-thm (symbol-append f-name 'standard))
         (continuous-thm (symbol-append  f-name 'continuous))
         (prime-number-thm (symbol-append f-name 'prime-number))
         (prime-standard-thm (symbol-append f-name 'prime-standard))
         (continuous-standard-thm (symbol-append f-name 'prime-continuous))
         )
  `( (encapsulate
      nil

      (defthmd ,close-thm
        (implies (and (acl2-numberp x)
                      (acl2-numberp y)
                      (standardp x)
                      (standardp arg)
                      (i-close x y) (not (equal x y)))
                 (i-close (/ (- x y)
                             (- x y))
                          (elem-id 1)))
        :hints (("Goal" :by (:instance eks-close) :in-theory nil)))

      (defthmd ,number-thm
        (implies (acl2-numberp x)
                 (acl2-numberp x))
        :hints (("Goal" :by (:instance eks-number) :in-theory nil)))

      (defthmd ,standard-thm
        (implies (and (standardp x)
                      (acl2-numberp x))
                 (standardp x))
        :hints (("Goal" :by (:instance eks-standard) :in-theory nil)))

      (defthmd ,continuous-thm
        (implies (and (acl2-numberp x) (standardp x)
                      (acl2-numberp y)
                      (i-close x y))
                 (i-close x y))
        :hints (("Goal" :by (:instance eks-continuous) :in-theory nil)))

      (defthmd ,prime-number-thm
        (implies (acl2-numberp x)
                 (acl2-numberp (elem-id 1)))
        :hints (("Goal" :by (:instance eks-prime-number) :in-theory nil)))

      (defthmd ,prime-standard-thm
        (implies (and (standardp x)
                      (acl2-numberp x))
                 (standardp (elem-id 1)))
        :hints (("Goal" :by (:instance eks-prime-standard) :in-theory nil)))

      (defthmd ,continuous-standard-thm
        (implies (and (acl2-numberp x) (standardp x)
                      (acl2-numberp y)
                      (i-close x y))
           (i-close (elem-id 1) (elem-id 1)))
        :hints (("Goal" :by (:instance eks-prime-continuous) :in-theory nil))))
     (elem-id 1)
     (acl2-numberp x))))


(defun differentiate-constant (c f-name)
  (let* ((close-thm (symbol-append f-name 'close))
         (number-thm (symbol-append f-name 'number))
         (standard-thm (symbol-append f-name 'standard))
         (continuous-thm (symbol-append  f-name 'continuous))
         (prime-number-thm (symbol-append  f-name 'prime-number))
         (prime-standard-thm (symbol-append f-name 'prime-standard))
         (continuous-standard-thm (symbol-append f-name 'prime-continuous))
         )

    `( (encapsulate
        nil

        (defthmd ,close-thm
          (implies (and (acl2-numberp x)
                        (acl2-numberp y)
                        (standardp x)
                        (standardp arg)
                        (i-close x y) (not (equal x y)))
                   (i-close (/ (- (elem-const ,c arg) (elem-const ,c arg))
                               (- x y))
                            (elem-id 0)))
          :hints (("Goal"
                   :use (:instance elem-const-close (name ,c))
                   )))

        (defthmd ,number-thm
          (acl2-numberp (elem-const ,c arg))
          :hints (("Goal" :in-theory '(elem-const-number))))

        (defthmd ,standard-thm
          (implies (standardp arg)
                   (standardp (elem-const ,c arg)))
          :hints (("Goal" :in-theory '(elem-const-standard))) )

        (defthmd ,continuous-thm
          (i-close (elem-const ,c arg) (elem-const ,c arg))
          :hints (("Goal"
                   :by (:instance elem-const-continuous (name ,c))
                   )))

        (defthm ,prime-number-thm
          (acl2-numberp (elem-id 0))
          :hints (("Goal" :in-theory (enable elem-id))) )

        (defthmd ,prime-standard-thm
          (standardp (elem-id 0))
          :hints (("Goal" :in-theory (enable elem-id))) )

        (defthmd ,continuous-standard-thm
          (i-close (elem-id 0) (elem-id 0))
          :hints (("Goal" :by (:instance constant-prime-continuous) :in-theory nil))))
       (elem-id 0)
       (acl2-numberp x))))

(defun binary-expr-p (operator expr)
  (and (equal (first expr) operator)
       (not (null (second expr)))
       (not (null (third expr)))
       (null (cdddr expr))))

(defun unary-expr-p (expr)
  (and (symbolp (first expr))
       (not (null (second expr)))
       (null (cddr expr))))

(defun constant-expr-p (expr)
  (and (equal (first expr) 'elem-const)
       ;(symbolp (second expr))
       (equal (third expr) 'arg)
       (null (cdddr expr))))

(defun differentiate-binary-+ (f-expr f-name lhs-diff rhs-diff)
  (let ((combination-results
         (sum-d/dx-apply-fn (second f-expr)   ; LHS expr
                            (second lhs-diff) ; LHS derivative
                            (third lhs-diff)  ; LHS domain
                            (symbol-append f-name 'left)
                            (third f-expr)    ;RHS expr
                            (second rhs-diff) ; RHS derivative
                            (third rhs-diff)  ; RHS domain
                            (symbol-append f-name 'right)
                            f-name)))
    `( (encapsulate
        nil
        (local ,(first lhs-diff))
        (local ,(first rhs-diff))

        ,(first combination-results)
        )
       ,(second combination-results) ; combination derivative
       ,(third combination-results)))) ; combination domain

(defun differentiate-binary-* (f-expr f-name lhs-diff rhs-diff)
  (let ((combination-results
         (product-composition-apply-fn
          (second f-expr)   ; LHS expr
          (second lhs-diff) ; LHS derivative
          (third lhs-diff)  ; LHS domain
          (symbol-append f-name 'left)
          (third f-expr)    ;RHS expr
          (second rhs-diff) ; RHS derivative
          (third rhs-diff)  ; RHS domain
          (symbol-append f-name 'right)
          f-name)))
    `( (encapsulate
        nil
        (local ,(first lhs-diff))
        (local ,(first rhs-diff))

        ,(first combination-results)
        )
       ,(second combination-results) ; combination derivative
       ,(third combination-results)))) ; combination domain



(defun differentiate-unary (f-expr f-name inner-diff unary-infos)
  (let ((unary-info (assoc-equal (first f-expr) unary-infos)))
    (if (null unary-info)
        (er hard 'top-level
            "er1 Can't differentiate unary function ~x0" (first f-expr))

      (let ((combination-results
             (chain-composition-apply-fn
              (list (first unary-info) 'x) ; outer function (unary)
              (fourth unary-info) ; derivative of unary function
              (third unary-info) ; domain of unary function
              (second unary-info) ; proof prefix for unary function
              (second f-expr) ; inner function
              (second inner-diff) ; its derivative
              (third inner-diff)  ; its domain
              (symbol-append f-name 'inner)
              f-name)))
        `( (encapsulate
            nil

	    ,(first inner-diff)             ;(local ,(first inner-diff))

            ,(first combination-results)
            )
           ,(second combination-results) ; combination derivative
           ,(third combination-results)))) ; combination domain
    ))

(defun differentiate-inverse (f-expr f-name inner-diff unary-fn-list inverse-functions-list)
  (let* ((inverse-info (assoc-equal (first f-expr) inverse-functions-list))
	 (deriv-info (assoc-equal (fourth (cdr inverse-info)) unary-fn-list)))
    (if (or (null inverse-info) (null deriv-info))
        (er hard 'top-level
            "er2 Can't differentate inverse function ~x0" (first f-expr))
	(let ((inverse-results
	       (inv-d/dx-apply-fn
		`(,(fourth (cdr inverse-info)) x)
		(third (cdr deriv-info))
		(second (cdr inverse-info))
		(symbol-append f-name 'inverse)
		(third (cdr inverse-info))
		(first f-expr))))
	  (let ((unary-results
		 (differentiate-unary f-expr
				      f-name
				      `((encapsulate
					 nil
					 (deflabel ,f-name)
					 ,(first inner-diff)
					 (deflabel ,(symbol-append f-name 'inverse-results))
					 ,(first inverse-results))
					,(second inner-diff)
					,(third inner-diff))
				      `( (,(first f-expr) . (,(symbol-append f-name 'inverse)
							      ,(third inverse-results)
							      ,(second inverse-results))) )
				      )))
	    unary-results
	    #|
	    `( (encapsulate
		nil
		,(first unary-results)
		(deflabel ,(symbol-append f-name 'copy-of-inverse-results))
		,(first inverse-results))
	       ,(second unary-results)
	       ,(third unary-results) )
	    |#
	    )))))

(defun has-known-inverse-p (fn inverse-functions-list)
    (let ((inverse-info (assoc-equal fn inverse-functions-list)))
      (not (null inverse-info)))
  )

(defun has-known-derivative-p (fn unary-fn-list)
    (let ((unary-info (assoc-equal fn unary-fn-list)))
      (not (null unary-info)))
  )

(defun differentiate-fn (f-expr f-name unary-fn-list inverse-functions-list)

  (cond ((equal f-expr 'x)
         (differentiate-x f-name))
        ((atom f-expr)
         (er hard  'top-level "er3 Can't differentate ~x0" f-expr))
        ((constant-expr-p f-expr)
         (differentiate-constant (second f-expr) f-name)
         )
        ((binary-expr-p 'binary-+ f-expr)
         (differentiate-binary-+ f-expr f-name
                                 (differentiate-fn (second f-expr)
                                                   (symbol-append f-name 'left)
                                                   unary-fn-list
						   inverse-functions-list)
                                 (differentiate-fn (third f-expr)
                                                   (symbol-append f-name 'right)
                                                   unary-fn-list
						   inverse-functions-list)))
        ((and (unary-expr-p f-expr)
	      (has-known-derivative-p (first f-expr) unary-fn-list))
         (differentiate-unary f-expr f-name
                              (differentiate-fn (second f-expr)
                                                (symbol-append f-name 'inner)
                                                unary-fn-list
						inverse-functions-list)
                              unary-fn-list))

        ((and (unary-expr-p f-expr)
	      (has-known-inverse-p (first f-expr) inverse-functions-list))
	 (differentiate-inverse f-expr f-name
				(differentiate-fn (second f-expr)
                                                (symbol-append f-name 'inner)
                                                unary-fn-list
						inverse-functions-list)
				unary-fn-list
				inverse-functions-list
				))

        ((unary-expr-p f-expr)
	 (er hard 'top-level "er4 Can't differentiate unary function ~x0" f-expr))

	((binary-expr-p 'binary-* f-expr)
	 (differentiate-binary-* f-expr f-name
                                 (differentiate-fn (second f-expr)
                                                   (symbol-append f-name 'left)
                                                   unary-fn-list
						   inverse-functions-list)
                                 (differentiate-fn (third f-expr)
                                                   (symbol-append f-name 'right)
                                                   unary-fn-list
						   inverse-functions-list)))


        (t (er hard  'top-level "er5 Can't differentate ~x0" f-expr))))


(mutual-recursion
 (defun flatten-and (expr)
   (if (and (consp expr)
            (equal (car expr) 'and))
       (flatten-ands (rest expr))
     (list expr)))

 (defun flatten-ands (exprs)
   (if (endp exprs)
       nil
     (append (flatten-and (first exprs))
             (flatten-ands (rest exprs)))))
 )

(defun clean-fn (expr arg)
  (if (atom expr)
      (cond ((equal expr 'binary-+) '+)
            ((equal expr 'unary--) '-)
            ((equal expr 'binary-*) '*)
            ((equal expr 'unary-/) '/)
            (t expr))
    (cond ((equal (first expr) 'elem-const)
           (cdr (assoc-equal (second (second expr)) arg)))
          ((equal (first expr) 'elem-id)
           (second expr))
          (t
           (cons (clean-fn (car expr) arg)
                 (clean-fn (cdr expr) arg))))))



(defun clean-domain (expr arg)
  (clean-fn (remove-duplicates-equal (flatten-and `(and ,expr))) arg))

(defun contains-atom (val expr)
  (if (atom expr)
      (equal val expr)
    (or (contains-atom val (car expr))
        (contains-atom val (cdr expr)))))

(mutual-recursion
 (defun argify-list (key-base idx expr)
   (declare (xargs :measure (acl2-count expr)))
   (cond ((consp expr)
          (mv-let (car-expr car-alist)
                  (argify (cons idx key-base)
                          (car expr))
                  (mv-let (cdr-expr cdr-alist)
                          (argify-list key-base (1+ idx) (cdr expr))
                          (mv (cons car-expr cdr-expr)
                              (append car-alist cdr-alist))))
          )
         (t (mv nil nil))))


 (defun argify (key-base expr)
   (declare (xargs :measure (acl2-count expr)))
   (cond
         ((equal expr 'x)
          (mv 'x nil))
         ((symbolp expr)
          (mv `(elem-const ',key-base arg)
              (list (cons key-base expr))))
         ((and (consp expr)
               (equal (first expr) 'quote)
               (acl2-numberp (second expr)))
          (mv `(elem-const ',key-base arg)
              (list (cons key-base (second expr)))))
         ((and (consp expr)
               (symbolp (first expr))
               (null (cdr expr)))
          (mv `(elem-const ',key-base arg)
              (list (cons key-base expr))))

         ((consp expr)
          (mv-let (arg-expr arg-alist)
                  (argify-list key-base 1
                               (cdr expr))
                  (mv (cons (car expr)  arg-expr)
                      arg-alist)))
         (t
          (mv (er hard  'top-level "er6 Can't differentate ~x0" expr) nil))))
 )

(defun listify-args (args)
  (if (endp args)
      nil
    (cons `(cons ',(car (first args)) ,(cdr (first args)))
          (listify-args (rest args)))))

(defun argify-unpack-thms (args all-args thm-base)
  (if (endp args)
      nil
    (cons `(local
            (defthm ,thm-base
              (implies (acl2-numberp ,(cdr (first args)))
                       (equal (elem-const ',(car (first args)) ,all-args)
                              ,(cdr (first args))))
              :hints (("Goal" :in-theory (enable elem-const
                                                 (:executable-counterpart elem-const))))))
          (argify-unpack-thms (cdr args)
                              all-args
                              (symbol-append thm-base 'a)))))

(defun argify-unpack-thm-names (n thm-base)
  (if (zp n)
      nil
    (cons thm-base
          (argify-unpack-thm-names (- n 1) (symbol-append thm-base 'a)))))

(defun arg-number-thms (args)
  (if (endp args)
      nil
    (cons `(acl2-numberp ,(cdr (first args)))
          (arg-number-thms (rest args)))))

(defun arg-standard-thms (args)
  (if (endp args)
      nil
    (if (symbolp (cdr (first args)))
        (cons `(standardp ,(cdr (first args)))
              (arg-standard-thms (rest args)))
      ;(er hard  'top-level "neek neek ~x0" `(standardp ,(cdr (first args))))
      ;nil
      ;)))
      (arg-standard-thms (rest args)))))

(defun add-one (n)
  (+ 1 n))

(defun double (num)
  (+ num num))


;(set-state-ok t)
;(i-am-here)
(defun subst-all (news olds tree)
  (if (endp olds)
      tree
    (subst-all (rest news)
               (rest olds)
               (subst (first news) (first olds) tree))))

(mutual-recursion
 (defun expand (expr terminals w depth)
   (declare (xargs :mode :program))
   (if (zp depth)
       (mv nil nil 'depth-exceeded)
     (if (consp expr)
         (cond ((equal (first expr) 'quote)
                (mv expr nil nil))
               ((equal (first expr) 'lambda)
                (mv-let (all-expanded symbols err)
                        (expand (third expr) terminals w depth)
                        (mv `(lambda ,(second expr)
                               ,all-expanded)
                            symbols err)))
               ((or (not (symbolp (first expr)))
                    (member-equal (first expr) terminals))
                (expand-all expr terminals w depth))
               (t
                (let* ((fn (first expr))
                       (expanded
                        (getprop fn 'unnormalized-body
                                 nil 'current-acl2-world w))
                       (formals
                        (getprop fn 'formals
                                 nil 'current-acl2-world w))
                       (arguments (rest expr))
                       (substituted (subst-all arguments formals expanded)))
                  (mv-let (all-expanded symbols err)
                          (if expanded
                              (expand substituted terminals w (- depth 1))
                            (expand-all expr terminals w (- depth 1)))
                          (mv all-expanded
                              (union-equal symbols (list fn))
                              err)))))
       (mv expr nil nil))))

 (defun expand-all (exprs terminals w depth)
   (declare (xargs :mode :program))
   (if (endp exprs)
       (mv nil nil nil)
     (mv-let (expanded-1 symbols-1 err-1)
             (expand (first exprs) terminals w depth)
             (mv-let (expanded-2 symbols-2 err-2)
                     (expand-all (rest exprs) terminals w depth)
                     (mv (cons expanded-1 expanded-2)
                         (union-equal symbols-1 symbols-2)
                         (or err-1 err-2)))))))


#|
     (cons (expand (first exprs) terminals w (- depth 1))
           (expand-all (rest exprs) terminals w (- depth 1))))))
|#


(defun differentiate-and-clean-fn (f-expr f-name unary-fn-list inverse-functions-list w)
  (declare (xargs :mode :program))
  (mv-let (expanded-f-expr expanded-symbols expand-err)
          (expand f-expr
		  (append (strip-cars unary-fn-list)
			  (strip-cars inverse-functions-list))
		  w 20)
          (if expand-err
              '(er hard 'top-level "Could not expand expression.")
          (mv-let
           (f-expr-bound bindings)
           (argify '(1) expanded-f-expr)
           (let* ((diff (differentiate-fn f-expr-bound (symbol-append f-name 'dirty) unary-fn-list inverse-functions-list))
                  (derivation-code (first diff))
                  (domain-expr (clean-domain (third diff) bindings))
                  (derivative-expr (clean-fn (second diff) bindings))
                  (std-thm (symbol-append f-name 'args-standard))
                  (clean-f-expr (clean-fn f-expr bindings))
                  (listified-bindings (cons 'list (listify-args bindings))))
             `(encapsulate
               nil
               ,derivation-code ; Do the actual derivative-proving

               ,@(argify-unpack-thms bindings
                                     listified-bindings
                                     'unargify)


               (local
                (defthm-std ,std-thm
                  (implies (and ,@(arg-standard-thms bindings))
                           (standardp ,listified-bindings))
                  :rule-classes nil))



               (defthm ,f-name
                 (implies (and ,@domain-expr
                               ,@(subst 'y 'x domain-expr)
                               (standardp x)
                               ,@(arg-standard-thms bindings)
                               ,@(arg-number-thms bindings)
                               (i-close x y) (not (equal x y)))
                          (i-close (/ (- ,clean-f-expr ,(subst 'y 'x clean-f-expr))
                                      (- x y))
                                   ,derivative-expr))
                 :hints (("Goal"
                          :use ((:instance ,(symbol-append f-name 'dirty-close)
                                           (arg ,listified-bindings))
                                (:instance ,std-thm))
                          :in-theory '(elem-id
                                       ,@expanded-symbols
                                       ,@(argify-unpack-thm-names
                                          (length bindings)
                                          'unargify)

                                       ))))))))))



;(differentiate-and-clean-fn '(binary-+ x x) 'twoxs nil)


(defmacro def-elem-derivative (fn thm-name-prefix domain derivative)
  `(table unary-derivatives ',fn '(,thm-name-prefix
                                   ,domain
                                   ,derivative)))

(defmacro def-elem-inverse (fn thm-name-prefix domain range fn-inverse)
  `(table inverse-functions ',fn '(,thm-name-prefix
                                   ,domain
				   ,range
                                   ,fn-inverse)))

(def-elem-derivative unary-/
  elem-unary-/
  (and (acl2-numberp x) (not (equal x 0)))
  (- (/ (* x x))))


(def-elem-derivative unary--
  elem-unary--
  (acl2-numberp x)
  (elem-id -1))


(encapsulate
 nil
 (set-state-ok t)
 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)

 (defun diff-fn (thm-name-base form state)
   (declare (xargs :mode :program))
   (mv-let (flg val bindings state)
           (TRANSLATE1 FORM :STOBJS-OUT
                       '((:STOBJS-OUT . :STOBJS-OUT))
                       T 'TOP-LEVEL
                       (w state) STATE)
           (mv-let (x unary-derivs state)
                   (table-fn 'unary-derivatives 'nil state
                             '(table unary-derivatives))
                   (mv-let (x inverse-functions state)
			   (table-fn 'inverse-functions 'nil state
				     '(table inverse-functions))
			   (mv `(progn ,(differentiate-and-clean-fn
					 val
					 thm-name-base
					 unary-derivs
					 inverse-functions
					 (w state)))
			       state)))))

 (defun diff-fn-quieted (thm-name-base form noisy state)
   (declare (xargs :mode :program))
   (mv-let (proof state)
           (diff-fn thm-name-base form state)
           (mv nil
               `(with-output
                 ,@(if noisy
                       nil
                     '(:off  (history event warning prove proof-tree proof-builder summary)))
                 ,proof)
               state))))

(defmacro defderivative (&whole whole-form thm-name-base form &key noisy)
  `(make-event (diff-fn-quieted ',thm-name-base ',form ,noisy state)
	       :on-behalf-of ,whole-form))
