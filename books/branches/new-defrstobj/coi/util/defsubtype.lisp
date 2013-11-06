#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "rule-sets")
(include-book "mv-nth")
(include-book "defun-support")

(set-verify-guards-eagerness 2)

;; ===================================================================
;; 
;; Define the rule-set classes used to characterize the subtype rules.
;;
;; ===================================================================

(def::rule-set type-backchain)
(def::rule-set type-definitions)

;; ===================================================================
;;
;; A means of evaluating constant expressions.
;;
;; ===================================================================

;; Give this its own book ..

(defmacro def::const (name value)
  `(make-event `(defmacro ,',name () ,,value)))

;; ===================================================================
;;
;; def::subtype :
;;
;; A macro for generating the kinds of rules we might want to use in
;; reasoning about subtypes.
;;
;; ===================================================================

(defun arg-appears-in-body (arg body)
  (if (consp body)
      (cond
       ((consp (car body))
	(or (arg-appears-in-body arg (car body))
	    (arg-appears-in-body arg (cdr body))))
       (t
	(or (equal arg (car body))
	    (arg-appears-in-body arg (cdr body)))))
    nil))
	
(defun all-args-appear-in-body (args body)
  (if (consp args)
      (and (arg-appears-in-body (car args) body)
	   (all-args-appear-in-body (cdr args) body))
    t))

;; (test rec)

(defun negate-term (term)
  (if (consp term)
      (if (and (equal (car term) 'not)
	       (consp (cdr term)))
	  (cadr term)
	`(not ,term))
    term))

(defun fapp-appears (name term)
  (if (consp term)
      (or (if (consp term) (fapp-appears name (car term)) (equal (car term) name))
	  (fapp-appears name (cdr term)))
    (equal name term)))

(defun recursive-function (name body)
  (if (and (consp body)
	   (equal (car body) 'if)
	   (consp (cdr body))
	   (consp (cddr body))
	   (consp (cdddr body)))
      (cond  ;; (if test a b)
       ((fapp-appears name (caddr body))
	(mv t (cadr body) (caddr body)))
       ((fapp-appears name (cadddr body))
	(mv t (negate-term (cadr body)) (cadddr body)))
       (t
	(mv nil nil nil)))
    (mv nil nil nil)))

(defun def::subtype-events (name args declare body)

  (declare (xargs :mode :program))

  (let ((implies-name (packn-pos (list "IMPLIES-" name) name))
	(name-implies (packn-pos (list name "-IMPLIES") name))

	;; DAG : we used to allow some arguments of the type statement
	;; to be ignored.  We no longer do because things
	;; (forward-chaining) doesn't work in that case.  In
	;; particular, there will be no rules to push the free
	;; variable onto the alist and the other rules will not
	;; backchain to cause the rewrite rules to fire.  Thus, we
	;; will just fail if there are ignored arguments.  If you
	;; really need to ignore arguments, try using "any"

	#+joe(ignore (not (all-args-appear-in-body args body)))
	)
    (mv-let (rec test rbody) (recursive-function name body)
    
	    (let ((implies-name-hyps (if rec `(and ,test ,rbody) body))
		  (implies-name-conc `(,name ,@args))
		  (name-implies-hyps (if rec `(and (,name ,@args) ,test) `(,name ,@args)))
		  (name-implies-conc (if rec rbody body))
		  )
	      
	      `(encapsulate
		   ()
		 
		 (defun ,name ,args
		   ,@declare
		   ,body)
		 
		 (local (in-theory (disable (,name))))

		 (defthm ,implies-name
		   (implies
		    ,implies-name-hyps
		    ,implies-name-conc)
		   :rule-classes (:rewrite :forward-chaining))
		 
		 
		 (defthm ,name-implies
		   (implies
		    ,name-implies-hyps
		    ,name-implies-conc)
		   :rule-classes (:rewrite :forward-chaining))
		 
		 (in-theory (disable (:rewrite ,name-implies)))
		 ,@(if rec nil `((in-theory (disable ,name))))
		 
		 (rule-set type-backchain (:rewrite ,name-implies))
		 (rule-set type-definitions ,name)
		 
		 )))))
    
(defmacro def::subtype (name args &rest body)
  (met ((decls body) (defun::strip-decls body))
       (def::subtype-events name args decls body)))

