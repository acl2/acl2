#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "../symbol-fns/symbol-fns")

(set-state-ok t)

;; (defun in-conclusion (term conclusion)
;;   (declare (type t term conclusion))
;;   (if (consp conclusion)
;;       (or (equal term (car conclusion))
;; 	  (in-conclusion term (cdr conclusion)))
;;     nil))

;; (defun in-conclusion-or-backchain-fn (term mfc state)
;;   (declare (xargs :mode :program)
;; 	   (ignore state))
;;   (and (or (mfc-ancestors mfc)
;; 	   (in-conclusion term (mfc-clause mfc)))
;;        (list (cons 'in-conclusion-or-backchain (syn::true)))))

;; (defmacro in-conclusion-or-backchaining (term)
;;   `(and
;;     (equal in-conclusion-or-backchain-variable ,term)
;;     (bind-free (in-conclusion-or-backchain-fn `in-conclusion-or-backchain-variable acl2::mfc acl2::state) 
;; 	       (in-conclusion-or-backchain))))

(defun mfc-rw-equiv (term obj equiv mfc state)
  (declare (xargs :mode :program
		  :guard (state-p state)))
  (let ((wrld  (access metafunction-context mfc :wrld))
	(rcnst (access metafunction-context mfc :rcnst)))
    (let ((geneqv (car (geneqv-lst equiv nil 
				   (access rewrite-constant rcnst
					   :current-enabled-structure)
				   wrld))))
      (if (and (termp term wrld)
	       (member-eq obj '(t nil ?)))
	  (mv-let
	   (rw ttree)
	   (rewrite-entry
	    (rewrite term nil 'meta)
	    :rdepth (rewrite-stack-limit wrld)
	    :type-alist (access metafunction-context mfc :type-alist)
	    :geneqv geneqv
	    :wrld wrld
	    :fnstack (access metafunction-context mfc :fnstack)
	    :ancestors (access metafunction-context mfc :ancestors)
	    :backchain-limit (access metafunction-context mfc
				     :backchain-limit)
	    :simplify-clause-pot-lst (access metafunction-context mfc
					     :simplify-clause-pot-lst)
	    :rcnst rcnst
	    :gstack (access metafunction-context mfc :gstack)
	    :ttree nil)
	   (declare (ignore ttree))
	   rw)
	(prog2$ (cw "***~%!!! mfc-rw-equiv failed wf-test !!!~%***~%")
		term)))))

(defun equiv-binding-fn (equiv term key mfc state)
  (declare (xargs :mode :program)
	   (type (satisfies state-p) state))
  (let ((term (acl2::mfc-rw-equiv term 'acl2::? equiv mfc state)))
    (cons (cons key term) nil)))

(mutual-recursion

 (defun enquote-function-call (function)
   (declare (type (satisfies consp) function)
	    (xargs :measure (acl2-count function)))
   (mbe :logic (if (consp function)
		   `(cons (quote ,(car function))
			  ,(enquote-function-args (cdr function)))
		 function)
	:exec
	`(cons (quote ,(car function))
	       ,(enquote-function-args (cdr function)))))

 (defun enquote-function-args (args)
   (declare (type t args)
	    (xargs :measure (acl2-count args)))
   (if (consp args)
       (let ((arg (car args)))
	 (if (consp arg)
	     `(cons ,(enquote-function-call arg) ,(enquote-function-args (cdr args)))
	   `(cons ,(car args)
		  ,(enquote-function-args (cdr args)))))
     'nil))

 )

(defun enquote-term (term)
  (declare (type t term))
  (if (consp term)
      (enquote-function-call term)
    term))

(defmacro defbinding (equiv)
  `(defmacro ,(symbol-fns::suffix equiv `-binding) (key term)
     `(,',equiv ,key (double-rewrite ,term))))
