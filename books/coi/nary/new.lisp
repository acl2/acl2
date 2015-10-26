(in-package "NARY")
(include-book "coi/util/defun" :dir :system)
(include-book "coi/util/in-conclusion" :dir :system)

(defun wf-primitive-fix (term)
  (declare (type t term))
  (and (consp term)
       (symbolp (car term)) ;; fixing function
       (consp (cdr term))
       (symbolp (cadr term))      ;; fixed-variable
       (symbol-listp (cddr term)) ;; moduli
       ))

(defun wf-fix (term)
  (declare (type t term))
  (and (consp term)
       (if (equal (car term) 'double-rewrite)
           (and (consp (cdr term))
                (wf-primitive-fix (cadr term)))
         (wf-primitive-fix term))))

(defun wf-primitive-binding (term)
  (declare (type t term))
  (and (consp term)
       (symbolp (car term)) ;; equiv
       (consp (cdr term))
       (symbolp (cadr term)) ;; bound result
       (consp (cddr term))
       (wf-fix (caddr term)) ;; fix
       (null (cdddr term))))
       
(defun wf-binding (term)
  (declare (type t term))
  (and (consp term)
       (if (equal (car term) 'rewrite-equiv)
           (and (consp (cdr term))
                (wf-primitive-binding (cadr term)))
         (wf-primitive-binding term))))

;; ------------------------------------------------------------------

(def::und extract-variables-from-primitive-fix (term)
  (declare (xargs :signature ((wf-primitive-fix) symbolp symbolp symbol-listp)))
  (mv (car term) (cadr term) (cddr term)))

(in-theory (disable wf-primitive-fix))

(def::und extract-variables-from-fix (term)
  (declare (xargs :signature ((wf-fix) symbolp symbolp symbol-listp)))
  (if (equal (car term) 'double-rewrite)
      (extract-variables-from-primitive-fix (cadr term))
    (extract-variables-from-primitive-fix term)))

(in-theory (disable wf-fix))

(def::un replace-new-var-primitive-binding (bound-var term)
  (declare (xargs :signature ((symbolp wf-primitive-binding) wf-primitive-binding)))
  (list* (car term) bound-var (cddr term)))

(def::und replace-new-var (bound-var term)
  (declare (xargs :signature ((symbolp wf-binding) wf-binding)))
  (if (equal (car term) 'rewrite-equiv)
      `(rewrite-equiv ,(replace-new-var-primitive-binding bound-var (cadr term)))
    (replace-new-var-primitive-binding bound-var term)))

(in-theory (disable replace-new-var-primitive-binding))

(def::und extract-variables-from-primitive-binding (term)
  (declare (xargs :signature ((wf-primitive-binding) symbolp symbolp symbolp symbol-listp)))
  (let ((new-var (cadr term)))
    (met ((fix-fn old-var moduli) (extract-variables-from-fix (caddr term)))
      (mv new-var fix-fn old-var moduli))))

(in-theory (disable wf-primitive-binding))

(def::und extract-variables-from-binding (term)
  (declare (xargs :signature ((wf-binding) symbolp symbolp symbolp symbol-listp)))
  (if (equal (car term) 'rewrite-equiv)
      (extract-variables-from-primitive-binding (cadr term))
    (extract-variables-from-primitive-binding term)))

(in-theory (disable wf-binding))

;; ------------------------------------------------------------------

(defmacro nary-symbol (&rest args)
  `(symbol-fns::join-symbols 'nary::witness-symbol ,@args))

(def::und fix-equiv-name (fix-fn)
  (declare (xargs :signature ((symbolp) symbolp)))
  (nary-symbol fix-fn "-EQUIV"))

(def::und fix-unfix-name (fix-fn)
  (declare (xargs :signature ((symbolp) symbolp)))
  (nary-symbol "UN-" fix-fn))

(def::und bound-var-name (new-var)
  (declare (xargs :signature ((symbolp) symbolp)))
  (nary-symbol "BOUND-" new-var))

(encapsulate
    (
     ((nary-monitor * *) => *)
     )
  (local
   (defun nary-monitor (x y) 
     (list x y)))
  )

(defun nary-monitor-off-fn (x y)
  (declare (type t x y))
  (declare (ignore x y)) 
  t)

(defun nary-monitor-on-fn (x y)
  (declare (type t x y))
  (if (and (not x) (not y))
      (not (cw "~%~%"))
    (not (cw "~p0 rewrote to ~p1~%" x y))))

(defmacro monitor-on ()
  `(defattach nary-monitor nary-monitor-on-fn))

(defmacro monitor-off ()
  `(defattach nary-monitor nary-monitor-off-fn))

(monitor-off)

(def::und bind-context-fn (n term)
  (declare (xargs :signature ((natp wf-binding) true-listp t t t)))
  (met ((new-var fix-fn old-var moduli) (extract-variables-from-binding term))
    (let* ((unfix-fn     (fix-unfix-name fix-fn))
           (fix-equiv-fn (fix-equiv-name fix-fn))
           (bound-var    (bound-var-name new-var))
           (new-var-hit  (nary-symbol new-var "-HIT-" n))
           (binding      (replace-new-var bound-var term)))
      (mv `(
            ,binding
            (bind-free (,unfix-fn ,bound-var ,old-var ',new-var-hit ',new-var) (,new-var-hit ,new-var))
            )
          new-var-hit
          `(,fix-equiv-fn ,bound-var ,new-var ,@moduli)
          `(syntaxp (nary-monitor ,old-var ,new-var))
          ))))

;; ------------------------------------------------------------------

(defun wf-binding-list (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (wf-binding (car list))
         (wf-binding-list (cdr list)))))

(def::und bind-context-rec (list n bindings new-vars tests debugs)
  (declare (xargs :signature ((wf-binding-list natp true-listp true-listp true-listp true-listp) 
                              true-listp
                              true-listp
                              true-listp
                              true-listp)))
  (if (endp list) (mv bindings new-vars tests debugs)
    (met ((new-bindings new-var-hit test debug) (bind-context-fn n (car list)))
      (let ((bindings (append bindings new-bindings))
            (new-vars (cons new-var-hit new-vars))
            (tests    (cons test tests))
            (debugs   (cons debug debugs)))
        (bind-context-rec (cdr list) (1+ n) bindings new-vars tests debugs)))))

(def::und bind-context-list (list)
  (met ((bindings new-vars tests debugs) (bind-context-rec list 0 nil nil nil nil))
    `(and
      ,@bindings
      (or ,@new-vars)
      ,@tests
      (syntaxp (nary-monitor nil nil))
      ,@debugs)))

(defmacro bind-context (&rest args)
  (declare (type (satisfies wf-binding-list) args))
  (bind-context-list args))

;; ------------------------------------------------------------------

(defun return-binding (new-var-hit unfix-success new-var value)
  (acons new-var-hit (if unfix-success acl2::*t* acl2::*nil*) (acons new-var value nil)))

(defun extract-new-value (fix-fn term)
  (if (equal (car term) fix-fn)
      (cadr term)
    term))
    
(def::un context-fn (term hyps hints)
  (declare (xargs :signature ((wf-primitive-fix t t) t)))
  (met ((fix-fn old-var moduli) (extract-variables-from-primitive-fix term))
    (let* ((bound-var    (bound-var-name old-var))
           (fix-equiv-fn (fix-equiv-name fix-fn))
           (unfix-fn     (fix-unfix-name fix-fn))
           (args         (cons old-var moduli))
           (open-fix-equiv   (nary-symbol "OPEN-" fix-equiv-fn "-IN-CONCLUSION"))
           (fix-equiv-of-fix (nary-symbol fix-equiv-fn "-OF-" fix-fn))
           (fix-equiv-no-fix (nary-symbol fix-equiv-fn "-NO-" fix-fn))
           )
      `(encapsulate
           ()
         
         (defun ,unfix-fn (bound-var old-var new-var-hit new-var)
           (let ((new-value (extract-new-value ',fix-fn bound-var)))
             (return-binding new-var-hit (not (equal new-value old-var)) new-var new-value)))
         
         (defun ,fix-equiv-fn (,bound-var ,@args)
           (equal (,fix-fn ,bound-var ,@moduli)
                  (,fix-fn ,@args)))
         
         (defthm ,open-fix-equiv
           (implies
            (acl2::in-conclusion-check (,fix-equiv-fn ,bound-var  ,@args))
            (equal (,fix-equiv-fn ,bound-var ,@args)
                   (equal (,fix-fn ,bound-var ,@moduli)
                          (,fix-fn ,@args)))))
         
         (defthm ,fix-equiv-of-fix
           ,(let ((conc `(,fix-equiv-fn (,fix-fn ,@args) ,@args)))
              (if hyps `(implies ,hyps ,conc)
                conc))
           ,@(and hints `(:hints ,hints)))
         
         (defthm ,fix-equiv-no-fix
           (,fix-equiv-fn ,old-var ,@args))
       
       ))))

(defmacro def::context (term &key (hyps 'nil) (hints 'nil))
  (declare (type (satisfies wf-primitive-fix) term))
  (context-fn term hyps hints))

#|

;; We also want to be able to support equivalence relations
;; defined as such:

(defun assoc-equiv (x y list)
  (forall (a) 
    (implies 
     (member a list) 
     (equal (assoc a x) (assoc a y)))))

;; To do so, we will want to introduce a fixing function.

;; There are a number of rules that we are going to want ..

(defthm commute-equiv
  (implies
   (good-rewrite-order x y)
   (equal (equiv y x)
          (equov x y))))

(defthm equiv-reduction
  (implies
   (in-conclusion-check (equal (fix x n) y))
   (iff (equal (fix x n) y)
        (and (fixed-p y n)
             (equiv x y n)))))


(defthm equiv-zed
  (equiv x x))

(defthm substitute
  (implies
   (equiv x y)
   (equal (fix x)
          (fix y))))


dag

(defun equiv-fn (term fix-fn equiv-macro define-fix-fn)
  (let (())
    `(encapsulate
         ()

       ,@(list (define-fix fix-fn))
       

       ;; (equal (fix ,lhs ,@moduli) (fix ,rhs ,@moduli))
       ;; (equivp x y moduli)

       (defmacro ,equiv (,lhs ,rhs &key (skip 'nil) ,@keyargs)
         `(equal (,',context-fn ,@(list ,@lhs-args--))
                 (if skip (skip-rewrite (,',fix-fn ,hyp ,@(list ,@args--)))
                   `(,',fix-fn ,hyp ,@(list ,@args--)))))
       
       )))

;; Sometimes we have an equivalence relation.  I don't think that
;; matters.

(defmacro def::equiv (term &key (equiv-macro 'nil) (context 'nil) (define-context 'nil))
  (equiv-fn term context equiv-macro define-context))


dag



- clean up nary
- similify the procedure
- consistency between 

(defun nary::unwrap-mod (term keys)
       )                        
       

;; Define a rewriting context for a "fixing" function.
(def::context (mod x n))

(defun mod-equivp (x y n)
  (equal (mod x n)
         (mod y n)))

(def::equiv (mod-equiv x y n))

(mod-equiv :lhs x
           :rhs z)

(defun unwrap-mod (newterm arg params)
  (cond
   ((equal (car term) 'fix)
    (if (not (equal (cadr term) arg))
        (ret t )
      (ret nil )))
   (t
    (if (not (equal newterm arg))
        (ret t )
      (ret nil )))))

(defun mod-equiv-check (newterm arg params)
  (equal (fix newterm params)
         (fix arg params)))


(mod-equiv-check (mod z v) z v)

(defun return-binding (unfix-success fixed-var value)
  (and unfix-success (acons fixed-var value nil)))

          

(defmacro bind-context (&rest args)
  )

(bind-context
 (equiv z (double-rewrite (term zed)))
 )

|#
