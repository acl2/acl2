;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "PATTERN")

;; Include the following in your .emacs file to provide
;; reasonable indenting for the pattern matching macro:
;;
;; (put 'pattern::match  'lisp-indent-hook 1)
;; (put 'match           'lisp-indent-hook 1)
;; (put 'pattern::match-with  'lisp-indent-hook 1)
;; (put 'match-with           'lisp-indent-hook 1)
;; (put 'pattern::let  'lisp-indent-hook 1)
;; (put 'pattern::let* 'lisp-indent-hook 1)

(include-book "coi/util/defun" :dir :system)
(include-book "coi/util/debug" :dir :system)

(defun self-evaluating-p (x)
  (declare (type t x))
  (or (acl2::quotep x)
      (acl2::acl2-numberp x)
      (acl2::stringp x)
      (eq x acl2::nil)
      (eq x acl2::t)
      (and (acl2::symbolp x)
           (equal (acl2::symbol-package-name x)
                  "KEYWORD"))))

(defun ignorep (x)
  (declare (type t x))
  (and (acl2::symbolp x)
       (acl2::let ((name (acl2::symbol-name x)))
         (or (equal name "_")
             (equal name "&")
             (equal name "*")))))

(defund binding-accessor (fn n)
  (declare (type symbol fn)
	   (type integer n))
  (if (equal fn 'acl2::list) `(acl2::lambda (x) (acl2::nth ,n x))
    (acl2::let ((pkg (acl2::symbol-package-name fn)))
      (symbol-fns::suffix '|| pkg "::" fn '- n))))

(defund pattern-recognizer (fn args)
  (declare (type symbol fn))
  (if (equal fn 'acl2::list) `(acl2::lambda (x) (and (acl2::true-listp x)
					       (acl2::equal (acl2::len x) 
							    ,(acl2::len args))))
    (acl2::let ((pkg (acl2::symbol-package-name fn)))
      (symbol-fns::suffix `|| pkg "::" fn '-p))))

(defun define-accessor-macros (fn n args nth)
  (declare (type symbol fn)
	   (type (integer 0 *) n))
  (if (consp args)
      (acl2::let ((acc (car args)))
        (acl2::let ((acc (if (ignorep acc) `(acl2::lambda (x) (,nth ,n x)) acc)))
          (acl2::let ((pmatch-acc (binding-accessor fn n)))
            (cons `(defmacro ,pmatch-acc (acl2::x)
                     `(,',acc ,acl2::x))
                  (define-accessor-macros fn (1+ n) (cdr args) nth)))))
    nil))

(defun pattern-fn (fn args type guard nth)
  (declare (type symbol fn)
	   (type (satisfies symbol-listp) args)
	   (acl2::ignore guard))
  (acl2::let ((type  (or type (symbol-fns::suffix fn '-p)))
	      (ptype (pattern-recognizer fn args)))
    `(encapsulate
	 ()
       ,@(define-accessor-macros fn 1 args nth)
       (defmacro ,ptype (acl2::x)
	 `(,',type ,acl2::x))
       )))

(defmacro def::pattern (fn args &key (type 'nil) (guard 'nil) (nth 'acl2::nth))
  (pattern-fn fn args type guard nth))

(local
 (defthm symbol-listp-implies
   (implies
    (and
     (symbol-listp list)
     (consp list))
    (and (symbolp (car list))
	 (symbol-listp (cdr list))))
   :rule-classes (:forward-chaining))
 )

(defun wf-rule-args (args)
  (declare (type t args))
  (if (consp args)
      (and (wf-rule-args (cdr args))
	   (acl2::let ((term (car args)))
	     (acl2::cond
	      ((self-evaluating-p term) t)
              ((ignorep term) t)
	      ((symbolp term) t)
	      ((consp term) (and (symbolp (car term))
				 (wf-rule-args (cdr term))))
	      (t nil))))
    (acl2::null args)))

;; --------------------------------

(defun wf-rule (list)
  (declare (type t list))
  (and (consp list)
       (symbolp (car list))
       (wf-rule-args (cdr list))))

(def::und rule-fn (rule)
  (declare (acl2::xargs :signature ((wf-rule) symbolp)))
  (car rule))

(def::und rule-args (rule)
  (declare (acl2::xargs :signature ((wf-rule) wf-rule-args)))
  (cdr rule))

(acl2::in-theory (acl2::disable wf-rule))

;; --------------------------------

(defun wf-rule-slot (x)
  (declare (type t x))
  (or (symbolp x)
      (wf-rule x)))

(acl2::in-theory (acl2::disable wf-rule-slot))

;; --------------------------------

(defun wf-pattern (pattern)
  (declare (type t pattern))
  (and (consp pattern)
       (true-listp (cdr pattern))
       (wf-rule-slot (car pattern))))

(defun wf-pattern-when (pattern)
  (declare (type t pattern))
  (and (consp pattern)
       ;; The default case doesn't need a 'when'
       (if (not (symbolp (car pattern)))
	   (and (consp (cdr pattern))
		(wf-rule-slot (car pattern))
		(true-listp (cddr pattern)))
	 t)))

(defun wf-pattern-guard (pattern)
  (declare (acl2::type t pattern))
  (or (wf-pattern pattern)
      (wf-pattern-when pattern)))

(def::un pattern-rule (pattern)
  (declare (acl2::type (satisfies wf-pattern-guard) pattern))
  (car pattern))

(def::signature pattern-rule (wf-pattern) wf-rule-slot)
(def::signature pattern-rule (wf-pattern-when) wf-rule-slot)

(defun wf-pattern-when-guard (pattern)
  (declare (acl2::type t pattern))
  (and (wf-pattern-when pattern)
       (not (symbolp (pattern-rule pattern)))))

(def::und pattern-body (pattern)
  (declare (acl2::xargs :signature ((wf-pattern) true-listp)))
  (cdr pattern))

(def::und pattern-when-body (pattern)
  (declare (acl2::xargs :signature ((wf-pattern-when-guard) true-listp)))
  (cddr pattern))

(def::und pattern-when-when (pattern)
  (declare (acl2::xargs :signature ((wf-pattern-when-guard) t)))
  (cadr pattern))

(acl2::in-theory (acl2::disable pattern-rule))

(acl2::in-theory (acl2::disable wf-pattern))
(acl2::in-theory (acl2::disable wf-pattern-when))

;; --------------------------------

(defund wf-let-pattern (pattern)
  (declare (type t pattern))
  (and (consp pattern)
       (wf-rule (car pattern))
       (consp (cdr pattern))
       (null (cddr pattern))))

(defthm wf-let-pattern-implies
  (implies
   (wf-let-pattern pattern)
   (and (consp pattern)
	(wf-rule (car pattern))
	(consp (cdr pattern))
	(null (cddr pattern))))
  :hints (("Goal" :in-theory (acl2::enable wf-let-pattern)))
  :rule-classes (:forward-chaining))

(defun wf-pbinding (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-let-pattern (car list))
	   (wf-pbinding (cdr list)))
    (null list)))

(defun rule-bindings (key base n args)
  (declare (type (satisfies symbol-listp) args)
	   (type symbol base)
	   (type integer n))
  (if (consp args)
      (cons `(,(car args) (,(binding-accessor base n) ,key))
	    (rule-bindings key base (1+ n) (cdr args)))
    nil))

;; --------------------------------

(defun more-pattern-args (args bound)
  (if (consp args)
      (or (not (symbolp (car args)))
	  (acl2::member-equal (car args) bound)
	  (more-pattern-args (cdr args) bound))
    nil))

(defun soft-alistp (list)
  (declare (type t list))
  (if (consp list)
      (and (consp (car list))
	   (consp (acl2::cdar list))
	   (soft-alistp (cdr list)))
    (null list)))

(defthm soft-alistp-implies-alistp
  (implies
   (soft-alistp x)
   (acl2::alistp x))
  :rule-classes (:forward-chaining))

(defthm consp-assoc
  (implies
   (and
    (acl2::assoc key alist)
    (soft-alistp alist))
   (and
    (consp (acl2::assoc key alist))
    (consp (cdr (acl2::assoc key alist)))))
  :rule-classes (:rewrite :forward-chaining))

(def::un recognize-pattern-args (key base n args pred bound)
  (declare (acl2::xargs :signature ((t symbol acl2::integerp wf-rule-args true-listp soft-alistp) true-listp soft-alistp)))
  (if (consp args)
      (met ((pred bound) (recognize-pattern-args key base (1+ n) (cdr args) pred bound))
	(acl2::let ((key `(,(binding-accessor base n) ,key)))
	  (acl2::let ((term (car args)))
	    (acl2::cond
	     ((self-evaluating-p term)
	      (acl2::mv (cons `(acl2::equal ,key ,term) pred) bound))
             ((ignorep term)
              (acl2::mv pred bound))
	     ((symbolp term)
	      (if (null term) (acl2::mv pred bound)
		  (acl2::let ((hit (acl2::assoc term bound)))
		    (if hit (acl2::mv (cons `(acl2::equal ,key ,(acl2::cadr hit)) pred) bound)
		      (acl2::let ((bound (acl2::acons term (list key) bound)))
			(acl2::mv pred bound))))))
	     ((consp term)
	      (acl2::let ((pred (cons `(,(pattern-recognizer (car term) (cdr term)) ,key) pred)))
		(recognize-pattern-args key (car term) 1 (cdr term) pred bound)))
	     (t
	      (acl2::mv (cons `(acl2::equal ,key ,term) pred) bound))))))
    (acl2::mv pred bound)))

(local
 (defthm true-listp-revappend
   (implies
    (true-listp y)
    (true-listp (acl2::revappend x y)))))

(defun any (x)
  (declare (type t x) (acl2::ignore x)) t)

(defun keys (alist)
  (declare (type (satisfies soft-alistp) alist))
  (if (endp alist) nil
    (cons (caar alist) (keys (cdr alist)))))

(def::un remove-key (key alist)
  (declare (acl2::xargs :signature ((t soft-alistp) soft-alistp)))
  (if (endp alist) nil
    (if (equal key (caar alist))
	(remove-key key (cdr alist))
      (cons (car alist) (remove-key key (cdr alist))))))

(def::un remove-keys (list alist)
  (declare (acl2::xargs :signature ((t soft-alistp) soft-alistp)))
  (if (consp list)
      (acl2::let ((alist (remove-key (car list) alist)))
        (remove-keys (cdr list) alist))
    alist))

(def::und recognize-pattern (deep prebound key term)
  (declare (acl2::xargs :signature ((t soft-alistp t wf-rule) any soft-alistp)))
  (acl2::let ((pred `(,(pattern-recognizer (rule-fn term) (rule-args term)) ,key)))
    (acl2::let ((preds (list pred)))
      (met ((preds bound) (recognize-pattern-args key (rule-fn term) 1 (rule-args term) preds prebound))
        (acl2::let ((bound (remove-keys (keys prebound) bound)))
          (acl2::mv (if deep `(acl2::and ,@(acl2::revappend preds nil)) pred) bound))))))

(defun implement-pattern (deep prebound key pattern)
  (declare (type (satisfies soft-alistp) prebound)
	   (type (satisfies wf-pattern) pattern))
  (acl2::let ((rule (pattern-rule pattern))
	      (body (pattern-body pattern)))
    (acl2::cond
     ((equal rule t) pattern)
     ((self-evaluating-p rule)
      `((equal ,key ,rule) ,@body))
     ((symbolp rule) pattern)
     (t
      (met ((pred bound) (recognize-pattern deep prebound key rule))
	`(,pred (acl2::let ,bound
		  ,@body)))))))
  
(acl2::mutual-recursion

 (defun get-variables-args (args)
   (declare (type t args))
   (if (not (consp args)) nil
     (acl2::append (get-variables (car args))
		   (get-variables-args (cdr args)))))
 
 (defun get-variables (term)
   (declare (type t term))
   (if (symbolp term) (list term)
     (if (not (consp term)) nil
       (if (equal (car term) 'quote) nil
	 (get-variables-args (cdr term))))))

 )

(def::un prune-bindings (vars bound)
  (declare (acl2::xargs :signature ((true-listp soft-alistp) soft-alistp)))
  (if (endp bound) nil
    (acl2::let ((entry (car bound)))
      (if (not (acl2::member-equal (car entry) vars)) (prune-bindings vars (cdr bound))
	(cons entry (prune-bindings vars (cdr bound)))))))

(defun implement-pattern-when (prebound key pattern)
  (declare (type (satisfies soft-alistp) prebound)
	   (type (satisfies wf-pattern-when) pattern))
  (acl2::let ((rule (pattern-rule pattern)))
    (if (symbolp rule) pattern
      (acl2::let ((body (pattern-when-body pattern))
		  (when (pattern-when-when pattern)))
	(met ((pred bound) (recognize-pattern t prebound key rule))
	  `((and ,pred 
		 (acl2::let ,(prune-bindings (get-variables when) bound)
		   ,when))
	    (acl2::let ,bound
	      ,@body)))))))

(def::und let-rule-bindings (key rule)
  (declare (acl2::xargs :signature ((t wf-rule) true-listp)))
  (met ((pred bound) (recognize-pattern nil nil key rule))
    (declare (acl2::ignore pred))
    bound))

(def::un let-pattern-bindings (pbinds)
  (declare (type (satisfies wf-pbinding) pbinds))
  (if (consp pbinds)
      (acl2::let ((pbind (car pbinds)))
	(acl2::let ((key  (cadr pbind))
		    (rule (car pbind)))
	  (acl2::revappend (let-rule-bindings key rule)
			   (let-pattern-bindings (cdr pbinds)))))
    nil))

(def::un let*-pattern-bindings (pbinds body)
  (declare (type (satisfies wf-pbinding) pbinds))
  (if (endp pbinds) body
    (acl2::let ((pbind (car pbinds)))
      (acl2::let ((key  (cadr pbind))
		  (rule (car pbind)))
	`(acl2::let ,(let-rule-bindings key rule)
	   (let-pattern-bindings (cdr pbinds) body))))))

(defmacro let* (pbinds body)
  (let*-pattern-bindings pbinds body))

(defmacro let (pbinds &rest args)
  `(acl2::let ,(let-pattern-bindings pbinds)
     ,@args))

(defun wf-pattern-body (body)
  (declare (type t body))
  (if (consp body)
      (and (wf-pattern (car body))
	   (wf-pattern-body (cdr body)))
    (null body)))

(defun implement-pattern-body-rec (deep bound key entry body)
  (declare (type (satisfies soft-alistp) bound)
	   (type (satisfies wf-pattern-body) body))
  (if (endp body) 
      (if (consp entry)
	  (if (and (symbolp (car entry))
		   (equal (acl2::symbol-name (car entry)) "T"))
	      (list entry)
	    (list (cons 't (cdr entry))))
	(list '(t nil)))
    (cons entry 
	  (acl2::let ((entry (implement-pattern deep bound key (car body))))
	    (implement-pattern-body-rec deep bound key entry (cdr body))))))

(defun wf-pattern-when-body (body)
  (declare (type t body))
  (if (consp body)
      (and (wf-pattern-when (car body))
	   (wf-pattern-when-body (cdr body)))
    (null body)))

(defun wf-pattern-body-guard (body)
  (declare (type t body))
  (if (consp body)
      (and (wf-pattern-guard (car body))
	   (wf-pattern-body-guard (cdr body)))
    (null body)))

(defthm wf-pattern-body-implies-wf-pattern-body-guard
  (implies
   (wf-pattern-body body)
   (wf-pattern-body-guard body))
  :rule-classes (:forward-chaining))

(defthm wf-pattern-when-body-implies-wf-pattern-body-guard
  (implies
   (wf-pattern-when-body body)
   (wf-pattern-body-guard body))
  :rule-classes (:forward-chaining))

(defun implement-pattern-when-body-rec (bound key entry body)
  (declare (type (satisfies soft-alistp) bound)
	   (type (satisfies wf-pattern-when-body) body))
  (if (endp body) 
      (if (consp entry)
	  (if (and (symbolp (car entry))
		   (equal (acl2::symbol-name (car entry)) "T"))
	      (list entry)
	    (list (cons 't (cdr entry))))
	(list '(t nil)))
    (cons entry 
	  (acl2::let ((entry (implement-pattern-when bound key (car body))))
	    (implement-pattern-when-body-rec bound key entry (cdr body))))))

(defun implement-pattern-body (deep bound key body)
  (declare (type (satisfies soft-alistp) bound)
	   (type (satisfies wf-pattern-body) body))
  (if (endp body) (list `(t nil))
    (acl2::let ((entry (implement-pattern deep bound key (car body))))
      (implement-pattern-body-rec deep bound key entry (cdr body)))))

(defun implement-pattern-when-body (bound key body)
  (declare (type (satisfies soft-alistp) bound)
	   (type (satisfies wf-pattern-when-body) body))
  (if (endp body) (list `(t nil))
    (acl2::let ((entry (implement-pattern-when bound key (car body))))
      (implement-pattern-when-body-rec bound key entry (cdr body)))))

(defun get-body-patterns (body)
  (declare (type (satisfies wf-pattern-body-guard) body))
  (if (endp body) nil
    (cons (pattern-rule (car body))
	  (get-body-patterns (cdr body)))))

(defun match-fn (deep bound key body)
  (declare (type (satisfies soft-alistp) bound)
	   (type (satisfies wf-pattern-body) body))
  `(acl2::cond
    ,@(implement-pattern-body deep bound key body)
    ))

(defun match-when-fn (bound key body)
  (declare (type (satisfies soft-alistp) bound)
	   (type (satisfies wf-pattern-when-body) body))
  `(acl2::cond
    ,@(implement-pattern-when-body bound key body)
    ))

(def::un self-soft-alist (list)
  (declare (acl2::xargs :signature ((t) soft-alistp)))
  (if (consp list)
      (cons (list (car list) (car list))
	    (self-soft-alist (cdr list)))
    nil))

(defmacro pattern::match (key &rest args)
  (match-fn t nil key args))

(defmacro pattern::match-with (key bound &rest args)
  (match-fn t (self-soft-alist bound) key args))

;; This variant tests only the top level pattern .. any nested
;; patterns become guard obligations.  Quoted constants should
;; not be used with this pattern.
(defmacro pattern::match! (key &rest args)
  (match-fn nil nil key args))

(defmacro match-when (key &rest args)
  (match-when-fn nil key args))

(defmacro match-with-when (key bound &rest args)
  (match-when-fn (self-soft-alist bound) key args))

;; We provide a ready made pattern for cons:

(def::pattern cons (car cdr)
  :type consp
  :guard consp)

;; and test it out ..

(local
 (defun test (x)
   (declare (type (satisfies acl2::integer-listp) x))
   (pattern::match x
    ;; Supports nested patterns .. with constants and duplicate values.
    ((cons (cons 3 x) (cons x q))
     (acl2::+ 3 (* 2 x) q))
    ((cons a b)
     (acl2::+ a (test b)))
    (t 0))))

(local
 (defun test2 (y x)
   (declare (type (satisfies acl2::integer-listp) x)
	    (type acl2::integer y))
   (pattern::match-with x (y)
     ((cons (cons 3 y) (cons x q))
      (acl2::+ 3 (* 2 x) q))
     ((cons a y)
      (acl2::+ a (test y)))
     (t 0))))

(local
 (defun test3 (x)
   (declare (type (satisfies acl2::integer-listp) x))
   (pattern::match-when x
    ;; Supports nested patterns .. with constants and duplicate values.
    ((cons (cons 3 x) (cons x q)) (equal x q)
     (acl2::+ 3 (* 2 x) q))
    ((cons a (cons b c)) (acl2::< a b)
     (acl2::+ a b (test c)))
    ((cons (cons a x) y) t
     (declare (acl2::ignore x))
     (acl2::+ a (test3 y)))
    (t 0))))

