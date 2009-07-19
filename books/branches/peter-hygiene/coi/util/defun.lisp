#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "DEFUN")

(include-book "recursion-support")
(include-book "pseudo-translate")
(include-book "mv-nth")

(local
 (defthm true-listp-append
   (implies
    (true-listp y)
    (true-listp (append x y)))))

(defun local-suffix (name string)
  (declare (type symbol name)
	   (type string string))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name name) string) name))

(defthm symbolp-suffix
  (implies
   (and
    (stringp string)
    (symbolp symbol))
   (symbolp (local-suffix symbol string))))

(in-theory (disable local-suffix))

(defun contains-nil-alistp (alist)
  (declare (type (satisfies alistp) alist))
  (if (consp alist)
      (or (null (cdar alist))
	  (contains-nil-alistp (cdr alist)))
    nil))

(defun contains-nil (list)
  (declare (type t list))
  (if (consp list)
      (or (null (car list))
	  (contains-nil (cdr list)))
    nil))

(in-theory (disable function-declaration-p))
(in-theory (disable decompose-defun-body))

(defun defun-fn (disable name args body induction-defun)
  (declare (type symbol name)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies wf-defun-body) body)
	   (type (satisfies true-listp) induction-defun)
	   (type t args body))
  (met ((doc decls body) (decompose-defun-body body))
    (met ((typespec signature sig-hints decls) (extract-function-declaration decls))
      (met ((cong-hints decls) (extract-xarg-key-from-decls :congruence-hints decls))
	(met ((cong-specs decls) (extract-xarg-key-from-decls :congruence decls))
	  (let* ((verify-guards   (get-xarg-keys-from-decls :verify-guards decls))
		 (xarg-guards     (get-xarg-keys-from-decls :guard decls))
		 (xarg-mode       (get-xarg-keys-from-decls :mode  decls))
		 (guard-hints     (get-xarg-keys-from-decls :guard-hints decls))
		 (type-decls      (get-type-declarations-from-decls decls))
		 (not-inhibited   (not (contains-nil verify-guards)))
		 (verify-guards   (and not-inhibited (or signature verify-guards xarg-guards type-decls)))
		 (decls           (if signature 
				      (cons `(declare 
					      (xargs :guard 
						     ,(function-declaration-to-guard args signature))) decls)
				    decls))
		 (typespec        (or typespec signature))
		 (inhibited-decls (cons `(declare (xargs :verify-guards nil)) decls))
		 (name-induction  (symbol-fns::suffix name '-induction)))
	    
	    `(progn
	       
	       (defun ,name ,args
		 ,@(and doc (list doc))
		 ,@(if (or verify-guards (member-equal :program xarg-mode)) inhibited-decls decls)
		 ,body)
	       
	       ,@(and (member-equal :program xarg-mode)
		      `((skip-proofs (verify-termination ,name))))
	       
	       ,@(and typespec
		      (function-declaration-to-type-thm name args typespec sig-hints))

	       ,@(and verify-guards `((verify-guards ,name
						     ,@(and guard-hints `(:hints ,@guard-hints)))))
	       
	       ,@(and induction-defun cong-specs
		      `((encapsulate
			    ()
			  (set-ignore-ok :warn)
			  (set-irrelevant-formals-ok :warn)
			  
			  ,@induction-defun
			  
			  ,(congruence-induction-reduction-proof name-induction name args)
			  
			  )))
	       
	       ;; And here we can add congruence proofs ..
	       ,@(process-congruence-arguments name args cong-hints cong-specs induction-defun)
	       
	       ,@(and disable `((in-theory (disable ,name))))
	       
	       )))))))
    

(set-state-ok t)

(defun defun-fn-wrapper (disable name args body state)
  (declare (xargs :mode :program))
  (met ((doc decls xbody) (decompose-defun-body body))
    (met ((err tbody state) (acl2::pseudo-translate xbody state))
      (met ((case base) (lift-base (list name) tbody args))
	(declare (ignore base))
	(let ((event (if (not (equal case acl2::*nil*))
			 (let ((induction-defun (make-defun 'defun name args (make-defun-body doc decls tbody))))
			   (let ((induction-defun `(,(congruence-induction-function induction-defun))))
			     (defun-fn disable name args body induction-defun)))
		       (defun-fn disable name args body nil))))
	  (mv err event state))))))
      
(defmacro def::un (name args &rest body)
  `(make-event (defun-fn-wrapper nil ',name ',args ',body state)))

(defmacro def::und (name args &rest body)
  `(make-event (defun-fn-wrapper t ',name ',args ',body state)))

(defun signature-fn (fn argspec vals hints)
  (let ((args (symbol-fns::item-to-numbered-symbol-list 'acl2::x (len argspec))))
    (function-declaration-to-type-thm fn args `(function ,fn ,argspec ,@vals) hints)))

(defun extract-hints (args)
  (if (consp args)
      (let ((arg (car args)))
	(if (equal arg :hints) (mv (cadr args) nil)
	  (met ((hints args) (extract-hints (cdr args)))
	    (mv hints (cons arg args)))))
    (mv nil nil)))

(defmacro def::signature (fname args &rest vals)
  (met ((hints vals) (extract-hints vals))
    `(acl2::progn ,@(signature-fn fname args vals hints))))

(local
 (encapsulate
     ()
   
   (local
    (encapsulate
	()

      (def::un zed (a b)
	(declare (type integer a)
		 (type string b)

		 ;; The following assertion is really at the heart of
		 ;; what we are doing (for now) with def::un.
		 ;; Assertions such as this provide a short-hand
		 ;; notation allowing us to auto-generate type
		 ;; theorems about functions.

		 (function zed (integer string) integer string))
	(mv (+ a 1) b))
      
      ))

   ))

(local
 (encapsulate
     ()
   
   (local
    (encapsulate
	()

      (defund fred (x)
	(declare (type t x))
	(integerp x))

      (def::un zed (a b)
	(declare (xargs :signature ((fred string) fred string)
			:signature-hints (("Goal" :in-theory (enable fred)))
			:guard-hints (("Goal" :in-theory (enable fred)))))
	(mv (+ a 1) b))
      
      ))

   ))

(local
 (encapsulate
     ()

   (local
    (encapsulate
	()

      (defun equiv1 (x y) (equal x y))
      (defun equiv2 (x y) (equal x y))
      
      (defequiv equiv1)
      (defequiv equiv2)
      
      (def::un foo (x) 
	(declare (xargs :measure (len x)
			:congruence ((equiv1) equiv2)
			:congruence ((equiv2) equiv1)
			:congruence-hints (("Goal" :in-theory (current-theory :here)))))
	(if (consp x) (foo (cdr x)) (endp x)))
      
      ))
   ))

   