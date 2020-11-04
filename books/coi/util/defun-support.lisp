; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.


(in-package "DEFUN")

(include-book "misc/beta-reduce" :dir :system)
(include-book "debug")
(include-book "../symbol-fns/symbol-fns")
(include-book "mv-nth")

;; ===================================================================
;;
;; It would be nice if ACL2 provided a better interface for all of
;; this.
;;
;; ===================================================================

;; ===================================================================
;;
;; decompose-defun-body:
;;
;; breaks up a defun body into components:
;;  :doc    A documentation string
;;  :decls  Declarations
;;  :body   The actual body of the function
;;
;; ===================================================================

(local
 (defthm true-listp-append-rewrite
   (implies
    (true-listp y)
    (true-listp (append x y)))))

(local
 (defthm true-listp-revappend
   (implies
    (true-listp y)
    (true-listp (revappend x y)))))

(defun declaration-p (decl)
  (declare (type t decl))
  (and (consp decl)
       (equal (car decl) 'declare)))
;; (consp (cdr decl))))

(defun declaration-listp (list)
  (declare (type t list))
  (if (consp list)
      (and (declaration-p (car list))
	   (declaration-listp (cdr list)))
    (null list)))

(defun wf-defun-subbody-rec (decl body)
  (declare (type t body))
  (if (consp body)
      (and (declaration-p decl) (wf-defun-subbody-rec (car body) (cdr body)))
    t))

(defun strip-decls-rec (body list)
  (declare (type t body list))
  (if (consp list)
      (met ((decls res) (strip-decls-rec (car list) (cdr list)))
	(mv (cons body decls) res))
    (mv nil body)))

(defthm declaration-listp-strip-decls-rec
  (implies
   (wf-defun-subbody-rec decl body)
   (declaration-listp (val 0 (strip-decls-rec decl body)))))

(defun strip-decls (list)
  (declare (type t list))
  (if (consp list)
      (strip-decls-rec (car list) (cdr list))
    (mv nil nil)))

(defun wf-defun-subbody (list)
  (declare (type t list))
  (if (consp list)
      (wf-defun-subbody-rec (car list) (cdr list))
    t))

(defthm declaration-listp-strip-decls
  (implies
   (wf-defun-subbody body)
   (declaration-listp (val 0 (strip-decls body)))))

(in-theory (disable strip-decls))

(defun wf-defun-body (body)
  (declare (type t body))
  (if (consp body)
      (if (stringp (car body))
	  (wf-defun-subbody (cdr body))
	(wf-defun-subbody body))
    nil))

(defun decompose-defun-body (body)
  (declare (type t body))
  (if (consp body)
      (if (stringp (car body))
	  (if (consp (cdr body))
	      (met ((decls sbody) (strip-decls (cdr body)))
		(mv (car body) decls sbody))
	    ;; Function is a constant string
	    (mv nil nil (car body)))
	(met ((decls body) (strip-decls body))
	  (mv nil decls body)))
    (mv nil nil body)))

(defthm declaration-listp-decompose-defun-body
  (implies
   (wf-defun-body body)
   (declaration-listp (val 1 (decompose-defun-body body)))))

(defun make-defun-body (doc decls body)
  (declare (xargs :guard (or (null doc) (stringp doc)))
	   (type (satisfies declaration-listp) decls))
  `(,@(and doc (list doc))
     ,@decls
     ,body))

(local
 (defthm car-append
   (equal (car (append x y))
	  (if (consp x)
	      (car x)
	    (car y)))))

(defthm wf-defun-body-make-defun-body-1
  (implies
   (and
    (null doc)
    (declaration-listp decls))
   (wf-defun-body (make-defun-body doc decls body))))

(defthm wf-defun-body-make-defun-body-2
  (implies
   (and
    (stringp doc)
    (declaration-listp decls))
   (wf-defun-body (make-defun-body doc decls body))))

(in-theory (disable make-defun-body))

(defun wf-defun (defun)
  (declare (type t defun))
  (and (consp defun)
       (symbolp (car defun))
       (consp (cdr defun))
       (symbolp (cadr defun))
       (consp (cddr defun))
       (symbol-listp (caddr defun))
       (wf-defun-body (cdddr defun))))

(defun defun-type (defun)
  (declare (type (satisfies wf-defun) defun))
  (car defun))

(defun defun-name (defun)
  (declare (type (satisfies wf-defun) defun))
  (cadr defun))

(defun defun-args (defun)
  (declare (type (satisfies wf-defun) defun))
  (caddr defun))

(defun defun-body (defun)
  (declare (type (satisfies wf-defun) defun))
  (cdddr defun))

(defund make-defun (type name args body)
  (declare (type (satisfies symbolp) type name)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies wf-defun-body) body))
  (cons type (cons name (cons args body))))

(local (in-theory (enable make-defun)))

(defthm make-defun-type
  (implies
   (and
    (symbolp type)
    (symbolp name)
    (symbol-listp args)
    (wf-defun-body body))
   (wf-defun (make-defun type name args body)))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((make-defun type name args body)))))

(defmacro update-defun (defun &key (type 'nil) (name 'nil) (args 'nil) (body 'nil))
  `(let ((defun ,defun))
     (let ((type ,(or type `(defun-type defun)))
	   (name ,(or name `(defun-name defun)))
	   (args ,(or args `(defun-args defun)))
	   (body ,(or body `(defun-body defun))))
       (make-defun type name args body))))

(defthm symbolp-defun-type
  (implies
   (wf-defun defun)
   (symbolp (defun-type defun))))

(defthm symbolp-defun-name
  (implies
   (wf-defun defun)
   (symbolp (defun-name defun))))

(defthm symbol-listp-defun-args
  (implies
   (wf-defun defun)
   (symbol-listp (defun-args defun))))

(local
 (defthm symbol-listp-implies-true-listp
   (implies
    (symbol-listp x)
    (true-listp x))))

(defthm wf-defun-body-defun-body
  (implies
   (wf-defun defun)
   (wf-defun-body (defun-body defun))))

(in-theory (disable defun-type defun-name defun-args defun-body))
(in-theory (disable wf-defun))
(in-theory (disable wf-defun-body))
(in-theory (disable decompose-defun-body))

(defun declaration-body (decl)
  (declare (type (satisfies declaration-p) decl))
  (cdr decl))

(defun signature-declaration-p (sig)
  (declare (type t sig))
  (and (consp sig)
       (true-listp (car sig))
       (consp (cdr sig))
       (true-listp (cdr sig))))

(defun function-declaration-p (body)
  (declare (type t body))
  (and (consp body)
       (equal (car body) 'function)
       (consp (cdr body))
       (signature-declaration-p (cddr body))))

(defun function-declaration (name args values)
  (declare (type t args values))
  `(function ,name ,args ,@values))

(defthm function-declaration-p-function-declaration
  (implies
   (and
    (true-listp args)
    (true-listp values)
    (force (consp values)))
   (function-declaration-p (function-declaration name args values))))

(in-theory (disable function-declaration))

(defund signature-to-declaration (sig)
  (declare (type t sig))
  (cons 'function (cons 'function sig)))

(defthm function-declaration-p-signature-to-declaration
  (implies
   (signature-declaration-p sig)
   (function-declaration-p (signature-to-declaration sig)))
  :hints (("Goal" :in-theory (enable signature-to-declaration))))

(defun function-declaration-args (decl)
  (declare (type (satisfies function-declaration-p) decl))
  (caddr decl))

(defun function-declaration-vals (decl)
  (declare (type (satisfies function-declaration-p) decl))
  (cdddr decl))

(defthm consp-function-declaration-vals
  (implies
   (function-declaration-p decl)
   (consp (function-declaration-vals decl))))

(defun xarg-p (decl)
  (declare (type t decl))
  (and (consp decl)
       (equal (car decl) 'xargs)))

(defun xarg-body (decl)
  (declare (type (satisfies xarg-p) decl))
  (cdr decl))

(defun get-xarg-key-from-body (key body)
  (declare (type t body))
  (if (and (consp body)
	   (consp (cdr body)))
      (let ((entry (car body)))
	(if (equal key entry)
	    (cons (cadr body) (get-xarg-key-from-body key (cddr body)))
	  (get-xarg-key-from-body key (cddr body))))
    nil))

(defthm true-listp-get-xarg-key-from-body
  (true-listp (get-xarg-key-from-body key body)))

(defun extract-xarg-key-from-body-rec (key body hit res)
  (declare (type t body))
  (if (and (consp body)
	   (consp (cdr body)))
      (let ((entry (car body))
	    (value (cadr body)))
	(if (equal key entry)
	    (extract-xarg-key-from-body-rec key (cddr body) (cons value hit) res)
	  (extract-xarg-key-from-body-rec key (cddr body) hit (cons entry (cons value res)))))
    (mv hit res)))

(defthm true-listp-extract-xarg-key-from-body-rec
  (implies
   (and
    (true-listp hit)
    (true-listp res))
   (and (true-listp (acl2::val 0 (extract-xarg-key-from-body-rec key body hit res)))
	(true-listp (acl2::val 1 (extract-xarg-key-from-body-rec key body hit res))))))

(defun extract-xarg-key-from-body (key body)
  (declare (type t body))
  (extract-xarg-key-from-body-rec key body nil nil))

(defthm declaration-listp-revappend
  (implies
   (and
    (declaration-listp x)
    (declaration-listp y))
   (declaration-listp (revappend x y))))

(defun extract-key-from-xarg-bodies (key list value res)
  (declare (type (satisfies true-listp) res))
  (if (consp list)
      (let ((decl (car list)))
	(if (xarg-p decl)
	    (met ((value xbody) (extract-xarg-key-from-body-rec key (xarg-body decl) value nil))
	      (let ((xarg (cons 'xargs xbody)))
		(extract-key-from-xarg-bodies key (cdr list) value (cons xarg res))))
	  (extract-key-from-xarg-bodies key (cdr list) value (cons decl res))))
    (mv value (revappend res nil))))

(defthm true-listp-extract-key-from-xarg-bodies
  (implies
   (true-listp value)
   (true-listp (acl2::val 0 (extract-key-from-xarg-bodies key list value res)))))

(defun extract-key-from-xarg-decls-rec (key decls value res)
  (declare (type (satisfies declaration-listp) decls)
	   (type (satisfies true-listp) value res))
  (if (consp decls)
      (met ((value decl) (extract-key-from-xarg-bodies key (cdar decls) value nil))
	(extract-key-from-xarg-decls-rec key (cdr decls) value (cons (cons 'declare decl) res)))
    (mv value (revappend res nil))))

(defthm declaration-listp-extract-key-from-xarg-decls-rec
  (implies
   (and
    (declaration-listp decls)
    (declaration-listp res))
   (declaration-listp (acl2::val 1 (extract-key-from-xarg-decls-rec key decls value res)))))

(defthm true-listp-extract-key-from-xarg-decls-rec-1
  (implies
   (true-listp res)
   (true-listp (acl2::val 1 (extract-key-from-xarg-decls-rec key decls value res)))))

(defthm true-listp-extract-key-from-xarg-decls-rec-0
  (implies
   (true-listp value)
   (true-listp (acl2::val 0 (extract-key-from-xarg-decls-rec key decls value res)))))

;; These functions should be refactored and renamed

(defun extract-xarg-key-from-decls (key decls)
  (declare (type (satisfies declaration-listp) decls))
  (extract-key-from-xarg-decls-rec key decls nil nil))

#+joe
(defthm eqlable-alistp-get-xarg-key-from-body
  (implies
   (eqlablep key)
   (eqlable-alistp (get-xarg-key-from-body key body)))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((get-xarg-key-from-body key body)))))

(defun get-xarg-keys-from-body (key body)
  (declare (type t body))
  (if (consp body)
      (let ((decl (car body)))
	(if (xarg-p decl)
	    (let ((hit (get-xarg-key-from-body key (xarg-body decl))))
	      (append hit (get-xarg-keys-from-body key (cdr body))))
	  (get-xarg-keys-from-body key (cdr body))))
    nil))

(defthm true-listp-get-xarg-keys-from-body
  (true-listp (get-xarg-keys-from-body key body)))

(defun get-xarg-keys-from-decls (key decls)
  (declare (type (satisfies declaration-listp) decls))
  (if (consp decls)
      (append (get-xarg-keys-from-body key (declaration-body (car decls)))
	      (get-xarg-keys-from-decls key (cdr decls)))
    nil))

(defthm true-listp-get-xarg-keys-from-decls
  (true-listp (get-xarg-keys-from-decls key decls)))

(defun type-declaration (body)
  (declare (type t body))
  (and (consp body)
       (equal (car body) 'type)))

(defun get-type-declarations-from-body (body)
  (declare (type t body))
  (if (consp body)
      (let ((decl (car body)))
	(if (type-declaration decl)
	    (cons decl (get-type-declarations-from-body (cdr body)))
	  (get-type-declarations-from-body (cdr body))))
    nil))

(defun get-type-declarations-from-decls (decls)
  (declare (type (satisfies declaration-listp) decls))
  (if (consp decls)
      (append (get-type-declarations-from-body (declaration-body (car decls)))
	      (get-type-declarations-from-decls (cdr decls)))
    nil))

;; declarations can be doubly nested ..

(defun extract-function-declaration-from-body-rec (body declaration signature sig-hints res)
  (declare (type t body))
  (if (consp body)
      (let ((decl (car body)))
	(cond
	 ((function-declaration-p decl)
	  (let ((declaration (coi-debug::assert (null declaration) :value decl :message "Multiple Function Declarations")))
	    (extract-function-declaration-from-body-rec (cdr body) declaration signature sig-hints res)))
	 ((xarg-p decl)
	  (met ((signature xbody) (extract-xarg-key-from-body-rec :signature (xarg-body decl) signature nil))
	    (met ((sig-hints xbody) (extract-xarg-key-from-body-rec :signature-hints xbody sig-hints nil))
	      (let ((xarg (cons 'xargs xbody)))
		(extract-function-declaration-from-body-rec (cdr body) declaration signature sig-hints (cons xarg res))))))
	 (t
	  (extract-function-declaration-from-body-rec (cdr body) declaration signature sig-hints (cons decl res)))))
    (mv declaration signature sig-hints res)))

(defthm true-listp-val-3-extract-function-declaration-from-body-rec
  (implies
   (true-listp res)
   (true-listp (val 3 (extract-function-declaration-from-body-rec body declaration signature sig-hints res)))))

(defund extract-function-declaration-from-body (body)
  (declare (type t body))
  (extract-function-declaration-from-body-rec body nil nil nil nil))

(defun extract-function-declaration-rec (decls declaration signature sig-hints res)
  (declare (type (satisfies declaration-listp) decls))
  (if (consp decls)
      (let ((decl (car decls)))
	(met ((declaration signature sig-hints body)
	      (extract-function-declaration-from-body-rec (declaration-body decl) declaration signature sig-hints nil))
	  (let ((res (cons (cons 'declare (revappend body nil)) res)))
	    (extract-function-declaration-rec (cdr decls) declaration signature sig-hints res))))
    (mv declaration signature sig-hints res)))

(defthm true-listp-val-3-extract-function-declaration-rec
  (implies
   (true-listp res)
   (true-listp (val 3 (extract-function-declaration-rec decls declaration signature sig-hints res)))))

(defthm declaration-listp-val-3-extract-function-declaration-rec
  (implies
   (declaration-listp res)
   (declaration-listp (val 3 (extract-function-declaration-rec decls declaration signature sig-hints res)))))

(defun extract-function-declaration (decls)
  (declare (type (satisfies declaration-listp) decls))
  (met ((declaration signature sig-hints decls) (extract-function-declaration-rec decls nil nil nil nil))
    (met ((fty-sig decls) (extract-xarg-key-from-decls :fty decls))
      (let ((signature (and (consp signature)
                            (coi-debug::assert (and (< (len signature) 2)
                                                    (signature-declaration-p (car signature))
                                                    (not declaration))
                                               :message "Malformed/Multiple signature specification(s)")
                            (signature-to-declaration (car signature))))
            (fty-sig   (and (consp fty-sig)
                            (coi-debug::assert (and (< (len fty-sig) 2)
                                                    (signature-declaration-p (car fty-sig))
                                                    (not declaration))
                                               :message "Malformed/Multiple fty signature specification(s)")
                            (signature-to-declaration (car fty-sig))))
            (sig-hints (and (consp sig-hints)
                            (coi-debug::assert (< (len signature) 2) :value (car sig-hints)
                                               :message "Multiple :sig-hints Bindings")))
            (declaration (if (and declaration
                                  (coi-debug::assert (function-declaration-p declaration)
                                                     :message "Malformed function declaration"))
                             declaration
                           nil))
            (decls (revappend decls nil)))
        (mv declaration signature fty-sig sig-hints decls)))))

(defthm function-declaration-p-val-0-extract-function-declaration
  (implies
   (val 0 (extract-function-declaration decls))
   (function-declaration-p (val 0 (extract-function-declaration decls))))
  :rule-classes (:forward-chaining))

(defthm function-declaration-p-val-1-extract-function-declaration
  (implies
   (val 1 (extract-function-declaration decls))
   (function-declaration-p (val 1 (extract-function-declaration decls))))
  :rule-classes (:forward-chaining))

(defthm function-declaration-p-val-2-extract-function-declaration
  (implies
   (val 2 (extract-function-declaration decls))
   (function-declaration-p (val 2 (extract-function-declaration decls))))
  :rule-classes (:forward-chaining))

(defthm true-listp-val-4-extract-function-declaration
  (true-listp (val 4 (extract-function-declaration decls))))

(defthm declaration-listp-revappend
  (implies
   (and
    (declaration-listp x)
    (declaration-listp y))
   (declaration-listp (revappend x y))))

(defthm declaration-listp-val-4-extract-function-declaration
  (implies
   (declaration-listp decls)
   (declaration-listp (val 4 (extract-function-declaration decls)))))

(in-theory (disable extract-function-declaration))

;; ===================================================================
;;
;; These functions are from ACL2 itself .. minus the annoying
;; dependency on world and :program mode.
;;
;; ===================================================================

(defun translate-declaration-to-guard/integer (lo var hi)
  (declare (type t lo))
  (let
   ((lower-bound (cond ((integerp lo) lo)
		       ((eq lo 'acl2::*) 'acl2::*)
		       ((and (consp lo)
			     (integerp (car lo))
			     (null (cdr lo)))
			(1+ (car lo)))
		       (t nil)))
    (upper-bound (cond ((integerp hi) hi)
		       ((eq hi 'acl2::*) 'acl2::*)
		       ((and (consp hi)
			     (integerp (car hi))
			     (null (cdr hi)))
			(1- (car hi)))
		       (t nil))))
   (cond
    ((and upper-bound lower-bound)
     (cond ((eq lower-bound 'acl2::*)
	    (cond ((eq upper-bound 'acl2::*)
		   (list 'acl2::integerp var))
		  (t (list 'acl2::and
			   (list 'acl2::integerp var)
			   (list 'acl2::<= var upper-bound)))))
	   (t (cond ((eq upper-bound 'acl2::*)
		     (list 'acl2::and
			   (list 'acl2::integerp var)
			   (list 'acl2::<= lower-bound var)))
		    (t (list 'acl2::and
			     (list 'acl2::integerp var)
			     (list 'acl2::<= lower-bound var)
			     (list 'acl2::<= var upper-bound)))))))
    (t nil))))



(defun unary-lambda-function (x)
  (declare (type t x))
  (and (true-listp x)
       (equal (length x) 3)
       (EQ (CAR X) 'acl2::LAMBDA)
       (SYMBOL-LISTP (CADR X))
       (PSEUDO-TERMP (CADDR X))
       (EQUAL (LENGTH (CADR X)) 1)))

(defthm unary-lambda-implies-lambda-expr-p
  (implies
   (unary-lambda-function x)
   (acl2::lambda-expr-p (list x a))))

(encapsulate
    ()

  ;; Lambda application stuff .. perhaps this should get its own book
  ;; along with rules for reasoning about pseudo-termp stuff ..
  ;;
  ;; ((lambda (x y z) body) args)

  (local (in-theory (enable acl2::lambda-expr-p)))

  (defund lambda-formals (lambda)
    (declare (type (satisfies acl2::lambda-expr-p) lambda))
    (cadr (car lambda)))

  (defund lambda-body (lambda)
    (declare (type (satisfies acl2::lambda-expr-p) lambda))
    (caddr (car lambda)))

  (defund lambda-args (lambda)
    (declare (type (satisfies acl2::lambda-expr-p) lambda))
    (cdr lambda))

  (defund make-lambda-application (formals body args)
    (declare (type t formals body args))
    (cons `(lambda ,formals ,body) args))

  (local (in-theory (enable lambda-formals lambda-body lambda-args make-lambda-application)))

  (defthm pseudo-termp-make-lambda-application
    (implies
     (and
      (symbol-listp formals)
      (pseudo-term-listp args)
      (equal (len formals) (len args))
      (pseudo-termp body))
     (and (pseudo-termp (make-lambda-application formals body args))
	  (acl2::lambda-expr-p (make-lambda-application formals body args))))
    :rule-classes (:rewrite
		   (:forward-chaining
		    :trigger-terms ((make-lambda-application formals body args)))))

  (defthm symbol-listp-lambda-formals
    (implies
     (and
      (pseudo-termp lambda)
      (acl2::lambda-expr-p lambda))
     (symbol-listp (lambda-formals lambda)))
    :rule-classes (:rewrite
		   (:forward-chaining
		    :trigger-terms ((lambda-formals lambda)))))

  (defthm pseudo-term-listp-lambda-args
    (implies
     (and
      (pseudo-termp lambda)
      (acl2::lambda-expr-p lambda))
     (pseudo-term-listp (lambda-args lambda)))
    :rule-classes (:rewrite
		   (:forward-chaining
		    :trigger-terms ((lambda-args lambda)))))

  (defthm pseudo-termp-lambda-body
    (implies
     (and
      (pseudo-termp lambda)
      (acl2::lambda-expr-p lambda))
     (pseudo-termp (lambda-body lambda)))
    :rule-classes (:rewrite
		   (:forward-chaining
		    :trigger-terms ((lambda-body lambda)))))

  (defthm lambda-body-measure
    (implies
     (acl2::lambda-expr-p lambda)
     (< (acl2-count (lambda-body lambda))
	(acl2-count lambda)))
    :rule-classes (:linear :forward-chaining))

  (defthm lambda-formals-measure
    (implies
     (acl2::lambda-expr-p lambda)
     (< (acl2-count (lambda-formals lambda))
	(acl2-count lambda)))
    :rule-classes (:linear :forward-chaining))

  (defthm lambda-args-measure
    (implies
     (acl2::lambda-expr-p lambda)
     (< (acl2-count (lambda-args lambda))
	(acl2-count lambda)))
    :rule-classes (:linear :forward-chaining))


  )

;; DAG -- ugh! How many times do I do this??
;;
(defun memberx (a x)
  (declare (type t x))
  (if (consp x)
      (or (equal a (car x))
	  (memberx a (cdr x)))
    nil))

(defun revappendx (x y)
  (declare (type t x))
  (if (consp x)
      (revappendx (cdr x) (cons (car x) y))
    y))

(defthm len-revappendx
  (equal (len (revappendx x y))
	 (+ (len x) (len y))))

(defthm true-listp-revappendx
  (equal (true-listp (revappendx x y))
	 (true-listp y)))

(defthm symbol-listp-revappendx
  (implies
   (and
    (symbol-listp x)
    (symbol-listp y))
   (symbol-listp (revappendx x y))))

(defthm pseudo-term-listp-revappendx
  (implies
   (and
    (pseudo-term-listp x)
    (pseudo-term-listp y))
   (pseudo-term-listp (revappendx x y))))

(mutual-recursion

 (defun collect-free-variables (bound term res)
   (declare (xargs :measure (acl2-count term)))
   (declare (type t term))
   (if (consp term)
       (cond
	((equal (car term) 'acl2::quote)
	 res)
	((symbolp (car term))
	 (collect-free-variables-args bound (cdr term) res))
	((acl2::lambda-expr-p term)
	 (let ((res (collect-free-variables (revappendx (lambda-formals term) bound) (lambda-body term) res)))
	   (collect-free-variables-args bound (lambda-args term) res)))
	(t res))
     (if (symbolp term)
	 (if (or (memberx term bound)
		 (memberx term res)) res
	   (cons term res))
       res)))

 (defun collect-free-variables-args (bound args res)
   (declare (xargs :measure (acl2-count args)))
   (declare (type t args))
   (if (consp args)
       (let ((res (collect-free-variables bound (car args) res)))
	 (collect-free-variables-args bound (cdr args) res))
     res))

 )

(defund promote-free-variables (lambda)
  (declare (type (satisfies acl2::lambda-expr-p) lambda))
  (let ((body    (lambda-body lambda))
	(args    (lambda-args lambda))
	(formals (lambda-formals lambda)))
    (let ((vars (collect-free-variables formals body nil)))
      (if (symbol-listp vars)
	  (make-lambda-application (revappendx vars formals) body (revappendx vars args))
	lambda))))

(defthm lambda-expr-p-promote-free-variables
  (implies
   (acl2::lambda-expr-p lambda)
   (acl2::lambda-expr-p (promote-free-variables lambda)))
  :hints (("Goal" :in-theory (enable make-lambda-application promote-free-variables))))

(defthm lambda-formals-args-len-equal
  (IMPLIES (AND (ACL2::LAMBDA-EXPR-P LAMBDA)
		(PSEUDO-TERMP LAMBDA))
	   (EQUAL (LEN (LAMBDA-FORMALS LAMBDA))
		  (LEN (LAMBDA-ARGS LAMBDA))))
  :hints (("Goal" :in-theory (enable LAMBDA-FORMALS LAMBDA-ARGS))))

(defthm symbol-listp-is-pseudo-term-listp
  (implies
   (symbol-listp x)
   (pseudo-term-listp x)))

(defthm pseudo-term-listp-implies-true-listp
  (implies
   (pseudo-term-listp x)
   (true-listp x))
  :rule-classes (:forward-chaining))

(local (in-theory (disable acl2::lambda-expr-p)))

(defthm pseudo-termp-promote-free-variables
  (implies
   (and
    (acl2::lambda-expr-p lambda)
    (pseudo-termp lambda))
   (pseudo-termp (promote-free-variables lambda)))
  :hints (("Goal" :in-theory (enable make-lambda-application promote-free-variables))))

(defthm equal-common-plus-reduction
  (implies
   (and
    (integerp a)
    (integerp b)
    (integerp c))
   (equal (equal (+ a b) (+ c b))
	  (equal a c))))



(defun translate-declaration-to-guard1 (x var)
  (declare (type t x))
  (cond
   ((or (eq x 'acl2::integer) (eq x 'acl2::signed-byte))
    (list 'acl2::integerp var))
   ((and (consp x)
	 (eq (car x) 'acl2::integer)
	 (true-listp x)
	 (equal (length x) 3))
    (translate-declaration-to-guard/integer (cadr x)
					    var (caddr x)))
   ((eq x 'acl2::rational) (list 'acl2::rationalp var))
   ((eq x 'acl2::real)
    (list 'acl2::real/rationalp var))
   ((eq x 'acl2::complex)
    (list 'acl2::complex/complex-rationalp var))
   ((and (consp x)
	 (eq (car x) 'acl2::rational)
	 (true-listp x)
	 (equal (length x) 3))
    (let
     ((lower-bound (cond ((rationalp (cadr x)) (cadr x))
			 ((eq (cadr x) 'acl2::*) 'acl2::*)
			 ((and (consp (cadr x))
			       (rationalp (car (cadr x)))
			       (null (cdr (cadr x))))
			  (list (car (cadr x))))
			 (t nil)))
      (upper-bound (cond ((rationalp (caddr x)) (caddr x))
			 ((eq (caddr x) 'acl2::*) 'acl2::*)
			 ((and (consp (caddr x))
			       (rationalp (car (caddr x)))
			       (null (cdr (caddr x))))
			  (list (car (caddr x))))
			 (t nil))))
     (cond
      ((and upper-bound lower-bound)
       (cond
	((eq lower-bound 'acl2::*)
	 (cond ((eq upper-bound 'acl2::*)
		(list 'acl2::rationalp var))
	       (t (list 'acl2::and
			(list 'acl2::rationalp var)
			(cond ((consp upper-bound)
			       (list 'acl2::< var (car upper-bound)))
			      (t (list 'acl2::<= var upper-bound)))))))
	(t
	 (cond
	  ((eq upper-bound 'acl2::*)
	   (list 'acl2::and
		 (list 'acl2::rationalp var)
		 (cond ((consp lower-bound)
			(list 'acl2::< (car lower-bound) var))
		       (t (list 'acl2::<= lower-bound var)))))
	  (t (list 'acl2::and
		   (list 'acl2::rationalp var)
		   (cond ((consp lower-bound)
			  (list 'acl2::< (car lower-bound) var))
			 (t (list 'acl2::<= lower-bound var)))
		   (cond ((consp upper-bound)
			  (list 'acl2::> (car upper-bound) var))
			 (t (list 'acl2::<= var upper-bound)))))))))
      (t nil))))
   ((and (consp x)
	 (eq (car x) 'acl2::real)
	 (true-listp x)
	 (equal (length x) 3))
    (let
     ((lower-bound (cond ((real/rationalp (cadr x)) (cadr x))
			 ((eq (cadr x) 'acl2::*) 'acl2::*)
			 ((and (consp (cadr x))
			       (real/rationalp (car (cadr x)))
			       (null (cdr (cadr x))))
			  (list (car (cadr x))))
			 (t nil)))
      (upper-bound (cond ((real/rationalp (caddr x)) (caddr x))
			 ((eq (caddr x) 'acl2::*) 'acl2::*)
			 ((and (consp (caddr x))
			       (real/rationalp (car (caddr x)))
			       (null (cdr (caddr x))))
			  (list (car (caddr x))))
			 (t nil))))
     (cond
      ((and upper-bound lower-bound)
       (cond
	((eq lower-bound 'acl2::*)
	 (cond ((eq upper-bound 'acl2::*)
		(list 'acl2::real/rationalp var))
	       (t (list 'acl2::and
			(list 'acl2::real/rationalp var)
			(cond ((consp upper-bound)
			       (list 'acl2::< var (car upper-bound)))
			      (t (list 'acl2::<= var upper-bound)))))))
	(t
	 (cond
	  ((eq upper-bound 'acl2::*)
	   (list 'acl2::and
		 (list 'acl2::real/rationalp var)
		 (cond ((consp lower-bound)
			(list 'acl2::< (car lower-bound) var))
		       (t (list 'acl2::<= lower-bound var)))))
	  (t (list 'acl2::and
		   (list 'acl2::real/rationalp var)
		   (cond ((consp lower-bound)
			  (list 'acl2::< (car lower-bound) var))
			 (t (list 'acl2::<= lower-bound var)))
		   (cond ((consp upper-bound)
			  (list 'acl2::> (car upper-bound) var))
			 (t (list 'acl2::<= var upper-bound)))))))))
      (t nil))))
   ((eq x 'acl2::bit)
    (list 'acl2::or
	  (list 'acl2::equal var 1)
	  (list 'acl2::equal var 0)))
   ((and (consp x)
	 (eq (car x) 'acl2::mod)
	 (true-listp x)
	 (equal (length x) 2)
	 (integerp (cadr x)))
    (translate-declaration-to-guard/integer 0 var (1- (cadr x))))
   ((and (consp x)
	 (eq (car x) 'acl2::signed-byte)
	 (true-listp x)
	 (equal (length x) 2)
	 (integerp (cadr x))
	 (> (cadr x) 0))
    (list 'acl2::signed-byte-p (cadr x) var))
   ((eq x 'acl2::unsigned-byte)
    (translate-declaration-to-guard/integer 0 var 'acl2::*))
   ((and (consp x)
	 (eq (car x) 'acl2::unsigned-byte)
	 (true-listp x)
	 (equal (length x) 2)
	 (integerp (cadr x))
	 (> (cadr x) 0))
    (list 'acl2::unsigned-byte-p (cadr x) var))
   ((eq x 'acl2::atom) (list 'acl2::atom var))
   ((eq x 'acl2::character)
    (list 'acl2::characterp var))
   ((eq x 'acl2::cons) (list 'acl2::consp var))
   ((eq x 'acl2::list) (list 'acl2::listp var))
   ((eq x 'acl2::nil) ''acl2::nil)
   ((eq x 'acl2::null) (list 'acl2::eq var nil))
   ((eq x 'acl2::ratio)
    (list 'acl2::and
	  (list 'acl2::rationalp var)
	  (list 'acl2::not (list 'acl2::integerp var))))
   ((eq x 'acl2::standard-char)
    (list 'acl2::standard-charp var))
   ((eq x 'acl2::string) (list 'acl2::stringp var))
   ((and (consp x)
	 (eq (car x) 'acl2::string)
	 (true-listp x)
	 (equal (length x) 2)
	 (integerp (cadr x))
	 (>= (cadr x) 0))
    (list 'acl2::and
	  (list 'acl2::stringp var)
	  (list 'acl2::equal
		(list 'acl2::length var)
		(cadr x))))
   ((eq x 'acl2::symbol) (list 'acl2::symbolp var))
   ((eq x 'acl2::t) acl2::t)
   ((and (consp x)
	 (eq (car x) 'acl2::satisfies)
	 (true-listp x)
	 (equal (length x) 2)
	 (symbolp (cadr x))
	 )
    (list (cadr x) var))
   ((and (consp x)
	 (eq (car x) 'acl2::member)
	 (eqlable-listp (cdr x)))
    (list 'acl2::member
	  var (list 'acl2::quote (cdr x))))

   ((and (unary-lambda-function x) (pseudo-termp var))
    (acl2::beta-reduce-lambda-expr (promote-free-variables (list x var))))

   ((symbolp x)
    (list x var))

   (t x)

   ))

(mutual-recursion

 (defun translate-declaration-to-guard (x var)
   (declare (type t x var))
   (cond
    ((atom x)
     (translate-declaration-to-guard1 x var))
    ((eq (car x) 'acl2::not)
     (cond
      ((and (true-listp x)
	    (equal (length x) 2))
       (let ((term (translate-declaration-to-guard (cadr x)
						   var)))
	    (and term (list 'acl2::not term))))
      (t nil)))
    ((eq (car x) 'acl2::and)
     (cond
      ((true-listp x)
       (cond
	((null (cdr x)) t)
	(t
	 (let
	  ((args (translate-declaration-to-guard-lst (cdr x)
						     var)))
	  (cond (args (cons 'acl2::and args))
		(t nil))))))
      (t nil)))
    ((eq (car x) 'acl2::or)
     (cond
      ((true-listp x)
       (cond
	((null (cdr x)) ''acl2::nil)
	(t
	 (let
	  ((args (translate-declaration-to-guard-lst (cdr x)
						     var)))
	  (cond (args (cons 'acl2::or args))
		(t nil))))))
      (t nil)))
    ((eq (car x) 'acl2::complex)
     (cond
      ((and (consp (cdr x)) (null (cddr x)))
       (list 'acl2::and
	     (list 'acl2::complex/complex-rationalp var)
	     (translate-declaration-to-guard (cadr x)
					     (list 'acl2::realpart var)
					    )
	     (translate-declaration-to-guard (cadr x)
					     (list 'acl2::imagpart var)
					    )))
      (t nil)))
    (t (translate-declaration-to-guard1 x var))))
 (defun translate-declaration-to-guard-lst (l var)
   (declare (type t l var))
   (and
    (consp l)
    (let ((frst (translate-declaration-to-guard (car l) var)))
      (cond
       ((null frst) nil)
       ((atom (cdr l)) (list frst))
       (t
	(let ((rst (translate-declaration-to-guard-lst (cdr l)
						       var)))
	  (cond ((null rst) nil)
		(t (cons frst rst)))))))))
 )

(defund extract-fapp-from-declaration (x)
  (declare (type t x))
  (let ((guard (translate-declaration-to-guard x 'var)))
    (if (consp guard) (car guard)
      nil)))

(defund translate-declaration-to-guard-list (x var)
  (declare (type t x var))
  (let ((guard (translate-declaration-to-guard x var)))
    (if (symbolp guard) nil
      (list guard))))

(defthm true-listp-translate-declaration-to-guard-list
  (true-listp (translate-declaration-to-guard-list x var)))

(defun merge-type-decl-fn-names (arg-types)
  (declare (type t arg-types))
  (if (consp arg-types)
      (let ((fn (extract-fapp-from-declaration (car arg-types))))
	(let ((fn (or fn 't)))
	  (let ((pkg (symbol-fns::to-symbol-in-package-of fn fn)))
	    (symbol-fns::join-symbols pkg fn `- (merge-type-decl-fn-names (cdr arg-types))))))
    '||))

(defun map-arg-types-over-args (arg-types args)
  (declare (type t arg-types args))
  (if (and (consp arg-types)
	   (consp args))
      (append (translate-declaration-to-guard-list (car arg-types) (car args))
	      (map-arg-types-over-args (cdr arg-types) (cdr args)))
    (coi-debug::assert (equal (consp arg-types) (consp args)) :value 'nil
		   :message "Function signature and argument list differ in length")))

(defthm true-listp-map-arg-types-over-args
  (true-listp (map-arg-types-over-args arg-types args)))

(defun map-type-declaration-over-vars (predicate vars)
  (declare (type t predicate vars))
  (if (consp vars)
      (cons (translate-declaration-to-guard predicate (car vars))
            (map-type-declaration-over-vars predicate (cdr vars)))
    nil))

(defund type-declaration-to-predicate (assertion vars)
  (declare (type t assertion vars))
  (cons `and (map-type-declaration-over-vars assertion vars)))

(defund function-declaration-to-guard (args signature)
  (declare (type (satisfies function-declaration-p) signature))
  `(and ,@(map-arg-types-over-args (function-declaration-args signature) args)))

(defun guards-from-declare-body (args body)
  (declare (type t body))
  (if (consp body)
      (let ((entry (car body)))
        (cond
	 ((atom entry)
	  (guards-from-declare-body args (cdr body)))
         ((and (equal (car entry) 'acl2::type)
	       (consp (cdr entry)))
          (cons (defun::type-declaration-to-predicate (cadr entry) (cddr entry))
		(guards-from-declare-body args (cdr body))))
         ((equal (car entry) 'acl2::xargs)
	  (let ((xarg-guards (defun::get-xarg-key-from-body :guard (cdr entry))))
	    (let ((signature (defun::get-xarg-key-from-body :signature (cdr entry))))
	      (let ((sig-guards (and (equal (len signature) 1)
				     (coi-debug::assert (signature-declaration-p (car signature)))
				     (let ((decl (signature-to-declaration (car signature))))
				       (list (function-declaration-to-guard args decl))))))
		(append xarg-guards sig-guards
			(guards-from-declare-body args (cdr body)))))))
         (t
          (guards-from-declare-body args (cdr body)))))
    nil))

(defun vals-to-thms-rec (n vals fapp)
  (declare (type (integer 0 *) n))
  (if (consp vals)
      (append (translate-declaration-to-guard-list (car vals) `(val ',n ,fapp))
	      (vals-to-thms-rec (1+ n) (cdr vals) fapp))
    nil))

(defthm true-listp-vals-to-thms-rec
  (true-listp (vals-to-thms-rec n vals fapp)))

(defund vals-to-thms (hyps vals fapp)
  (declare (type t fapp))
  (if (consp vals)
      (if (consp (cdr vals))
	  (let ((conc (vals-to-thms-rec 0 vals fapp)))
	    (and conc `((implies ,hyps (and (true-listp ,fapp) ,@conc)))))
	(let ((conc (translate-declaration-to-guard-list (car vals) fapp)))
	  (and conc `((implies ,hyps ,@conc)))))
    nil))

(defthm true-listp-vals-to-thms
  (true-listp (vals-to-thms hyps vals fapp))
  :hints (("Goal" :in-theory (enable vals-to-thms))))

(defun guards-from-declare-list (args list)
  (declare (type (satisfies declaration-listp) list))
  (if (endp list) nil
    (let ((declare (car list)))
      (append (guards-from-declare-body args (cdr declare))
	      (guards-from-declare-list args (cdr list))))))

(defund function-declaration-to-type-statement (name args decl)
  (declare (type symbol name)
	   (type (satisfies function-declaration-p) decl)
	   (type (satisfies true-listp) args))
  (let ((arg-types (function-declaration-args decl))
	(val-types (function-declaration-vals decl)))
    (let ((fapp `(,name ,@args)))
      (let ((hyps `(and ,@(map-arg-types-over-args arg-types args))))
	(vals-to-thms hyps val-types fapp)))))

(defthm true-listp-function-declaration-to-type-statement
  (true-listp (function-declaration-to-type-statement name args decl))
  :hints (("Goal" :in-theory (enable function-declaration-to-type-statement))))

(defund function-declaration-to-type-thm (name args decl sig-hints)
  (declare (type symbol name)
	   (type (satisfies function-declaration-p) decl)
	   (type (satisfies true-listp) args))
  (let ((fapp `(,name ,@args)))
    (let ((argsymbol (merge-type-decl-fn-names (function-declaration-args decl))))
      (let ((valsymbol (merge-type-decl-fn-names (function-declaration-vals decl))))
	(let ((thmname (symbol-fns::join-symbols name argsymbol 'implies- valsymbol name)))
	  (let ((type-statement (function-declaration-to-type-statement name args decl)))
	    (and type-statement
		 `((defthm ,thmname
		     ,@type-statement
		     ,@(and sig-hints `(:hints ,sig-hints))
		     :rule-classes (:rewrite
				    (:forward-chaining
				     :trigger-terms (,fapp))))))))))))

(defthm true-listp-function-declaration-to-type-thm
  (true-listp (function-declaration-to-type-thm name args decl sig-hints))
  :hints (("Goal" :in-theory (enable function-declaration-to-type-thm))))

(in-theory (disable function-declaration-p))

(defund decls-to-type-statement (name args decls)
  (declare (type symbol name)
	   (type (satisfies true-listp) args)
	   (type (satisfies declaration-listp) decls))
  (met ((typespec signature fty-sig sig-hints decls) (extract-function-declaration decls))
    ;;
    ;; DAG - we shouldn't ignore fty-sig here .. but I don't think
    ;; this ever gets used ..
    ;;
    (declare (ignore fty-sig sig-hints decls))
    (let ((typespec (or typespec signature)))
      (and typespec
	   (function-declaration-to-type-statement name args typespec)))))

(defun defun-to-type-statement (defun)
  (declare (type (satisfies wf-defun) defun))
  (let ((body (defun-body defun)))
    (met ((doc decls body) (decompose-defun-body body))
      (declare (ignore doc body))
      (decls-to-type-statement (defun-name defun) (defun-args defun) decls))))

(defun clean-defun (defun)
  (declare (type (satisfies wf-defun) defun))
  (let ((body (defun-body defun)))
    (met ((doc decls body) (decompose-defun-body body))
      (met ((typespec signature fty-sig sig-hints decls) (extract-function-declaration decls))
        ;; Also, clean-defun appears unused ..
	(declare (ignore typespec fty-sig sig-hints))
	(let ((decls (if signature
			 (cons `(declare
				 (xargs :guard
					,(function-declaration-to-guard (defun-args defun) signature))) decls)
		       decls)))
	  `(,(defun-type defun) ,(defun-name defun) ,(defun-args defun)
	    ,@(and doc (list doc))
	    ,@decls
	    ,body))))))

;; Adding support for :congruence .. doing so will eventually require
;; recursion-support for recursive functions.
;;
;; :congruence assertions take the following form:
;;
#|
(defun foo (x y z)
  (declare (xargs :congruence (((setequiv nil setequiv) setequiv)
			       )
		  :congruence-hints ((("Goal" ..))
				     nil)))
  ..)

|#

;; Support for multiple-value return congruences

(defun mv-equiv (equiv offset)
  (declare (type symbol equiv)
           (type (integer 0 *) offset))
  (cons equiv offset))

(defun mv-equivp (x)
  (declare (type t x))
  (and (consp x)
       (symbolp (car x))
       (natp (cdr x))))

(defthm mv-equivp-implies-symbolp-mv-equiv
  (implies
   (and
    (symbolp equiv)
    (natp offset))
   (mv-equivp (mv-equiv equiv offset)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((mv-equiv equiv offset)))))

(defun outer-equivp (x)
  (declare (type t x))
  (or (symbolp x)
      (mv-equivp x)))

(defthm outer-equivp-from-symbolp
  (implies
   (symbolp x)
   (outer-equivp x))
  :rule-classes (:forward-chaining))

(defthm outer-equivp-from-mv-equivp
  (implies
   (mv-equivp x)
   (outer-equivp x))
  :rule-classes (:forward-chaining))

(defun outer-equiv (x)
  (declare (type (satisfies outer-equivp) x))
  (if (symbolp x) x (car x)))

(defun mv-offset (x)
  (declare (type (satisfies mv-equivp) x))
  (cdr x))

(defthm outer-equivp-implies-symbolp-outer-equiv
  (implies
   (outer-equivp x)
   (symbolp (outer-equiv x)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((outer-equiv x)))))

(defthm mv-equivp-implies-natp-mv-offset
  (implies
   (mv-equivp x)
   (natp (mv-offset x)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((mv-offset x)))))

(defthm symbolp-implies-not-mv-equivp
  (implies
   (and
    (outer-equivp x)
    (not (symbolp x)))
   (mv-equivp x))
  :rule-classes (:forward-chaining))

(in-theory (disable mv-equivp mv-equiv outer-equivp))
(in-theory (disable outer-equiv mv-offset))

(defun outer-equiv-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (outer-equivp (car list))
         (outer-equiv-listp (cdr list)))))

(defthm outer-equiv-listp-implies-true-listp
  (implies
   (outer-equiv-listp x)
   (true-listp x))
  :rule-classes (:forward-chaining))

(defun congruence-spec (list)
  (declare (type t list))
  (and (consp list)
       (symbol-listp (car list))
       (consp (cdr list))
       (outer-equivp (cadr list))
       (null (cddr list))))

(defund mv-congruencep (x)
  (declare (type (satisfies congruence-spec) x))
  (not (symbolp (cadr x))))

(defund congruence-offset (x)
  (declare (type (satisfies congruence-spec) x)
           (type (satisfies mv-congruencep) x)
           (xargs :guard-hints (("Goal" :in-theory (enable mv-congruencep)))))
  (mv-offset (cadr x)))

(defund congruence-equiv (cong)
  (declare (type (satisfies congruence-spec) cong))
  (outer-equiv (cadr cong)))

(defund congruence-pattern (cong)
  (declare (type (satisfies congruence-spec) cong))
  (car cong))

(defthm symbol-listp-congrence-pattern
  (implies
   (congruence-spec cong)
   (symbol-listp (congruence-pattern cong)))
  :hints (("Goal" :in-theory (enable congruence-pattern))))

(defthm symbol-congrence-equiv
  (implies
   (congruence-spec cong)
   (symbolp (congruence-equiv cong)))
  :hints (("Goal" :in-theory (enable congruence-equiv))))

(defthm natp-congrence-offset
  (implies
   (and
    (congruence-spec cong)
    (mv-congruencep cong))
   (natp (congruence-offset cong)))
  :hints (("Goal" :in-theory (enable mv-congruencep congruence-offset)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((congruence-offset cong)))))

(in-theory (disable congruence-spec))

(defun congruence-spec-listp (list)
  (declare (type t list))
  (if (consp list)
      (and (congruence-spec (car list))
	   (congruence-spec-listp (cdr list)))
    (null list)))

(defthm congruence-spec-listp-implies-true-listp
  (implies
   (congruence-spec-listp x)
   (true-listp x))
  :rule-classes (:forward-chaining))

;; User level congruence specifications

(defun wf-congruence-spec (x)
  (declare (type t x))
  (and (consp x)
       (symbol-listp (car x))
       (symbol-listp (cdr x))
       (< 0 (len (cdr x)))))

(defund wf-congruence-pattern (cong)
  (declare (type (satisfies wf-congruence-spec) cong))
  (car cong))

(defthm symbol-listp-wf-congrence-pattern
  (implies
   (wf-congruence-spec cong)
   (symbol-listp (wf-congruence-pattern cong)))
  :hints (("Goal" :in-theory (enable wf-congruence-pattern))))

#+joe
(defun congruence-spec-list-from-wf-congruence-spec-rec (args off res)
  (declare (type (satisfies symbol-listp) args res)
           (type (integer 0 *) off))
  (if (endp res) nil
    (if (not (car res)) (congruence-spec-list-from-wf-congruence-spec-rec args (1+ off) (cdr res))
      (cons (list args (mv-equiv (car res) off))
            (congruence-spec-list-from-wf-congruence-spec-rec args (1+ off) (cdr res))))))

#+joe
(defthm congruence-spec-listp-congruence-spec-list-from-wf-congruence-spec-rec
  (implies
   (and
    (symbol-listp args)
    (symbol-listp res)
    (natp off))
   (congruence-spec-listp (congruence-spec-list-from-wf-congruence-spec-rec args off res)))
  :hints (("Goal" :in-theory (enable congruence-spec))))

#+joe
(defund congruence-spec-list-from-wf-congruence-spec (x)
  (declare (type (satisfies wf-congruence-spec) x))
  (if (< 1 (len (cdr x)))
      (congruence-spec-list-from-wf-congruence-spec-rec (car x) 0 (cdr x))
    (list (list (car x) (cadr x)))))

#+joe
(defthm congruence-spec-listp-congruence-spec-list-from-wf-congruence-spec
  (implies
   (wf-congruence-spec x)
   (congruence-spec-listp (congruence-spec-list-from-wf-congruence-spec x)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((congruence-spec-list-from-wf-congruence-spec x))))
  :hints (("Goal" :in-theory (enable congruence-spec
                                     congruence-spec-list-from-wf-congruence-spec))))

(defun wf-congruence-spec-listp (x)
  (declare (type t x))
  (if (consp x)
      (and (wf-congruence-spec (car x))
	   (wf-congruence-spec-listp (cdr x)))
    (null x)))

#+joe
(defun congruence-spec-list-from-wf-congruence-spec-list (x)
  (declare (type (satisfies wf-congruence-spec-listp) x))
  (if (endp x) nil
    (append (congruence-spec-list-from-wf-congruence-spec (car x))
            (congruence-spec-list-from-wf-congruence-spec-list (cdr x)))))

#+joe
(defun flatten-wf-congruence-spec-list (x)
  (declare (type t x))
  (if (consp x)
      (if (congruence-spec-list (car x))
	  (append (car x) (flatten-wf-congruence-spec-list (cdr x)))
	(cons (car x) (flatten-wf-congruence-spec-list (cdr x))))
    nil))

#+joe
(defthm congruence-spec-list-flatten-wf-congruence-spec-list
  (implies
   (wf-congruence-spec-list x)
   (congruence-spec-list (flatten-wf-congruence-spec-list x))))

(defun wf-congruence-hint (hint)
  (declare (type t hint))
  (true-list-listp hint))

(defun wf-congruence-hint-listp (list)
  (declare (type t list))
  (if (consp list)
      (and (wf-congruence-hint (car list))
	   (wf-congruence-hint-listp (cdr list)))
    (null list)))

#+joe
(defun wf-congruence-hint (x)
  (declare (type t x))
  (or (congruence-hint x)
      (congruence-hint-list x)))

#+joe
(defun wf-congruence-hint-list (x)
  (declare (type t x))
  (if (consp x)
      (and (wf-congruence-hint (car x))
	   (wf-congruence-hint-list (cdr x)))
    (null x)))

#+joe
(defun flatten-wf-congruence-hint-list (x)
  (declare (type t x))
  (if (consp x)
      (if (congruence-hint-list (car x))
	  (append (car x) (flatten-wf-congruence-hint-list (cdr x)))
	(cons (car x) (flatten-wf-congruence-hint-list (cdr x))))
    nil))

#+joe
(defthm congruence-hint-list-flatten-wf-congruence-hint-list
  (implies
   (wf-congruence-hint-list x)
   (congruence-hint-list (flatten-wf-congruence-hint-list x))))

(defun nullify-list-append (x y)
  (declare (type t x y))
  (if (consp x)
      (nullify-list-append (cdr x) (cons nil y))
    y))

(defthm symbol-listp-nullify-list-append
  (implies
   (symbol-listp y)
   (symbol-listp (nullify-list-append x y))))

(defun map-list (x list)
  (declare (type (satisfies symbol-listp) x)
           (type (satisfies outer-equiv-listp) list))
  (if (endp list) nil
    (cons (list x (car list))
          (map-list x (cdr list)))))

(defthm congruence-spec-listp-map-list
  (implies
   (and
    (symbol-listp x)
    (outer-equiv-listp list))
   (congruence-spec-listp (map-list x list)))
  :hints (("Goal" :in-theory (enable CONGRUENCE-SPEC))))

(defun split-pattern (prev next equiv)
  (declare (type (satisfies symbol-listp) prev next)
           (type (satisfies outer-equiv-listp) equiv))
  (if (endp next) nil
    (if (null (car next))
	(split-pattern (cons (car next) prev) (cdr next) equiv)
      (append (map-list (nullify-list-append prev (cons (car next) (nullify-list-append (cdr next) nil))) equiv)
              (split-pattern (cons (car next) prev) (cdr next) equiv)))))

(defthm congruence-spec-listp-append
  (implies
   (congruence-spec-listp x)
   (equal (congruence-spec-listp (append x y))
          (congruence-spec-listp y))))

(defthm congruence-spec-list-split-pattern
  (implies
   (and
    (outer-equiv-listp equiv)
    (symbol-listp prev)
    (symbol-listp next))
   (congruence-spec-listp (split-pattern prev next equiv)))
  :hints (("Goal" :in-theory (enable congruence-spec))))

(defun map-cons (a list)
  (declare (type t list))
  (if (consp list)
      (cons (cons a (car list))
	    (map-cons a (cdr list)))
    nil))

(defun wf-congruence-pairing (pairs)
  (declare (type t pairs))
  (if (consp pairs)
      (and (consp (car pairs))
	   (wf-congruence-hint (caar pairs))
	   (wf-congruence-spec (cdar pairs))
	   (wf-congruence-pairing (cdr pairs)))
    (null pairs)))

(defun congruence-pairing (pairs)
  (declare (type t pairs))
  (if (consp pairs)
      (and (consp (car pairs))
	   (wf-congruence-hint (caar pairs))
	   (congruence-spec (cdar pairs))
	   (congruence-pairing (cdr pairs)))
    (null pairs)))

(defthm congruence-pairing-append
  (implies
   (and
    (congruence-pairing x)
    (congruence-pairing y))
   (congruence-pairing (append x y))))

(defthm congruence-pairing-map-cons
  (implies
   (and
    (wf-congruence-hint a)
    (congruence-spec-listp list))
   (congruence-pairing (map-cons a list))))

(defun outer-equiv-list (off list)
  (declare (type (integer 0 *) off)
           (type (satisfies symbol-listp) list))
  (if (endp list) nil
    (let ((entry (car list)))
      (if (not entry) (outer-equiv-list (1+ off) (cdr list))
        (cons (mv-equiv (car list) off)
              (outer-equiv-list (1+ off) (cdr list)))))))

(defthm outer-equiv-listp-outer-equiv-list
  (implies
   (and
    (natp off)
    (symbol-listp list))
   (outer-equiv-listp (outer-equiv-list off list))))

(defund wf-congruence-outer-equiv-list (cong)
  (declare (type (satisfies wf-congruence-spec) cong)
           (xargs :guard-hints (("Goal" :in-theory (enable wf-congruence-spec)))))
  (let ((outer (cdr cong)))
    (if (= (len outer) 1) (list (car outer))
      (outer-equiv-list 0 outer))))

(defthm outer-equiv-listp-wf-congruence-outer-equiv-list
  (implies
   (wf-congruence-spec cong)
   (outer-equiv-listp (wf-congruence-outer-equiv-list cong)))
  :hints (("Goal" :in-theory (enable wf-congruence-outer-equiv-list))))

(defun split-paired-congruences (pairs)
  (declare (type (satisfies wf-congruence-pairing) pairs))
  (if (consp pairs)
      (let ((pair (car pairs)))
	(let ((hint (car pair))
	      (cong (cdr pair)))
	  (append (map-cons hint (split-pattern nil (wf-congruence-pattern cong) (wf-congruence-outer-equiv-list cong)))
		  (split-paired-congruences (cdr pairs)))))
    nil))

(defthm congruence-pairing-split-paired-congruences
  (implies
   (wf-congruence-pairing pairs)
   (congruence-pairing (split-paired-congruences pairs))))

(defun pair-hints-and-patterns (hints spec)
  (declare (type t hints spec))
  (if (consp spec)
      (if (consp hints)
	  (cons (cons (car hints) (car spec))
		(pair-hints-and-patterns (cdr hints) (cdr spec)))
	(cons (cons nil (car spec))
	      (pair-hints-and-patterns nil (cdr spec))))
    nil))

(defthm congruence-pairing-pair-hints-and-patterns
  (implies
   (and
    (wf-congruence-spec-listp spec)
    (wf-congruence-hint-listp hints))
   (wf-congruence-pairing (pair-hints-and-patterns hints spec))))

(defun pair-hints-with-patterns-and-split (hints spec)
  (declare (type (satisfies wf-congruence-hint-listp) hints)
	   (type (satisfies wf-congruence-spec-listp) spec))
  (let ((pairs (pair-hints-and-patterns hints spec)))
    (split-paired-congruences pairs)))

(defthm congruence-pairing-pair-hints-with-patterns-and-split
  (implies
   (and
    (wf-congruence-hint-listp hints)
    (wf-congruence-spec-listp spec))
   (congruence-pairing (pair-hints-with-patterns-and-split hints spec))))

(include-book "../symbol-fns/symbol-fns")

(defun alt-args-from-pattern (args pattern suffix)
  (declare (type (satisfies symbol-listp) args))
  (if (and (consp args)
	   (consp pattern))
      (let ((arg (car args)))
	(let ((arg (if (null (car pattern)) arg (symbol-fns::suffix arg suffix))))
	  (cons arg (alt-args-from-pattern (cdr args) (cdr pattern) suffix))))
    nil))

(defun arg-equiv (pattern args)
  (declare (type t pattern args))
  (if (and (consp pattern)
	   (consp args))
      (if (null (car pattern))
	  (arg-equiv (cdr pattern) (cdr args))
	(car args))
    'failure))

(defthm symbolp-arg-equiv
  (implies
   (symbol-listp args)
   (symbolp (arg-equiv pattern args))))

(defun add-to-goal-hint (hint value res)
  (declare (type (satisfies wf-congruence-hint) hint)
	   (type (satisfies true-listp) value res))
  (if (consp hint)
      (if (or (equal (caar hint) "Goal")
	      (equal (caar hint) "goal"))
	  (revappend res (cons `("Goal" ,@value ,@(cdar hint)) (cdr hint)))
	(add-to-goal-hint (cdr hint) value (cons (car hint) res)))
    (cons `("Goal" ,@value) (revappend res nil))))

(defthm true-listp-add-to-goal-hint
  (implies
   (true-listp hint)
   (true-listp (add-to-goal-hint hint value res))))

(defund make-congruence-hint (fn fn-induct args alt-args hint)
  (declare (type (satisfies wf-congruence-hint) hint)
	   (type (satisfies true-listp) args alt-args))
  (if fn-induct
      (add-to-goal-hint hint `(:induct (,fn-induct ,@args ,@alt-args)) nil)
    (add-to-goal-hint hint `(:expand ((,fn ,@args) (,fn ,@alt-args))) nil)))

(defthm true-listp-make-congruence-hint
  (implies
   (true-listp hint)
   (true-listp (make-congruence-hint fn fn-induct args alt-args hint)))
  :hints (("Goal" :in-theory (enable make-congruence-hint))))

(defund indexed-equiv-prefix (cong)
  (declare (type (satisfies congruence-spec) cong))
  (if (mv-congruencep cong)
      (symbol-fns::join-symbols '- (congruence-offset cong) '-)
    '-))

(defthm symbolp-indexed-equiv-prefix
  (symbolp (indexed-equiv-prefix cong))
  :hints (("Goal" :in-theory (enable indexed-equiv-prefix))))

(defun make-congruence-conclusion (cong equiv fn args alt-args)
  (declare (type (satisfies congruence-spec) cong)
           (type (satisfies true-listp) args alt-args))
  (if (mv-congruencep cong)
      (let ((off (congruence-offset cong)))
        `(,equiv (val ,off (,fn ,@args))
                 (val ,off (,fn ,@alt-args))))
    `(,equiv (,fn ,@args) (,fn ,@alt-args))))

(defund make-congruence-theorem (n fn fn-induct args congruence hint )
  (declare (type symbol fn)
           (type (satisfies wf-congruence-hint) hint)
	   (type (satisfies symbol-listp) args)
	   (type (satisfies congruence-spec) congruence))
  (let ((equiv    (congruence-equiv congruence))
        (pattern  (congruence-pattern congruence)))
    (let ((offset (indexed-equiv-prefix congruence)))
      (let ((alt-args (alt-args-from-pattern args pattern (symbol-fns::prefix offset equiv))))
        (let ((arg-equiv (arg-equiv pattern pattern))
              (alt-arg   (arg-equiv pattern alt-args))
              (arg       (arg-equiv pattern args)))
          (let ((thm-name (symbol-fns::join-symbols fn (symbol-fns::suffix arg-equiv '- n '-implies- equiv '- fn))))
            (let ((hint (make-congruence-hint fn fn-induct args alt-args hint)))
              (let ((hints (and hint `(:hints ,hint))))
                `(defthm ,thm-name
                   (implies
                    (,arg-equiv ,arg ,alt-arg)
                    ,(make-congruence-conclusion congruence equiv fn args alt-args))
                   :rule-classes :congruence
                   ,@hints)))))))))

(defun make-congruence-theorems (n fn fn-induct args pairs )
  (declare (type integer n)
	   (type symbol fn)
           (type (satisfies congruence-pairing) pairs)
	   (type (satisfies symbol-listp) args))
  (if (consp pairs)
      (let ((pattern (cdar pairs))
	    (hint    (caar pairs)))
	(cons (make-congruence-theorem n fn fn-induct args pattern hint )
	      (make-congruence-theorems (1+ n) fn fn-induct args (cdr pairs) )))
    nil))

(defun process-congruence-arguments (fn args hints specs rec)
  (declare (type (satisfies symbol-listp) args)
	   (type symbol fn)
           (type (satisfies wf-congruence-hint-listp) hints)
           (type (satisfies wf-congruence-spec-listp) specs))
  (let ((pairs (pair-hints-with-patterns-and-split hints specs)))
    (let ((fn-induct (and rec (symbol-fns::suffix fn '-induction))))
      (let ((events (make-congruence-theorems 1 fn fn-induct args pairs)))
        (and events `((encapsulate
                          ()
                        ,@events
                        )))))))
;;    `(:malformed-congruence-xargs)))

(defthm true-listp-process-congruence-arguments
  (true-listp (process-congruence-arguments fn args hints spec rec)))

(in-theory (disable process-congruence-arguments))

(mutual-recursion
 (defun replace-function-names-args (keys suffix args)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (cons (replace-function-names keys suffix (car args))
             (replace-function-names-args keys suffix (cdr args)))
     nil))
 (defun replace-function-names (keys suffix fn)
   (declare (xargs :measure (acl2-count fn)))
   (if (consp fn)
       (cond
	((acl2::lambda-expr-p fn)
	 (defun::make-lambda-application
	   (defun::lambda-formals fn)
	   (replace-function-names keys suffix (defun::lambda-body fn))
	   (replace-function-names-args keys suffix (defun::lambda-args fn))))
	((equal (car fn) 'acl2::quote)
	 fn)
        ((member (car fn) keys)
         (acl2::fcons-term (symbol-fns::suffix (car fn) suffix)
			   (replace-function-names-args keys suffix (cdr fn))))
        (t (acl2::fcons-term (car fn) (replace-function-names-args keys suffix (cdr fn)))))
     fn))
 )
