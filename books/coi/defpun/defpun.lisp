; Copyright (C) 2013, Regents of the University of Texas
; Written by Panagiotis Manolios and J Strother Moore, 2000
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Modified May 2004 by Matt Kaufmann, in order to allow stobjs.  Thanks to John
; Matthews for providing a motivating example.  NOTE:  Do not use a :stobjs
; declaration in your defpun!

;; Modified by May 2006 by Dave Greve to provide simple predicate type
;; constraints on the partial function.  The user must provide a type
;; expression on the arguments and the name of the predicate type
;; along with a default value for that type.  If no default value is
;; provided, defpun will attempt to use the 0-ary function constructed
;; from the valtype base name: (default-valtype).
#|
(defpun joe (x)
  (if (zp x) x
    (joe (1- x)))
  :argtypes (integerp x)
  :valtype integerp
  :default 0
  )
|#
;; Will produce the type theorem:
#|
(defthm joe-type
  (implies
   (integerp x)
   (integerp (joe x))))
|#
;; The following form also happens to work, since the typed arguments
;; are used as witnesses for the defchosen default value of natp.
#|
(defchoose default-natp (n) nil
  (natp n))

(defthm natp-instance-type
  (implies
   (natp n)
   (natp (default-natp)))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal" :use default-natp)))

(defpun joe (x) (if (zp x) x (joe (1- x))) :argtypes (natp x) :valtype natp)
|#

;  Written by Panagiotis Manolios and J Strother Moore who can be
;  reached as follows.

;  Email: pete@cs.utexas.edu, moore@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

; To introduce an arbitrary tail-recursive function we proceed in
; three steps.  First is the proof that we can admit the generic one
; argument tail recursive function.  This ``generic theorem'' is
; proved once; the proof is not redone for each new function.  Second,
; the generic theorem is used to introduce the arity one version of
; the desired function.  Third, we prove that the arity one version is
; a witness for the desired equation.

; Here is an example.  Suppose we wish to admit the tail recursive
; factorial.

; (defun trfact (n a)
;   (if (equal n 0)
;       a
;     (trfact (- n 1) (* n a))))

; We first recognize that this is probably tail recursive (without
; checking that trfact is new, that the vars are distinct, etc.).
; Successful recognition produces

; (mv '((n (car x))
;       (a (cadr x)))
;     '(equal n 0)
;     'a
;     '(list (- n 1) (* n a)))

; Using the output of this check, we introduce three defuns

; (defun test1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     (equal n 0)))

; (defun base1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     a))

; (defun step1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     (list (- n 1) (* n a))))

; We then use the generic theorem to introduce

; (defun trfact1 (x)
;   (if (test1 x)
;       (base1 x)
;     (trfact1 (step1 x))))

; We then define

; (defun trfact (n a)
;   (trfact1 (list n a)))

; and we prove that it satisfies the constraint

; (equal (trfact n a)
;        (if (equal n 0)
;            a
;          (trfact (- n 1) (* n a))))

; Now we write the code to do all this.

; First, we prove the generic theorem.  We use the proof Pete
; developed in his prototype implementation of defpartial but for the
; generic case.

(in-package "ACL2")

(defmacro defun-nonexec (name args &rest rst)
  `(defun-nx ,name ,args ,@rst))

(encapsulate
    (
     ((defpun-arg-type *) => *)
     ((defpun-ret-type *) => *)
     ((defpun-default) => *)
     ((defpun-test *) => *)
     ((defpun-base *) => *)
     ((defpun-st *) => *)
     )

  (local
   (encapsulate
       ()
     (set-ignore-ok t)
     (set-irrelevant-formals-ok t)
     (defstub defpun-test (x) t)
     (defstub defpun-base (x) t)
     (defstub defpun-st   (x) t)
     (defstub defpun-default () t)
     (defun defpun-arg-type (x) t)
     (defun defpun-ret-type (x) t)
     ))

  (defthm defpun-ret-type-defpun-default
    (implies
     (defpun-arg-type x)
     (defpun-ret-type (defpun-default))))

  (defthm defpun-ret-type-defpun-base
    (implies
     (defpun-arg-type x)
     (defpun-ret-type (defpun-base x))))

  (defthm defpun-arg-type-defpun-st
    (implies
     (and
      (not (defpun-test x))
      (defpun-arg-type x))
     (defpun-arg-type (defpun-st x))))

  )

(defun defpun-stn (x n)
  (if (zp n) x (defpun-stn (defpun-st x) (1- n))))

(defchoose defpun-fch (n)
  (x)
  (defpun-test (defpun-stn x n)))

(defun defpun-fn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (defpun-test x))
      (defpun-base x)
      (defpun-fn (defpun-st x) (1- n))))

(defthm defpun-ret-type-defpun-fn
  (implies
   (defpun-arg-type x)
   (defpun-ret-type (defpun-fn x n))))

(defun defpun-f (x)
  (if (defpun-test (defpun-stn x (defpun-fch x)))
      (defpun-fn x (defpun-fch x))
    (defpun-default)))

;; Key type theorem
(defthm defpun-ret-type-defpun-f
  (implies
   (defpun-arg-type x)
   (defpun-ret-type (defpun-f x))))

(defun defpun-true (x)
  (declare (ignore x)) t)

;; The "clique" theorem
(defthm defpun-true-defpun-f
  (defpun-true (defpun-f x)))

(in-theory (disable defpun-true))
(in-theory (disable (defpun-true)))
(in-theory (disable (:type-prescription defpun-true)))

; The following encapsulate exports one constrained function, namely,
; f, with the constraint

; (DEFTHM GENERIC-TAIL-RECURSIVE-F
;   (EQUAL (defpun-f X)
;          (IF (TEST X) (DEFPUN-BASE X) (defpun-f (DEFPUN-ST X))))
;   :RULE-CLASSES NIL)

; Nothing else is exported.

(encapsulate nil
 (local (defthm test-fch
          (implies (defpun-test x)
                   (defpun-test (defpun-stn x (defpun-fch x))))
          :hints
          (("goal" :use ((:instance defpun-fch (n 0)))))))
 (local (defthm test-f-def
          (implies (defpun-test x)
                   (equal (defpun-f x) (defpun-base x)))))
 (local (defthm open-stn
          (implies (and (integerp n) (< 0 n))
                   (equal (defpun-stn x n) (defpun-stn (defpun-st x) (1- n))))))

 (local (defthm +1-1 (equal (+ -1 +1 x) (fix x))))

 (local (defthm st-stn-fch
          (implies (defpun-test (defpun-stn (defpun-st x) (defpun-fch (defpun-st x))))
                   (defpun-test (defpun-stn x (defpun-fch x))))
          :hints
          (("goal" :use
            ((:instance defpun-fch (n (1+ (nfix (defpun-fch (defpun-st x))))))
             (:instance defpun-fch (n 1)))))
          :rule-classes :forward-chaining))
 (local (defthm test-nil-fch
          (implies (not (defpun-test x))
                   (iff (defpun-test (defpun-stn (defpun-st x) (defpun-fch (defpun-st x))))
                        (defpun-test (defpun-stn x (defpun-fch x)))))
          :hints
          (("subgoal 2" :expand (defpun-stn x (defpun-fch x))
            :use
            ((:instance defpun-fch (x (defpun-st x))
                        (n (+ -1 (defpun-fch x)))))))))
 (local (defthm fn-st
          (implies (and (defpun-test (defpun-stn x n)) (defpun-test (defpun-stn x m)))
                   (equal (defpun-fn x n) (defpun-fn x m)))
          :rule-classes nil))
 (defthm generic-tail-recursive-f
   (equal (defpun-f x)
          (if (defpun-test x) (defpun-base x) (defpun-f (defpun-st x))))
   :hints
   (("subgoal 1" :expand (defpun-fn x (defpun-fch x)))
    ("subgoal 1.2'" :use
     ((:instance fn-st (x (defpun-st x))
                 (n (+ -1 (defpun-fch x)))
                 (m (defpun-fch (defpun-st x)))))))
   :rule-classes nil))

(defun arity-1-tail-recursive-encap (f test base st arg-type ret-type default)

; Execution of this function produces an encapsulation that introduces
; a constrained tail recursive f with the constraint
; (equal (defpun-f x) (if (defpun-test x) (defpun-base x) (defpun-f (defpun-st x)))),
; where test, base and st are previously defined functions of arity 1.

  (declare (xargs :mode :program))

  (let ((stn (packn-pos (list f "-stn") f))
        (fch (packn-pos (list f "-fch") f))
        (fn  (packn-pos (list f "-fn") f)))

    `(encapsulate
      ((,f (x) t))

      (local (in-theory (disable ,test ,base ,st)))

      (local (defun-nonexec ,stn (x n)
               (if (zp n)
                   x
                 (,stn (,st x) (1- n)))))

      (local (defchoose ,fch (n) (x)
               (,test (,stn x n))))

      (local (defun-nonexec ,fn (x n)
               (declare (xargs :measure (nfix n)))
               (if (or (zp n)
                       (,test x))
                   (,base x)
                 (,fn (,st x) (1- n)))))

      (local (defun-nonexec ,f (x)
               (if (,test (,stn x (,fch x)))
                   (,fn x (,fch x))
                 (,default))))

      (defthm ,(packn-pos (list f "-CLIQUE") f)
        (defpun-true (,f x))
        :hints (("Goal"
		 :in-theory '(,f ,test ,base ,st ,stn ,fn ,arg-type
				 (:type-prescription ,fn))
                 :use
                 (:functional-instance defpun-true-defpun-f
                                       (defpun-arg-type ,arg-type)
				       (defpun-ret-type ,ret-type)
				       (defpun-f ,f)
                                       (defpun-test ,test)
                                       (defpun-base ,base)
                                       (defpun-st ,st)
                                       (defpun-stn ,stn)
                                       (defpun-fch ,fch)
                                       (defpun-fn ,fn)
				       (defpun-default ,default)
                                       ))
                ("Subgoal 2" :in-theory '(,f ,test ,base ,st ,stn ,fn ,arg-type
				 (:type-prescription ,fn))
		 :use ,fch)
		(and stable-under-simplificationp
		     '(:in-theory (current-theory :here))))
        :rule-classes nil)

      (defthm ,(packn-pos (list f "-DEF") f)
        (equal (,f x)
               (if (,test x)
                   (,base x)
                 (,f (,st x))))
        :hints (("Goal"
                 :use
                 (:functional-instance GENERIC-TAIL-RECURSIVE-F
                                       (defpun-arg-type ,arg-type)
				       (defpun-ret-type ,ret-type)
				       (defpun-f ,f)
                                       (defpun-test ,test)
                                       (defpun-base ,base)
                                       (defpun-st ,st)
                                       (defpun-stn ,stn)
                                       (defpun-fch ,fch)
                                       (defpun-fn ,fn)
				       (defpun-default ,default)
                                       )))
        :rule-classes nil)

      (defthm ,(packn-pos (list f "-TYPE") f)
        (implies
	 (,arg-type x)
	 (,ret-type (,f x)))
        :hints (("Goal"
                 :use
                 (:functional-instance defpun-ret-type-defpun-f
                                       (defpun-arg-type ,arg-type)
				       (defpun-ret-type ,ret-type)
				       (defpun-f ,f)
                                       (defpun-test ,test)
                                       (defpun-base ,base)
                                       (defpun-st ,st)
                                       (defpun-stn ,stn)
                                       (defpun-fch ,fch)
                                       (defpun-fn ,fn)
				       (defpun-default ,default)
                                       )))
        :rule-classes nil)
      )

    ))

; Second, we recognize probably tail-recursive definitions and introduce
; the appropriate functions of arity 1.

; Note that probably-tail-recursivep and destructure-tail-recursion should be
; kept in sync.

(defun probably-tail-recursivep (f vars body)
  (and (symbolp f)
       (symbol-listp vars)
       (true-listp body)
       (eq (car body) 'IF)
       (or (and (consp (caddr body))
                (eq (car (caddr body)) f))
           (and (consp (cadddr body))
                (eq (car (cadddr body)) f)))))

(defun destructure-tail-recursion-aux (vars x)
  (declare (xargs :mode :program))
  (cond ((endp vars) nil)
        (t (cons (list (car vars)
                       (list 'car x))
                 (destructure-tail-recursion-aux (cdr vars)
                                               (list 'cdr x))))))

(defun destructure-tail-recursion (f vars body)
  (declare (xargs :mode :program))
  (cond
   ((and (consp (caddr body))
         (eq (car (caddr body)) f))
    (mv (destructure-tail-recursion-aux vars 'x)
        (list 'NOT (cadr body))
        (cadddr body)
        (cons 'LIST (cdr (caddr body)))))
   (t
    (mv (destructure-tail-recursion-aux vars 'x)
        (cadr body)
        (caddr body)
        (cons 'LIST (cdr (cadddr body)))))))

(defun arbitrary-tail-recursive-encap (f vars body arg-type ret-type default keypairs)
  (declare (xargs :mode :program))
  (mv-let
   (bindings test-body base-body step-body)
   (destructure-tail-recursion f vars body)
   (let ((f1    (packn-pos (list f "-arity-1") f))
         (type1 (packn-pos (list f "-arity-1-type") f))
         (test1 (packn-pos (list f "-arity-1-test") f))
         (base1 (packn-pos (list f "-arity-1-base") f))
         (step1 (packn-pos (list f "-arity-1-step") f)))
     `(encapsulate
	  ()
	(encapsulate
	    ((,f ,vars t))
	  (set-ignore-ok t)
	  (set-irrelevant-formals-ok t)
	  (local (defun-nonexec ,test1 (x) (let ,bindings ,test-body)))
	  (local (defun-nonexec ,base1 (x) (let ,bindings ,base-body)))
	  (local (defun-nonexec ,step1 (x) (let ,bindings ,step-body)))
	  (local (defun-nonexec ,type1 (x) (let ,bindings ,arg-type)))
	  (local ,(arity-1-tail-recursive-encap f1 test1 base1 step1 type1 ret-type `(lambda () ,default)))
	  (local (defun-nonexec ,f ,vars (,f1 (list ,@vars))))
	  (defthm ,(packn-pos (list f "-DEF") f)
	    (equal (,f ,@vars) ,body)
	    :hints (("Goal" :use (:instance ,(packn-pos (list f1 "-DEF") f)
					    (x (list ,@vars)))))
	    ,@keypairs)

	  ,@(and arg-type
		 `((defthm ,(packn-pos (list f "-TYPE") f)
		     (implies
		      ,arg-type
		      (,ret-type (,f ,@vars)))
		     :hints (("Goal" :use (:instance ,(packn-pos (list f1 "-TYPE") f)
						     (x (list ,@vars))))))))

	  )
	;;
	;; DAG -- In most circumstances, the following rule appears to
	;; work much better than the :definition rule above.
	;;
	;; Nonetheless, I have it disabled for now.
	;;
	(defthmd ,(packn-pos (list "OPEN-" f) f)
	  (and
	   (implies
	    ,test-body
	    (equal (,f ,@vars) ,base-body))
	   (implies
	    (not ,test-body)
	    (equal (,f ,@vars) ,(cons f (cdr step-body)))))
          :hints (("Goal" :in-theory (theory 'minimal-theory)
                   :use ,(packn-pos (list f "-DEF") f))))
	))))

(defun remove-xargs-domain-and-measure (dcl)
  (case-match dcl
              (('declare ('xargs ':domain dom-expr
                                 ':measure measure-expr
                                 . rest))
               (mv nil dom-expr measure-expr rest))
              (('declare ('xargs ':gdomain dom-expr
                                 ':measure measure-expr
                                 . rest))
               (mv t dom-expr measure-expr rest))
              (& (mv nil nil 0 nil))))

(mutual-recursion
 (defun subst-fn-into-pseudo-term (new-fn old-fn pterm)
   (declare (xargs :mode :program))
   (cond
    ((atom pterm) pterm)
    ((eq (car pterm) 'quote) pterm)
    ((or (eq (car pterm) 'let)
         (eq (car pterm) 'let*))
     (list (car pterm)
           (subst-fn-into-pseudo-bindings new-fn old-fn (cadr pterm))
           (subst-fn-into-pseudo-term new-fn old-fn (caddr pterm))))
    ((eq (car pterm) 'cond)
     (cons 'cond
           (subst-fn-into-pseudo-cond-clauses new-fn old-fn (cdr pterm))))
    (t
     (cons (if (eq (car pterm) old-fn)
               new-fn
             (car pterm))
           (subst-fn-into-pseudo-term-list new-fn old-fn (cdr pterm))))))

 (defun subst-fn-into-pseudo-bindings (new-fn old-fn pbindings)
   (declare (xargs :mode :program))
   (cond
    ((atom pbindings) pbindings)
    (t (cons (list (car (car pbindings))
                   (subst-fn-into-pseudo-term new-fn old-fn
                                              (cadr (car pbindings))))
             (subst-fn-into-pseudo-bindings new-fn old-fn (cdr pbindings))))))

 (defun subst-fn-into-pseudo-cond-clauses (new-fn old-fn pclauses)
   (declare (xargs :mode :program))
   (cond
    ((atom pclauses) pclauses)
    (t (cons (list (subst-fn-into-pseudo-term new-fn old-fn
                                              (car (car pclauses)))
                   (subst-fn-into-pseudo-term new-fn old-fn
                                              (cadr (car pclauses))))
             (subst-fn-into-pseudo-cond-clauses new-fn old-fn
                                                (cdr pclauses))))))

 (defun subst-fn-into-pseudo-term-list (new-fn old-fn list)
   (declare (xargs :mode :program))
   (cond
    ((atom list) list)
    (t (cons (subst-fn-into-pseudo-term new-fn old-fn (car list))
             (subst-fn-into-pseudo-term-list new-fn old-fn (cdr list)))))))

(defun default-defpun-rule-classes (keyword-alist)

; We add :rule-classes :definition to keyword-alist if :rule-classes is
; not mentioned in it.

  (cond
   ((keyword-value-listp keyword-alist)
    (cond ((assoc-keyword :rule-classes keyword-alist)
           keyword-alist)
          (t (list* :rule-classes :definition keyword-alist))))
   (t keyword-alist)))

(defun destructure-dcl-body-keypairs (lst)

; Lst is the tail of some defpun.  It optionally contains a DECLARE
; form, a body, and some keyword binding pairs, in that order.  We
; return the three components.  Body must be present, and if keyword
; binding pairs are present, the length of that part of the list must
; be even.  So the parity of the length of the list determines which
; optional components are present.

; 0. illegal - never allowed to happen
; 1. body
; 2. dcl body
; 3. body :rule-classes classes
; 4. dcl body :rule-classes classes
; 5. body :rule-classes classes :hints hints
; 6. dcl body :rule-classes classes :hints hints
; etc.
; If rule-classes is unspecified it defaults to :definition.

  (cond
   ((evenp (length lst))
    (mv (car lst)
        (cadr lst)
        (default-defpun-rule-classes (cddr lst))))
   (t (mv nil
          (car lst)
          (default-defpun-rule-classes (cdr lst))))))

(defun defpun-syntax-er nil
  '(er soft 'defpun
       "The proper shape of a defpun event is~%~
        (defpun g (v1 ... vn) body).~%~
        A single optional declare form may be present ~
        before the body.  If present, the form must be one of three:~%~
        (DECLARE (XARGS :witness fn))~%~
        or~%~
        (DECLARE (XARGS :domain dom-expr :measure m . rest))~%~
        or~%~
        (DECLARE (XARGS :gdomain dom-expr :measure m . rest)).~%~
        An optional keyword alist may be ~
        present after the body.  The declare form is used during the ~
        admission of the witness function.  The keyword alist is ~
        attached to the equality axiom constraining the new function ~
        symbol.  If the :rule-classes keyword is not specified by the ~
        keyword alist, :definition is used."))

(defun extract-pair (a plist)
  (if (and (consp plist)
	   (consp (cdr plist)))
      (let ((key (car plist))
	    (val (cadr plist)))
	(if (equal a key)
	    (mv (cons key val) (cddr plist))
	  (mv-let
	   (pair plist) (extract-pair a (cddr plist))
	   (mv pair (list* key val plist)))))
    (mv nil nil)))

(defun extract-type-info (keypairs)
  (declare (xargs :mode :program))
  (mv-let
   (pair keypairs) (extract-pair :argtypes keypairs)
   (let ((argtype (if (consp pair) (cdr pair) nil)))
     (mv-let
      (pair keypairs) (extract-pair :valtype keypairs)
      (if (consp pair)
	  (let ((rettype (cdr pair)))
	    (mv-let
	     (pair keypairs) (extract-pair :default keypairs)
	     (if (consp pair)
		 (let ((default (cdr pair)))
		   (mv argtype rettype default keypairs))
	       (let ((default `(,(packn-pos (list "DEFAULT-" rettype) rettype))))
		 (mv argtype rettype default keypairs)))))
	(let ((rettype '(lambda (x) t)))
	  (mv-let
	   (pair keypairs) (extract-pair :default keypairs)
	   (let ((default (if (consp pair) (cdr pair) 'nil)))
	     (mv argtype rettype default keypairs)))))))))

(defmacro defpun (g vars &rest rest)
  (cond
   ((and (symbolp g)
         (symbol-listp vars)
         (not (endp rest)))

; This form may be legal, so we will destructure it and proceed.  Otherwise,
; we will cause an error.

    (mv-let
     (dcl body keypairs)
     (destructure-dcl-body-keypairs rest)
     (mv-let
      (arg-type ret-type default keypairs) (extract-type-info keypairs)
      (cond
       ((not (keyword-value-listp keypairs))
	(defpun-syntax-er))
       ((and (not dcl)
	     (probably-tail-recursivep g vars body))
	(arbitrary-tail-recursive-encap g vars body arg-type ret-type default
                                        keypairs))
       ((and dcl
	     (match dcl
		    ('declare ('xargs ':witness &))))
	`(encapsulate
	     ((,g ,vars t))
	   (local (defun-nonexec ,g ,vars (,(caddr (cadr dcl))
					   ,@vars)))
	   (defthm ,(packn-pos (list g "-DEF") g)
	     (equal (,g ,@vars)
		    ,body)
	     ,@keypairs)))
       ((not (and (consp dcl)
		  (eq (car dcl) 'declare)))
	(defpun-syntax-er))
       (t
	(mv-let
	 (closed-domp dom-expr measure-expr rest-of-xargs)
	 (remove-xargs-domain-and-measure dcl)
	 (cond
	  (closed-domp
	   (let ((gwit (packn-pos (list "THE-" g) g)))
	     `(encapsulate
		  nil
		(defun ,gwit ,vars
		  (declare (xargs :measure
				  (if ,dom-expr
				      ,measure-expr
				    0)
				  :guard ,dom-expr
				  :verify-guards nil
				  ,@rest-of-xargs))
		  (if ,dom-expr
		      ,(subst-fn-into-pseudo-term gwit g body)
		    'undef))
		(encapsulate
		    ((,g ,vars t))
		  (local (defun-nonexec ,g ,vars (,gwit ,@vars)))
		  (defthm ,(packn-pos (list g "-DEF") g)
		    (implies ,dom-expr
			     (equal (,g ,@vars)
				    ,body))
		    ,@keypairs))
		(defthm ,(packn-pos (list g "-IS-UNIQUE") g)
		  (implies ,dom-expr
			   (equal (,g ,@vars)
				  (,gwit ,@vars))))
		(in-theory (disable ,(packn-pos (list g "-IS-UNIQUE") g)))
		(verify-guards ,gwit))))
	  (t `(encapsulate
		  ((,g ,vars t))
		(local (defun-nonexec ,g ,vars
			 (declare (xargs :measure
					 (if ,dom-expr
					     ,measure-expr
					   0)
					 ,@rest-of-xargs))
			 (if ,dom-expr
			     ,body
			   'undef)))
		(defthm ,(packn-pos (list g "-DEF") g)
		  (implies ,dom-expr
			   (equal (,g ,@vars)
				  ,body))
		  ,@keypairs))))))))))
    (t (defpun-syntax-er))))
