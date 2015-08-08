;;===========================================================================
;; Copyright (C) 1999 Institut fuer Informatik, University of Kiel, Germany
;;===========================================================================
;; File:         evaluator.lisp
;; Author:       Wolfgang Goerigk
;; Content:      ACL2 implementation of an operational Lisp semantics
;; as of:        24/05/99, University of Kiel, Germany
;;---------------------------------------------------------------------------
;; $Revision: 1.8 $
;; $Id: evaluator.lisp,v 1.8 1999/10/02 20:05:48 wg Exp wg $
;;===========================================================================
;; This book is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;---------------------------------------------------------------------------
;; This book is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;---------------------------------------------------------------------------
;; You should have received a copy of the GNU General Public License along
;; with this book; if not, write to the Free Software Foundation, Inc., 675
;; Mass Ave, Cambridge, MA 02139, USA.
;;===========================================================================
;;
;; This book is part of a series of books that come with and are described in
;; the article "Wolfgang Goerigk: Compiler Verification Revisited" as part of
;; "Computer Aided Reasoning: ACL2 Case Studies" edited by Matt Kaufmann, Pete
;; Manolios and J Strother Moore.
;;
;;===========================================================================
;; Disclaimer: We are not experts in using ACL2. Probably most of the stuff in
;; this book could be expressed much more elegantly, in particular with
;; respect to guard verification, which we only perform to make this a
;; certified book. We are quite restrictive in the guards and thus have to
;; prove a lot.
;;===========================================================================
;;
;; An Operational Semantics (evaluator) for mini-ComLisp
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; This book contains a semantics definition for mini-ComLisp (SL). There is a
;; definition of well-formed mini-ComLisp (SL) programs as well. The syntax of
;; programs is described in the article and also in "compiler". The function
;; evaluate takes a list of definitions (defs), a list of global variables
;; (vars), a top level form (main), that is the program, and an input list
;; (inputs) with length at least (len vars). Its result is either a one
;; element list containing the regular result of evaluating main, or 'error if
;; it ran out of time.
;;
;; Note: We can not guarantee programs to terminate, consequently we can not
;; guarantee the interpreter to terminate. Therefore we add an additional
;; "termination argument" n which forces the evaluator to terminate after at
;; most n user defined function calls. (See "machine" for more information.)
;;
;;===========================================================================

(in-package "ACL2")
(include-book "compiler")
(include-book "../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)


;;---------------------------------------------------------------------------
;; We treat true lists as regular results, i.e. every non true list and in
;; particular 'error serves as the undefined value. There is one exception: nil
;; is a regular result of evlist. But evl only returns either 'error or a
;; one-element list with the result. defined is a predicate, undefined a
;; constant.
;;---------------------------------------------------------------------------

(defun defined (x) (declare (xargs :guard t)) (true-listp x))
(defun undefined () (declare (xargs :guard t)) 'error)

;;---------------------------------------------------------------------------
;; The evaluators State (env)
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; The state (or environment) maps variables to their values. We use
;; association lists. Binding variables (x1 ... xn) (vars) to values (v1
;; ... vn) (args) in a given local environment (env) is the construction of a
;; true association list ((x1 . v1) ... (xn . vn)) appended to env.
;;
;; Note: It is not necessary to extend the old environment in our case since
;; we do not have any block or function nesting. Therefore, we could cut the
;; old environment off entirely and evaluate function bodies in their own
;; local environment:
;;
;;  (defun bind (vars args)
;;    (if (endp vars)
;;        nil
;;      (cons (cons (car vars) (car args)) (bind (cdr vars) (cdr args)))))
;;
;; But we prefer to use the classical way and extend the old environment.
;;---------------------------------------------------------------------------

(defun bind (vars args env)
  (declare (xargs :guard (and (symbol-listp vars) (true-listp args))))
  (if (endp vars)
      env
    (cons (cons (car vars) (car args)) (bind (cdr vars) (cdr args) env))))


;;---------------------------------------------------------------------------
;; In order to evaluate a program, we need a global environment (genv) that
;; maps function names to their definitions (i.e. the list of formal
;; parameters and the body). We construct an association list from the list of
;; the program's function definitions:
;;
;; ((DEFUN f1 args1 code1) (DEFUN f2 args2 code2) ...)
;; -> ((f1 . (args1 code1)) (f2 . (args2 code2)) ...)
;;---------------------------------------------------------------------------

(defun construct-genv (defs)
  (declare (xargs :guard (definition-listp defs)))
  (if (consp defs)
      (cons (cons (cadar defs) (cddar defs)) ;; same as (cdar defs)
	    (construct-genv (cdr defs)))
    nil))

;;
;; For guard verification we need a recognizer for such association lists, and
;; we prove that construct-genv constructs such a thing:
;;

(defun genvp (genv)
  (declare (xargs :guard t))
  (if (consp genv)
      (and (consp (car genv)) (symbolp (caar genv))
	   (consp (cdar genv)) (symbol-listp (cadar genv))
	   (consp (cddar genv)) (formp (caddar genv))
	   (genvp (cdr genv)))
    (null genv)))

(defthm constructs-genv
  (implies (definition-listp defs) (genvp (construct-genv defs))))

;;
;; The following two functions return the body respectively the formals of the
;; definition associated with f within genv.
;;

(defun get-vars (f genv)
  (declare (xargs :guard (and (symbolp f) (genvp genv))))
  (cadr (assoc f genv)))

(defun get-body (f genv)
  (declare (xargs :guard (and (symbolp f) (genvp genv))))
  (caddr (assoc f genv)))

;;
;; The global environment genv contains the same information as the definition
;; list it has been constructed from.
;;

(defun corresponds (defs genv)
  (declare (xargs :guard (and (definition-listp defs) (genvp genv))))
  (if (consp defs)
      (and (equal (cadr (car defs)) (car (assoc (cadr (car defs)) genv)))
	   (equal (caddr (car defs)) (get-vars (cadr (car defs)) genv))
	   (equal (cadddr (car defs)) (get-body (cadr (car defs)) genv))
	   (corresponds (cdr defs) (cdr genv)))
    (null genv)))

(defthm corresponding-genv
  (corresponds defs (construct-genv defs)))

;;
;; Now let us define what it means that a definition is "within" a list of
;; definitions. Note that def is defined to be "within" defs, if the first
;; definition with its name in defs is equal to def. This notion ignores
;; double declarations the same way assoc does.
;;

(defun get-definition (name defs)
  (declare (xargs :guard (definition-listp defs)))
  (if (consp defs)
      (if (equal name (cadr (car defs)))
	  (car defs)
	(get-definition name (cdr defs)))
    nil))

(defun within (def defs)
  (declare (xargs :guard (and (definitionp def) (definition-listp defs))))
  (equal def (get-definition (cadr def) defs)))


(defthm get-vars-gets-vars
  (implies (within def defs)
	   (equal (get-vars (cadr def) (construct-genv defs))
		  (caddr def)))
  :rule-classes nil)

(defthm get-body-gets-body
  (implies (within def defs)
	   (equal (get-body (cadr def) (construct-genv defs))
		  (cadddr def)))
  :rule-classes nil)

(defun used-definition (name defs)
  (declare (xargs :guard (and (symbolp name) (definition-listp defs))))
  (list 'defun name (get-vars name (construct-genv defs))
	(get-body name (construct-genv defs))))

(in-theory (disable get-definition within used-definition))

;;
;; The following theorems are technical. Don't look too intensively through
;; them. They are just in order to be able to verify the guards of the
;; mutually recursive definitions of evl and evlist.
;;

(defthm genvp-implies-alistp
  (implies (genvp genv) (alistp genv)))

(defthm form-if
  (implies (and (formp f) (equal (car f) 'if))
	   (and (formp (cadr f)) (formp (caddr f)) (formp (cadddr f)))))

(defthm genv-lookup-function-defp  ;; deleted premise (assoc f genv)
  (implies (genvp genv)              ;; -> well-formed programs
	   (and (symbol-listp (cadr (assoc f genv)))
		(formp (caddr (assoc f genv))))))

(defthm alistp-bind
  (implies (alistp env) (alistp (bind vars forms env))))

(defthm genv-lookup-nil
  (implies (and (genvp genv) (not (consp (assoc f genv))))
	   (not (assoc f genv))))

(defthm genv-lookup-nil-2
  (implies (and (genvp genv) (not (consp (cddr (assoc f genv)))))
	   (not (cddr (assoc f genv)))))

(defthm genv-lookup-nil-3
  (implies (and (genvp genv) (not (consp (cdr (assoc f genv)))))
	   (not (cdr (assoc f genv)))))

;;===========================================================================
;; The operational semantics
;; ~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; In order to apply a standard function, we use the corresponding operator
;; defined in "machine". This sound weird, but note: It is only for guard
;; verification. Moreover, in "machine" you will find a proof that these
;; operators are equal to their ACL2 counterparts. So read this as if e.g. for
;; the evaluation of (car ...) we use car, and so forth.
;;
;; Note: Evaluating forms returns either a one element list with the result
;; (defined case) or 'error (undefined case).
;;---------------------------------------------------------------------------

(defun evlop (op args genv env n)
  (declare (ignore genv env n)
	   (xargs :guard (true-listp args)))
  (cond
   ((equal op 'CAR) (list (MCAR (car args))))
   ((equal op 'CDR) (list (MCDR (car args))))
   ((equal op 'CADR) (list (MCADR (car args))))
   ((equal op 'CADDR) (list (MCADDR (car args))))
   ((equal op 'CADAR) (list (MCADAR (car args))))
   ((equal op 'CADDAR) (list (MCADDAR (car args))))
   ((equal op 'CADDDR) (list (MCADDDR (car args))))
   ((equal op '1-) (list (M1- (car args))))
   ((equal op '1+) (list (M1+ (car args))))
   ((equal op 'LEN) (list (MLEN (car args))))
   ((equal op 'SYMBOLP) (list (MSYMBOLP (car args))))
   ((equal op 'CONSP) (list (MCONSP (car args))))
   ((equal op 'ATOM) (list (MATOM (car args))))
   ((equal op 'CONS) (list (MCONS (car args) (cadr args))))
   ((equal op 'EQUAL) (list (MEQUAL (car args) (cadr args))))
   ((equal op 'APPEND) (list (MAPPEND (car args) (cadr args))))
   ((equal op 'MEMBER) (list (MMEMBER (car args) (cadr args))))
   ((equal op 'ASSOC) (list (MASSOC (car args) (cadr args))))
   ((equal op '+) (list (M+ (car args) (cadr args))))
   ((equal op '-) (list (M- (car args) (cadr args))))
   ((equal op '*) (list (M* (car args) (cadr args))))
   ((equal op 'LIST1) (list (LIST1 (car args))))
   ((equal op 'LIST2) (list (LIST2 (car args) (cadr args))))
   ))

;;---------------------------------------------------------------------------
;; The semantics of forms and form lists. The next two definitions are
;; mutually recursive.
;;---------------------------------------------------------------------------
(mutual-recursion

(defun evl (form genv env n)
  (declare (xargs :guard (and (formp form) (genvp genv)
			      (alistp env) (natp n))
		  :measure (cons (1+ (acl2-count n)) (acl2-count form))))
  (cond
   ((zp n) (undefined))
   ((equal form 'nil) (list nil))
   ((equal form 't) (list t))
   ((symbolp form) (list (cdr (assoc form env))))
   ((atom form) (list form))
   ((equal (car form) 'QUOTE) (list (cadr form)))
   ((equal (car form) 'IF)
    (let ((cond (evl (cadr form) genv env n)))
      (if (defined cond)
	  (if (car cond)
	      (evl (caddr form) genv env n)
	    (evl (cadddr form) genv env n))
	(undefined))))
   (t (let ((args (evlist (cdr form) genv env n)))
	(if (defined args)
	    (if (operatorp (car form))
		(evlop (car form) args genv env n)
	      (evl (caddr (assoc (car form) genv))
		   genv
		   (bind (cadr (assoc (car form) genv)) args env)
		   (1- n)))
	  (undefined))))))

(defun evlist (forms genv env n)
  (declare (xargs :guard (and (form-listp forms) (genvp genv)
			      (alistp env) (natp n))
		  :measure (cons (1+ (acl2-count n)) (acl2-count forms))))
  (cond ((zp n) (undefined))
	((endp forms) nil)
	(t (let ((f (evl (car forms) genv env n))
		 (r (evlist (cdr forms) genv env n)))
	     (if (and (defined f) (defined r))
		 (cons (car f) r)
	       (undefined))))))
)

;;---------------------------------------------------------------------------
;; Now we define the semantics of a program, i.e. of a list of definitions, an
;; input variable list and a main program form. For a given list of inputs we
;; evaluate the main expression in an environment that binds the input
;; variables to the inputs.
;;---------------------------------------------------------------------------

(defun evaluate (defs vars main inputs n)
  (declare (xargs :guard (and (definition-listp defs)
			      (symbol-listp vars)
			      (formp main)
			      (true-listp inputs)
			      (natp n))))
  (evl main (construct-genv defs) (bind vars inputs nil) n))


;;===========================================================================
;; Some tests
;;---------------------------------------------------------------------------

(defthm first-test
  (equal
   (evaluate '((defun f (n) (* n n))) '(n) '(f (f n)) '(10) 1000000)
   '(10000))
  :rule-classes nil)

(defthm second-test
  (equal
   (evaluate '((defun fac (n) (if (equal n 0) 1 (* n (fac (1- n))))))
	     '(n) '(fac n) '(5) 1000000)
   '(120))
  :rule-classes nil)

;;
;; The following test evaluates the compiler on the factorial program.
;;

(defthm compiler-semantics-for-factorial
  (equal
   (evaluate (compiler-source)
	     '(defs vars main) '(compile-program defs vars main)
	     '(((defun fac (n) (if (equal n 0) 1 (* n (fac (1- n)))))) (n) (f n))
	     1000000)
   '(((DEFCODE FAC
	((PUSHV 0)
	 (PUSHC 0)
	 (OPR EQUAL)
	 (IF ((PUSHC 1))
	     ((PUSHV 0)
	      (PUSHV 1)
	      (OPR 1-)
	      (CALL FAC)
	      (OPR *)))
	 (POP 1)))
      ((PUSHV 0) (CALL F) (POP 1)))))
  :rule-classes nil)

;;
;; The next test proves, that the semantics of the compiler applied to the
;; factorial program is the same as compiling the factorial program using the
;; ACL2 implementation of the compiler.
;;
(defthm compiler-and-semantics
  (equal
   (compile-program
    '((defun fac (n) (if (equal n 0) 1 (* n (fac (1- n))))))
    '(n)
    '(fac n))
   (car (evaluate
	 (compiler-source)
	 '(defs vars main)
	 '(compile-program defs vars main)
	 '(((defun fac (n) (if (equal n 0) 1 (* n (fac (1- n)))))) (n) (fac n))
	 1000000)))
  :rule-classes nil)

;;
;; If we run the compiler's target code on the machine and apply it to the
;; factorial program, we get the same as if we evaluate the compiler source
;; code on that input. The following theorem is proved just by execution, but
;; it gives us an impression of what we in principle would have to prove for a
;; compiler correctness proof (not only for the factorial program, of course,
;; and under a lot more conditions).
;;

(defun rev (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x) nil
    (append (rev (cdr x)) (list (car x)))))

(defthm correct-compilation-on-factorial
  (equal
   (car (evaluate
	 (compiler-source)
	 '(defs vars main)
	 '(compile-program defs vars main)
	 '(((defun fac (n)
	      (if (equal n 0) 1 (* n (fac (1- n)))))) (n) (fac n))
	 1000000))
   (car (execute
	 (compile-program (compiler-source)
			  '(defs vars main)
			  '(compile-program defs vars main))
	 (rev '(((defun fac (n)
		   (if (equal n 0) 1 (* n (fac (1- n)))))) (n) (fac n)))
	 1000000)))
  :rule-classes nil)




;;===========================================================================
;; Well-formed programs:
;; ~~~~~~~~~~~~~~~~~~~~~
;; We don't need this here, so the definition is just for information. The
;; compiler correctness proof will depend on the well-formedness of forms to
;; be compiled.
;;===========================================================================
;;
;; First, the program has to be syntactically correct. Then, variables have to
;; be bound, functions have to be defined and applied to the correct number of
;; arguments. Operators have to have the correct number of arguments as well.
;;
;;===========================================================================

(mutual-recursion
(defun wellformed-form (form genv env)
  (declare (xargs :guard (and (genvp genv) (symbol-listp env))))
  (and
   ;; form is syntactically correct, and
   ;; ----------------------------------
   (formp form)
   ;; NIL is wellformed
   ;; -----------------
   (if (equal form 'nil) t
   ;; T is wellformed
   ;; ---------------
   (if (equal form 't) t
   ;; Variables are wellformed if they are bound
   ;; ------------------------------------------
   (if (symbolp form) (member form env)
   ;; Any atom which is not a variable is wellformed
   ;; ----------------------------------------------
   (if (atom form) t
   ;; QUOTE-forms are wellformed
   ;; --------------------------
   (if (equal (car form) 'QUOTE) t
   ;; Conditionals are wellformed if test, then, and else are
   ;; -------------------------------------------------------
   (if (equal (car form) 'IF) (wellformed-forms (cdr form) genv env)
   ;; Operator calls are unary or binary with one or two
   ;; wellformed argument forms
   ;; --------------------------------------------------
   (if (operatorp (car form))
       (or
        ;; unary
        ;; -----
        (and (member (car form) '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
				      LEN SYMBOLP CONSP ATOM LIST1))
	     (consp (cdr form))
	     (wellformed-form (cadr form) genv env)
	     (null (cddr form)))
        ;; binary
        ;; ------
        (and (member (car form) '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))
	     (consp (cdr form))
	     (wellformed-form (cadr form) genv env)
	     (consp (cddr form))
	     (wellformed-form (caddr form) genv env)
	     (null (cdddr form))))
   ;; Function calls are wellformed, if the function is defined and called
   ;; on the correct number of wellformed argument forms
   ;; --------------------------------------------------------------------
       (and (assoc (car form) genv)
	    (equal (len (cdr form)) (len (cadr (assoc (car form) genv))))
	    (wellformed-forms (cdr form) genv env)))))))))))

(defun wellformed-forms (flist genv env)
  (declare (xargs :guard (and (genvp genv) (symbol-listp env))))
  ;; Form lists are well-formed, if every form is
  ;; --------------------------------------------
  (and (form-listp flist)  ;; should not be necessary
       (if (consp flist)
	   (and (wellformed-form (car flist) genv env)
		(wellformed-forms (cdr flist) genv env))
	 (null flist))))
)

(defun wellformed-def (def genv)
  (declare (xargs :guard (genvp genv)))
  ;; A definition is well-formed, it its body is well-formed
  ;; w.r.t. the global environment and the formals parameter list
  ;; ------------------------------------------------------------
  (and (definitionp def)
       (wellformed-form (cadddr def) genv (caddr def))))

(defun wellformed-defs (defs genv)
  (declare (xargs :guard (genvp genv)))
  ;; A list of defintions is well-formed, if every definition is
  ;; -----------------------------------------------------------
  (and (definition-listp defs)  ;; should be unnecessary
       (if (consp defs)
	   (and (wellformed-def (car defs) genv)
		(wellformed-defs (cdr defs) genv))
	 (null defs))))

(defun wellformed-program (defs vars main)
  (declare (xargs :guard t))
  ;; A program is well-formed, if the declarations part is well-formed,
  ;; and if the main form is well-formed w.r.t. the global environment
  ;; and the list of (global) variables.
  ;; -----------------------------------
  (and (definition-listp defs)
       (wellformed-defs defs (construct-genv defs))
       (symbol-listp vars)
       (wellformed-form main (construct-genv defs) vars)))



(defthm wellformed-form-eqn
  (equal (wellformed-form form genv env)
  (and
   (formp form)
   (if (equal form 'nil) t
   (if (equal form 't) t
   (if (symbolp form) (member form env)
   (if (atom form) t
   (if (equal (car form) 'QUOTE) t
   (if (equal (car form) 'IF) (wellformed-forms (cdr form) genv env)
   (if (operatorp (car form))
       (or
        (and (member (car form) '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
				      LEN SYMBOLP CONSP ATOM LIST1))
	     (consp (cdr form))
	     (wellformed-form (cadr form) genv env)
	     (null (cddr form)))
        (and (member (car form) '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))
	     (consp (cdr form))
	     (wellformed-form (cadr form) genv env)
	     (consp (cddr form))
	     (wellformed-form (caddr form) genv env)
	     (null (cdddr form))))
       (and (assoc (car form) genv)
	    (equal (len (cdr form)) (len (cadr (assoc (car form) genv))))
	    (wellformed-forms (cdr form) genv env)))))))))))
  :rule-classes ((:definition
		  :clique (wellformed-form wellformed-forms)
		  :controller-alist
		  ((wellformed-forms t nil nil) (wellformed-form t nil nil))))
  :hints (("Goal" :in-theory (disable operatorp member))))


(defthm wellformed-forms-eqn
  (equal (wellformed-forms flist genv env)
  (and (form-listp flist)
       (if (consp flist)
	   (and (wellformed-form (car flist) genv env)
		(wellformed-forms (cdr flist) genv env))
	 (null flist))))
  :rule-classes ((:definition
		  :clique (wellformed-form wellformed-forms)
		  :controller-alist
		  ((wellformed-forms t nil nil) (wellformed-form t nil nil))))
  :hints (("Goal" :in-theory (disable wellformed-form))))






