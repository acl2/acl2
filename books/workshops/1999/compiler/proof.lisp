;;===========================================================================
;; Copyright (C) 1999 Institut fuer Informatik, University of Kiel, Germany
;;===========================================================================
;; File:         proof.lisp
;; Author:       Wolfgang Goerigk
;; Content:      ACL2 Austin CP correctness proof
;; as of:        01/06/99, University of Kiel, Germany
;;---------------------------------------------------------------------------
;; $Revision: 1.9 $
;; $Id: proof.lisp,v 1.9 1999/10/02 20:06:16 wg Exp wg $
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
;;
;; The Compiler Correctness Proof - Main Part
;;
;;===========================================================================
;;
;; This file contains the main part of the compiler correctness proof for the
;; miniComLisp (called SL in the paper) compiler defined in "compiler.lisp"
;; with respect to the semantics of miniComLisp as defined in "evaluator.lisp"
;; and the machine semantics as defined in "machine.lisp". In this book we
;; prove compiler correctness for expressions and for programs.
;;
;;---------------------------------------------------------------------------
;;
;; Some notes (in particular w.r.t. non-well-formed programs)
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;
;; The compiler generates (PUSHV -1) for unbound variables. Variable lookup in
;; the evaluator returns nil in that case. Thus, we need well-formedness of
;; programs (as defined in "evaluator.lisp") in order to prove compiler
;; correctness. We could generate (PUSHC nil) for unbound variable access in
;; order to meet the semantics (of those non well-formed programs), but with
;; the remarks below we'll fail anyway.
;;
;; If a function or operator is called on a wrong number of arguments, the
;; compiler generates wrong code w.r.t. the evaluator. If there are too many
;; actuals, then the evaluator consumes the FIRST n (n = number of formals)
;; and ignores the rest, whereas the compiled code consumes the LAST n
;; arguments (since the stack is built up in reverse order).
;;
;;   (evl '(cons 3 4 5) () () 1)                            = ((3 . 4))
;;         ~~~~~~~~~~~~
;;   (msteps (compile-form '(cons 3 4 5) () 0) () () 1)     = ((4 . 5) 3)
;;                          ~~~~~~~~~~~~
;;
;; We could fix this by changing the compiler to ignore superfluous argument
;; forms as well. But if there are not enough arguments, then the evaluator
;; adds nil's, whereas the compiled code on the machine consumes some
;; preceeding stack cells:
;;
;;   (evl '(cons 3) () () 1)                                = ((3))
;;         ~~~~~~~~
;;   (msteps (compile-form '(cons 3) () 0) () '(a b c) 1)   = ((A . 3) B C)
;;                          ~~~~~~~~
;;
;; We did not like changing the compiler to generate code that meets this
;; (latter) kind of dynamic behavior of mal-formed programs. We could make the
;; compiler partial in that case, i.e. to add a "regular compiler result"
;; condition to the compiler correctness conjecture. However, since we are in
;; a logic of total functions, this would force us to make the compiler
;; definition error-strict, which is very unelegant, in particular because we
;; primarily use the compiler in order to show the Thompson-effect.
;;
;;===========================================================================

(in-package "ACL2")
(include-book "proof1")
(include-book "../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;;---------------------------------------------------------------------------
;; Now we are going to prove that the compiled code for a function or operator
;; call works as expected, i.e. it runs through the compiled argument forms
;; and the calls the code for the function or applies the operator. In
;; particular, if the code for (f e1 ... en) is defined, then it is for all
;; argument forms and the function body.
;;---------------------------------------------------------------------------


(defun function-callp (form)
  (and (formp form)
       (not (base-form form))
       (not (equal (car form) 'if))
       (not (operatorp (car form)))))


(defun operator-callp (form)
  (and (formp form)
       (not (base-form form))
       (not (equal (car form) 'if))
       (operatorp (car form))))


;;---------------------------------------------------------------------------
;; Operator Call Strictness and Values

(defthm arguments-strictness-function-call
  (implies
   (and (function-callp form)
	(defined (msteps (compile-form form cenv top) code stack n)))
   (defined (msteps (compile-forms (cdr form) cenv top) code stack n))))

(defthm arguments-strictness-operator-call
  (implies
   (and (operator-callp form)
	(defined (msteps (compile-form form cenv top) code stack n)))
   (defined (msteps (compile-forms (cdr form) cenv top) code stack n))))

(in-theory (disable operatorp defined))


;;---------------------------------------------------------------------------
;; Function Calls


;; By "call-f-will-execute-the-code-for-f" we will know, that (get-code f
;; code) is the compiled body of f with the additional (POP n), if code is
;; (download (compile-defs dcls)) and if there exists a definition of f in
;; (construct-genv dcls).
;;
(defthm call-f-will-execute-the-code-for-f-new
  (implies (assoc f (construct-genv dcls))
 	   (equal (append
 		   (compile-form (caddr (assoc f (construct-genv dcls)))
 				 (cadr (assoc f (construct-genv dcls)))
 				 0)
 		   (list (list 'pop
 			       (len (cadr (assoc f (construct-genv dcls)))))))
		  (cdr (assoc f (download (compile-defs dcls))))))
  :hints (("Goal" :in-theory (enable get-body get-vars get-code)))
  :rule-classes nil)


(defthm call-f-will-execute-the-code-for-f
  (implies (and (function-callp (cons f args))
		(wellformed-form (cons f args) (construct-genv dcls) cenv))
	   (equal (append
		   (compile-form (get-body f (construct-genv dcls))
				 (get-vars f (construct-genv dcls))
				 0)
		   (list (list 'pop (len (get-vars f (construct-genv dcls))))))
		  (get-code f (download (compile-defs dcls)))))
  :hints (("Goal'4'" :by call-f-will-execute-the-code-for-f-new)))


(in-theory (disable get-body get-vars))

;; This rule should make some of the strictness rules below unnecessary, but
;; it doesn't.
;;
(defthm defined-if-equal-value
  (implies (and (equal (msteps m1 code1 stack1 n1)
		       (msteps m2 code2 stack2 n2))
		(defined (msteps m1 code1 stack1 n1)))
	   (defined (msteps m2 code2 stack2 n2)))
     :hints (("Goal" :in-theory (disable msteps msteps-eqn))))



(defthm machine-value-on-call
  (implies
   (and (function-callp (cons f args))
	(defined (msteps (compile-form (cons f args) cenv top)
			 (download (compile-defs dcls)) stack n)))
   (equal (msteps (compile-form (cons f args) cenv top)
		  (download (compile-defs dcls)) stack n)
	  (msteps (get-code f (download (compile-defs dcls)))
		  (download (compile-defs dcls))
		  (msteps (compile-forms args cenv top)
			  (download (compile-defs dcls)) stack n)
		  (1- n)))))

(defthm machine-strictness-on-call
  (implies
   (and (function-callp (cons f args))
	(defined (msteps (compile-form (cons f args) cenv top)
			 (download (compile-defs dcls)) stack n)))
   (defined (msteps (get-code f (download (compile-defs dcls)))
		    (download (compile-defs dcls))
		    (msteps (compile-forms args cenv top)
			    (download (compile-defs dcls)) stack n)
		    (1- n))))
     :hints (("Goal"
	      :use (defined-if-equal-value machine-value-on-call)
	      :in-theory (disable defined msteps msteps-eqn get-code))))


(in-theory (disable function-callp base-form get-code))


;; For the next three theorems it turns out that we have to disable
;; msteps-distributes-over-append, because it normalizes calls of msteps the
;; wrong way here. We need to preserve the append that we get from get-code.
;;
(defthm msteps-doa
  (equal (msteps m2 code (msteps m1 code stack n) n)
	 (msteps (append m1 m2) code stack n)))

(in-theory (disable MSTEPS-DISTRIBUTES-OVER-APPEND))

(defthm compiled-body-value-1
  (implies
   (and (function-callp (cons f args))
  	(wellformed-form (cons f args) (construct-genv dcls) cenv)
  	(defined (msteps (compile-form (cons f args) cenv top)
  			 (download (compile-defs dcls)) stack n)))
   (equal
    (msteps (compile-form (cons f args) cenv top)
	    (download (compile-defs dcls)) stack n)
    (msteps (list (list 'pop (len (get-vars f (construct-genv dcls)))))
	     (download (compile-defs dcls))
	     (msteps (compile-form (get-body f (construct-genv dcls))
				   (get-vars f (construct-genv dcls)) 0)
		     (download (compile-defs dcls))
		     (msteps (compile-forms args cenv top)
			     (download (compile-defs dcls)) stack n)
		     (1- n))
	     (1- n)))))

(defthm compiled-body-strictness-1
  (implies
   (and (function-callp (cons f args))
  	(wellformed-form (cons f args) (construct-genv dcls) cenv)
  	(defined (msteps (compile-form (cons f args) cenv top)
  			 (download (compile-defs dcls)) stack n)))
   (defined
     (msteps (list (list 'pop (len (get-vars f (construct-genv dcls)))))
	     (download (compile-defs dcls))
	     (msteps (compile-form (get-body f (construct-genv dcls))
				   (get-vars f (construct-genv dcls)) 0)
		     (download (compile-defs dcls))
		     (msteps (compile-forms args cenv top)
			     (download (compile-defs dcls)) stack n)
		     (1- n))
	     (1- n)))))

(defthm compiled-body-strictness-2
  (implies
   (and (function-callp (cons f args))
  	(wellformed-form (cons f args) (construct-genv dcls) cenv)
  	(defined (msteps (compile-form (cons f args) cenv top)
  			 (download (compile-defs dcls)) stack n)))
   (defined
     (msteps (compile-form (get-body f (construct-genv dcls))
				   (get-vars f (construct-genv dcls)) 0)
		     (download (compile-defs dcls))
		     (msteps (compile-forms args cenv top)
			     (download (compile-defs dcls)) stack n)
		     (1- n))))
  :hints (("Goal"
	   :use
	   (:instance
	    machine-strictness1
	    (m1 (compile-form (get-body f (construct-genv dcls))
			      (get-vars f (construct-genv dcls)) 0))
	    (m2 (list (list 'pop (len (get-vars f (construct-genv dcls))))))
	    (code (download (compile-defs dcls)))
	    (stack (msteps (compile-forms args cenv top)
			   (download (compile-defs dcls)) stack n))
	    (n (1- n))))))

(in-theory (enable MSTEPS-DISTRIBUTES-OVER-APPEND))
(in-theory (disable msteps-doa))


;;---------------------------------------------------------------------------
;; Well-formedness properties for function calls  -> evaluator.lisp
;;---------------------------------------------------------------------------

(in-theory (enable function-callp base-form get-code))


(defthm argument-forms-are-wellformed-for-function-call
  (implies (and (function-callp form)
 		(wellformed-form form genv env))
 	   (wellformed-forms (cdr form) genv env))
  :hints (("Goal" :use wellformed-form-eqn)))

(defthm argument-forms-are-wellformed-for-operator-call
  (implies (and (operator-callp form)
 		(wellformed-form form genv env))
 	   (wellformed-forms (cdr form) genv env))
  :hints (("Goal" :use wellformed-form-eqn
	   :in-theory (disable wellformed-form))))

(defthm car-forms-wellformed
  (implies (wellformed-forms forms genv env)
	   (wellformed-form (car forms) genv env)))

(defthm cadr-forms-wellformed
  (implies (wellformed-forms forms genv env)
	   (wellformed-form (cadr forms) genv env)))

(defthm function-is-defined
  (implies (and (function-callp form) (wellformed-form form genv env))
	   (assoc (car form) genv))
  :hints (("Goal" :use wellformed-form-eqn)))


(in-theory (enable get-definition get-vars get-body))
(in-theory (disable wellformed-form wellformed-forms))


(defthm wff-2
  (implies (and (wellformed-defs defs genv)
		(assoc name (construct-genv defs)))
	   (wellformed-def (get-definition name defs) genv)))

(defthm wff-3
  (implies (and (definition-listp defs)
		(assoc name (construct-genv defs)))
	   (equal (get-definition name defs)
		  (list 'defun name (get-vars name (construct-genv defs))
			(get-body name (construct-genv defs))))))

(in-theory (disable get-definition construct-genv))

;; If we prove this, the proof of wff-4 below runs faster.
;;
(defthm wellformed-defs-definition-listp
  (implies (wellformed-defs defs (construct-genv defs))
	   (definition-listp defs))
  :rule-classes nil)

(defthm wff-4
  (implies (and (wellformed-defs defs (construct-genv defs))
		(assoc name (construct-genv defs)))
	   (equal (get-definition name defs)
		  (list 'defun name (get-vars name (construct-genv defs))
			(get-body name (construct-genv defs)))))
     :hints (("Goal" :use wellformed-defs-definition-listp)))


(in-theory (disable get-body get-vars))


(defthm wellformed-defs-implies-wellformed-bodies
  (implies (and (wellformed-defs defs (construct-genv defs))
		(assoc name (construct-genv defs)))
	   (wellformed-form (get-body name (construct-genv defs))
			    (construct-genv defs)
			    (get-vars name (construct-genv defs))))
    :hints (("Goal" :use (:instance wff-2 (genv (construct-genv defs))))))

(defthm wellformed-function-body
  (implies (and (assoc (car form) (construct-genv dcls))
		(wellformed-defs dcls (construct-genv dcls)))
	   (wellformed-form (get-body (car form) (construct-genv dcls))
			    (construct-genv dcls)
			    (get-vars (car form)
				      (construct-genv dcls)))))

;;---------------------------------------------------------------------------
;; Operator Calls on the Machine

(defthm machine-on-operator-call
 (implies
  (and (operator-callp (cons op args))
       (defined (msteps (compile-form (cons op args) cenv top) code stack n)))
  (equal (msteps (compile-form (cons op args) cenv top) code stack n)
	 (opr op code (msteps (compile-forms args cenv top) code stack n))))
  :hints (("Goal" :in-theory (disable opr operatorp))))


(in-theory (disable mcar-is-like-car mcdr-is-like-cdr m1+-is-like-1+
		    m1--is-like-1- mappend-is-like-append
		    mmember-is-like-member massoc-is-like-assoc
		    m+-is-like-+  m--is-like--  m*-is-like-*))

;;---------------------------------------------------------------------------
;; Operator Calls

(defthm unary-for-args
  (implies (and (consp args) (null (cdr args)))
	   (equal (append (rev args) stack) (cons (car args) stack))))

(defthm binary-for-args
  (implies (and (consp args) (consp (cdr args)) (null (cddr args)))
	   (equal (append (rev args) stack)
		  (append (list (cadr args) (car args)) stack))))

(defthm unary-for-args-evlist
  (implies (and (consp args) (null (cdr args))
		(defined (evlist args genv env n)))
	   (and (consp (evlist args genv env n))
		(null (cdr (evlist args genv env n)))))
  :hints (("Goal" :induct (form-listp-induction args))))

(defthm binary-for-args-evlist
  (implies (and (consp args) (consp (cdr args)) (null (cddr args))
		(defined (evlist args genv env n)))
	   (and (consp (evlist args genv env n))
		(consp (cdr (evlist args genv env n)))
		(null (cddr (evlist args genv env n)))))
  :hints (("Goal" :induct (form-listp-induction args))))

(defthm unary-for-argsevlist-append
  (implies (and (consp args) (null (cdr args))
		(defined (evlist args genv env n)))
	   (equal (append (rev (evlist args genv env n)) stack)
		  (cons (car (evlist args genv env n)) stack))))

(defthm binary-for-argsevlist-append
  (implies (and (consp args) (consp (cdr args)) (null (cddr args))
		(defined (evlist args genv env n)))
	   (equal (append (rev (evlist args genv env n)) stack)
		  (append (list (cadr (evlist args genv env n))
				(car (evlist args genv env n)))
			  stack))))

(defthm unary-has-one-argument
  (implies (and (member op '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
				 LEN SYMBOLP CONSP ATOM LIST1))
		(wellformed-form (cons op args) genv cenv))
	   (and (consp args) (null (cdr args)))))

(defthm binary-has-two-arguments
  (implies (and (member op '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))
		(wellformed-form (cons op args) genv cenv))
	   (and (consp args) (consp (cdr args)) (null (cddr args)))))

(defthm unary-for-operators
  (implies (and (member op '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
				 LEN SYMBOLP CONSP ATOM LIST1))
		(wellformed-form (cons op args) genv cenv)
		(defined (evlist args genv env n)))
	   (equal (append (rev (evlist args genv env n)) stack)
		  (cons (car (evlist args genv env n)) stack)))
  :hints (("Goal" :use (unary-has-one-argument unary-for-argsevlist-append))))

(defthm binary-for-operators
  (implies (and (member op '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))
		(wellformed-form (cons op args) genv cenv)
		(defined (evlist args genv env n)))
	   (equal (append (rev (evlist args genv env n)) stack)
		  (append (list (cadr (evlist args genv env n))
				(car (evlist args genv env n)))
			  stack)))
  :hints (("Goal" :use (binary-has-two-arguments binary-for-argsevlist-append))))

(defthm correct-opcall-unary
 (implies
  (and (member op '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
				 LEN SYMBOLP CONSP ATOM LIST1))
       (wellformed-form (cons op args) genv cenv)
       (defined (evlist args genv env n)))
  (equal (opr op code (append (rev (evlist args genv env n)) stack))
	 (cons (car (evlop op (evlist args genv env n) genv env n)) stack)))
 :hints (("Goal" :in-theory (disable member))))

(defthm correct-opcall-binary
 (implies
  (and (member op '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))
       (wellformed-form (cons op args) genv cenv)
       (defined (evlist args genv env n)))
  (equal (opr op code (append (rev (evlist args genv env n)) stack))
	 (cons (car (evlop op (evlist args genv env n) genv env n)) stack)))
 :hints (("Goal" :in-theory (disable member))))

(defthm operator-unary-or-binary
  (iff (operatorp op)
	 (or (member op '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
			      LEN SYMBOLP CONSP ATOM LIST1))
	     (member op '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))))
  :hints (("Goal" :in-theory (enable operatorp)))
  :rule-classes nil)

(defthm correct-opcall
 (implies
  (and (operatorp op)
       (wellformed-form (cons op args) genv cenv)
       (defined (evlist args genv env n)))
  (equal (opr op code (append (rev (evlist args genv env n)) stack))
	 (cons (car (evlop op (evlist args genv env n) genv env n)) stack)))
 :hints (("Goal" :use operator-unary-or-binary)))


;;---------------------------------------------------------------------------
;; Conditionals

(defthm wellformed-cond
  (implies (and (equal (car x) 'if)
		(wellformed-form x genv cenv))
	   (wellformed-form (cadr x) genv cenv)))

(defthm wellformed-then
  (implies (and (equal (car x) 'if)
		(wellformed-form x genv cenv))
	   (wellformed-form (caddr x) genv cenv)))

(defthm wellformed-else
  (implies (and (equal (car x) 'if)
		(wellformed-form x genv cenv))
	   (wellformed-form (cadddr x) genv cenv)))

(defthm compiler-on-if
  (implies
   (equal (car form) 'if)
   (equal (compile-form form cenv top)
	  (append (compile-form (cadr form) cenv top)
		  (list (list 'if (compile-form (caddr form) cenv top)
			      (compile-form (cadddr form) cenv top)))))))

(defthm cond-strictness
  (implies
   (and (equal (car form) 'IF)
	;;(wellformed-form form genv cenv)
	(defined (msteps (compile-form form cenv top) code stack n)))
   (defined (msteps (compile-form (cadr form) cenv top) code stack n)))
  :hints (("Goal" :in-theory (enable defined))))

(defthm then-strictness
 (implies
  (and (equal (car form) 'if)
       (defined (msteps (compile-form form cenv top) code stack n))
       (car (msteps (compile-form (cadr form) cenv top) code stack n)))
  (defined (msteps (compile-form (caddr form) cenv top)
		      code
		      (cdr (msteps (compile-form (cadr form) cenv top)
				   code stack n))
		      n))))

(defthm else-strictness
 (implies
  (and (equal (car form) 'if)
       (defined (msteps (compile-form form cenv top) code stack n))
       (not (car (msteps (compile-form (cadr form) cenv top) code stack n))))
  (defined (msteps (compile-form (cadddr form) cenv top)
		      code
		      (cdr (msteps (compile-form (cadr form) cenv top)
				   code stack n))
		      n))))

;; Crucial for strictness in case the condition is defined but not the
;; conditional
;;
(defthm then-else-strictness
  (implies
   (and (equal (car form) 'if)
	(defined (msteps (compile-form form cenv top) code stack n))
	(not (defined (msteps (compile-form (caddr form) cenv top)
			      code
			      (cdr (msteps (compile-form (cadr form) cenv top)
					   code stack n))
			      n))))
   (defined (msteps (compile-form (cadddr form) cenv top)
		    code
		    (cdr (msteps (compile-form (cadr form) cenv top)
				 code stack n))
		    n))))

(defthm evl-if-true
  (implies (and (equal (car form) 'if)
		(car (evl (cadr form) genv env n))
		(defined (evl (cadr form) genv env n)))
	   (equal (evl form genv env n)
		  (evl (caddr form) genv env n))))

(defthm evl-if-false
  (implies (and (equal (car form) 'if)
		(not (car (evl (cadr form) genv env n)))
		(defined (evl (cadr form) genv env n)))
	   (equal (evl form genv env n)
		  (evl (cadddr form) genv env n))))

;; The following rule proposes a case split on the value of the condition in
;; case we prove definedness for the conditional. We prove definedness of the
;; condition. But then, due to the non-strictness of the conditional, we have
;; either definedness of condition and the then-branch, or of the condition
;; and the else-branch, depending on the value of the condition.
;;
(defthm evl-if-case-split
  (implies (and (equal (car form) 'if)
		(defined (evl (cadr form) genv env n)))
	   (equal (defined (evl form genv env n))
		  (if (car (evl (cadr form) genv env n))
		      (defined (evl (caddr form) genv env n))
		    (defined (evl (cadddr form) genv env n))))))


;;---------------------------------------------------------------------------
;; The induction scheme that we will use to prove the compiler correctness for
;; forms and form lists.
;; It is a combined structural and computational induction (on n). If flag is
;; true, we think of proving the theorem for a form x, and we use the
;; structural induction hypothesis for conditionals and argument lists (of
;; functions or operators) and the computational induction hypothesis in case
;; of the function call (where we evaluate resp. execute the function
;; body).
;; If flag is false, we think of proving the theorem for form lists and assume
;; the structural induction hypothesis for the form (car x) and the form list
;; (cdr x).
;;---------------------------------------------------------------------------

(defun compiler-induction (flag x cenv env top dcls stack n)
  (declare (xargs :measure (cons (1+ (acl2-count n)) (acl2-count x))))
  (if (or (zp n) (atom x))
      (list x cenv env top dcls stack n)
    (if flag
	(if (base-form x) (list x cenv env top dcls stack n)
	  (if (equal (car x) 'if)
	      (list (compiler-induction
		     t (cadr x) cenv env top dcls stack n)
		    (compiler-induction
		     t (caddr x) cenv env top dcls
		     (cdr (msteps (compile-form (cadr x) cenv top)
				  (download (compile-defs dcls))
				  stack n))
		     n)
		    (compiler-induction
		     t
		     (cadddr x) cenv env top dcls
		     (cdr (msteps (compile-form (cadr x) cenv top)
				  (download (compile-defs dcls))
				  stack n))
		     n))
	    (if (operatorp (car x))
		(compiler-induction
		   nil
		   (cdr x) cenv env top dcls stack n)
	      (list (compiler-induction
		     nil
		     (cdr x) cenv env top dcls stack n)
		    (compiler-induction
		     t
		     (get-body (car x) (construct-genv dcls))
		     (get-vars (car x) (construct-genv dcls))
		     (bind cenv (rev (get-stack-frame cenv top stack)) env)
		     0
		     dcls
		     (msteps (compile-forms (cdr x) cenv top)
			     (download (compile-defs dcls))
			     stack n)
		     (1- n))))))
      (list (compiler-induction
	     t (car x) cenv env top dcls stack n)
	    (compiler-induction
	     nil
	     (cdr x)
	     cenv
	     env
	     (1+ top)
	     dcls
	     (msteps (compile-form (car x) cenv top)
		     (download (compile-defs dcls))
		     stack n)
	     n)))))


;;---------------------------------------------------------------------------
;; A version of cc-theorem for form lists, i.e. argument lists to function or
;; operator calls. This is the same as cc-theorem, but for evlist and
;; compile-forms. It says that the compiled code for form lists appends the
;; reverse of the values returned by evlist to the stack, that is it pushes
;; value by value onto the stack.
;;---------------------------------------------------------------------------

(defmacro forms-theorem (forms cenv env top dcls stack n)
  `(implies (and (natp ,top)
		 (wellformed-defs ,dcls (construct-genv ,dcls))
	         (wellformed-forms ,forms (construct-genv ,dcls) ,cenv)
		 (defined (msteps (compile-forms ,forms ,cenv ,top)
				  (download (compile-defs ,dcls));; code
				  ,stack
				  ,n)))
	    (and
	     (defined
	       (evlist ,forms
		       (construct-genv ,dcls)
		       (bind ,cenv (rev (get-stack-frame ,cenv ,top ,stack))
			     ,env);; (nthcdr (+ ,top (len ,cenv)) ,stack))
		       ,n))
	     (equal
	      (msteps (compile-forms ,forms ,cenv ,top)
		      (download (compile-defs ,dcls));; code
		      ,stack
		      ,n)
	      (append
	       (rev (evlist ,forms
			    (construct-genv ,dcls);; genv (evaluator)
			    (bind ,cenv (rev (get-stack-frame ,cenv ,top ,stack))
				  ,env);; (nthcdr (+ ,top (len ,cenv)) ,stack))
			    ,n))
	       ,stack)))))


;;---------------------------------------------------------------------------
;; some theorems about the definedness of the evaluator. Basically we want to
;; run through the structure of the forms and prove that whenever the
;; semantics of the sub-forms is defined then so is the semantics of the form
;; itself (but with respect to non-strictness of IF, and with (n-1) for
;; calls).
;;---------------------------------------------------------------------------
;; Base forms
;;

(defthm evl-defined-base-form
  (implies (and (not (zp n))
		(base-form form))
	   (defined (evl form genv env n)))
  :hints (("Goal" :in-theory (enable defined))))


;;---------------------------------------------------------------------------
;; Operator Calls
;;


;; This rule is crucial to the definedness part of the proof for operator
;; calls 1/4.2.
;;
(defthm evlop-defined-opcalls
  (implies (and (not (zp n))
		(defined (evlist forms genv env n))
		(operatorp op))
	   (defined (evlop op (evlist forms genv env n) genv env n)))
  :hints (("Goal" :in-theory (enable defined operatorp))))


(defthm evl-value-opcalls
  (implies (and (not (zp n))
		(operatorp op)
	        (defined (evlist args genv env n)))
	   (equal (evl (cons op args) genv env n)
		  (evlop op (evlist args genv env n) genv env n)))
  :hints (("Goal" :in-theory (enable operatorp))))

(in-theory (enable defined))


;;---------------------------------------------------------------------------
;; Argument Lists
;;

;; This one is crucial to the definedness part of the proof for form lists
;; 1/6.2. We also need get-stack-frame-shifts below to get rid of (1+ top) in
;; the compile-form for the cdr.
;;
(defthm evlist-defined
  (implies (and (not (zp n))
		(defined (evl form genv env n))
		(defined (evlist forms genv env n)))
	   (defined (evlist (cons form forms) genv env n))))

(defthm append-and-rev
  (equal (append (rev (cons x l)) s)
	 (append (rev l) (cons x s))))


;; This rule is crucial for the value part of the proof for form lists 1/6.1.
;;
(defthm evlist-and-rev
 (implies (and (defined (evl form genv env n))
	       (defined (evlist forms genv env n)))
 (equal (append (rev (evlist forms genv env n))
		    (cons (car (evl form genv env n)) stack))
	    (append (rev (evlist (cons form forms) genv env n)) stack))))


;; This rule is crucial to the definedness and the value part of the proof for
;; form lists 1/6.2 and 1/6.1.
;;
(defthm get-stack-frame-shifts
  (implies (natp top)
	   (equal (get-stack-frame cenv (1+ top) (cons x s))
		  (get-stack-frame cenv top s))))


;; We need this one in 1/6 to see how argument form lists are built. We want
;; to disable compile-forms. The rule says that compile-forms maps
;; compile-form over forms and thats all we need to know.
;;
(defthm compile-forms-eqn
  (equal (compile-forms (cons form forms) cenv top)
	 (append (compile-form form cenv top)
		 (compile-forms forms cenv (1+ top)))))

(in-theory (disable compile-forms))

;; This one is crucial in the form lists part 1/6 to get the
;; non-wellformed-cases done.
;;
(defthm wellformed-form-lists
  (implies (wellformed-forms (cons form forms) genv env)
	   (and (wellformed-form form genv env)
		(wellformed-forms forms genv env))))

(in-theory (disable defined evlist))
(in-theory (disable operatorp))



;;---------------------------------------------------------------------------
;; Crucial properties for function calls
;;---------------------------------------------------------------------------
;; We have to know, that if the argument values (i.e. (evlist (cdr form) genv
;; env n)) are on top of the stack in reverse order, then (rev
;; (get-stack-frame (get-vars ...) 0 stack) takes exactly these
;; values. Moreover, we want to know that the machine semantics of (POP n)
;; pops the argument values from the stack and leaves the result of the
;; function call on top of the old stack. That is, (POP n), applied to (cons
;; (evl ...) (append (rev (evlist ...) stack))), returns (cons (evl ...) stack).
;;

(defthm rev-rev
  (implies (true-listp l) (equal (rev (rev l)) l)))

(defthm rev-len
  (implies (true-listp l) (equal (len (rev l)) (len l))))

(defthm tlp-rev
  (implies (true-listp l) (true-listp (rev l))))

(defthm mytake-len
  (implies (true-listp vals)
	   (equal (mytake (len vals) (append vals stack)) vals)))

(defthm nthcdr-len
  (implies (true-listp vals)
	   (equal (nthcdr (len vals) (append vals stack)) stack)))

(defthm nthcdr-help
  (implies (and (true-listp vals1);;(true-listp vals2)
		(equal (len vals1) (len vals2)))
	   (equal (nthcdr (len vals2) (append vals1 stack))
		  stack)))

(defthm nthcdr-len-rev
  (implies (true-listp vals)
	   (equal (nthcdr (len vals) (append (rev vals) stack)) stack)))

(defthm mytake-len-rev
  (implies (true-listp vals)
	   (equal (rev (mytake (len vals) (append vals stack)))
		  (rev vals))))

(defthm mytake-len-rev-1
  (implies (true-listp vals)
	   (equal (rev (mytake (len vals) (append (rev vals) stack)))
		  vals))
  :hints (("Goal" :do-not-induct t
	   :use (:instance mytake-len-rev (vals (rev vals))))))


(defthm rev-get-stack-frame
  (implies (and (true-listp vals)
		(equal (len vars) (len vals)))
	   (equal (rev (get-stack-frame vars 0 (append (rev vals) stack)))
		  vals)))

(defthm len-get-vars
  (implies (and (function-callp (cons f args))
		(wellformed-form (cons f args) genv cenv))
	   (equal (len (get-vars f genv))
		  (len args)))
  :hints (("Goal" :in-theory (enable get-vars))))

(defthm evlist-preserves-length
  (implies (defined (evlist args genv env n))
	   (and (true-listp (evlist args genv env n))
		(equal (len (evlist args genv env n)) (len args))))
     :hints (("Goal" :induct (form-listp-induction args)
	             :in-theory (enable evlist))))

(defthm evlist-values-in-new-stack-frame
  (implies (and (wellformed-defs dcls genv)
		(function-callp (cons f args))
		(wellformed-form (cons f args) genv cenv)
		;;(assoc f genv)
		(defined (evlist args genv env n)))
	   (equal
	    (rev (get-stack-frame
		  (get-vars f genv) 0
		  (append (rev (evlist args genv env n)) stack)))
	    (evlist args genv env n)))
  :hints (("Goal"
	   :in-theory (disable get-stack-frame function-callp base-form)
	   :use (:instance rev-get-stack-frame
			      (vals (evlist args genv env n))
			      (vars (get-vars f genv))))))


;; This rule tells the prover in case 1/5.1 (values for function call) to
;; split the proof into 2 cases, that is to prove that the top of stack is the
;; value of the function body, and that nthcdr of the cdr is the original
;; stack. The latter is by nthcdr-evlist below, and the former by
;; evlist-on-function-calls and evlist-values-in-new-stack-frame.
;;
(defthm msteps-pop
  (implies (defined (msteps (list (list 'POP (len args))) code stack n))
	   (equal (msteps (list (list 'POP (len args))) code stack n)
		  (cons (car stack) (nthcdr (len args) (cdr stack)))))
     :hints (("Goal" :in-theory (enable msteps))))


;; This rule is needed for nthcdr-evlist-1 below.
;;
(defthm nthcdr-evlist
  (implies (defined (evlist args genv env n))
	   (equal (nthcdr (len args)
			  (append (rev (evlist args genv env n)) stack))
		  stack)))

;; This rule is crucial for the cdr part of the proof in case 1/5.1. It says
;; that popping the arguments returns the old stack
;;
(defthm nthcdr-evlist-1
  (implies (and (function-callp (cons f args))
		(wellformed-form (cons f args) genv cenv)
		(wellformed-defs dcls genv)
	        (defined (evlist args genv env n)))
	   (equal (nthcdr (len (get-vars f genv))
			  (append (rev (evlist args genv env n)) stack))
		  stack))
  :hints (("Goal" :use (nthcdr-evlist len-get-vars))))


;;The following rule are needed if we want to disable all of those many
;;functions.
;;

(defthm natp1+ (implies (natp top) (natp (+ 1 top))))

(defthm fcp
  (implies (wellformed-form x (construct-genv dcls) cenv)
	   (equal (function-callp x)
		  (and (consp x) (not (base-form x))
		       (not (equal (car x) 'if))
		       (not (operatorp (car x))))))
  :rule-classes :rewrite)

(defthm ocp
  (implies (wellformed-form x (construct-genv dcls) cenv)
	   (equal (operator-callp x)
		  (and (consp x) (not (base-form x))
		       (not (equal (car x) 'if))
		       (operatorp (car x)))))
  :rule-classes :rewrite)

(defthm evl-on-function-calls
  (implies (and (function-callp (cons f args))
		(defined (evl (get-body f genv)
		       genv
		       (bind (get-vars f genv) (evlist args genv env n) env)
		       (1- n)))
		(defined (evlist args genv env n)))
	   (equal (evl (cons f args) genv env n)
		  (evl (get-body f genv)
		       genv
		       (bind (get-vars f genv) (evlist args genv env n) env)
		       (1- n))))
     :hints (("Goal" :in-theory (enable evl get-body get-vars))))

(in-theory (enable defined))

(defthm msteps-nil
  (implies (and (defined stack) (not (zp n)))
	   (equal (msteps nil code stack n) stack))
  :hints (("Goal" :in-theory (disable zp))))

(defthm evlist-on-non-integers
  (implies (not (integerp n)) (not (defined (evlist forms genv env n))))
  :hints (("Goal" :in-theory (enable evlist))))

(defthm evlist-on-non-conses
  (implies (and (not (zp n)) (not (consp x)))
	   (defined (evlist x genv env n)))
  :hints (("Goal" :in-theory (enable evlist))))

(defthm evlist-on-non-conses-2
  (implies (and (not (consp x)) (not (defined (evlist x genv env n))))
	   (zp n)))

(defthm msteps-on-zp-n
  (implies (zp n) (not (defined (msteps x code stack n)))))

(in-theory (disable defined))

(defthm non-conses-are-base-forms
  (implies (not (consp x)) (base-form x)))

(defthm compile-forms-on-nil
  (implies (not (consp x)) (null (compile-forms x cenv top)))
  :hints (("Goal" :in-theory (enable compile-forms))))

(defthm msteps-on-compile-forms-nil
  (implies (and (defined (msteps (compile-forms x cenv top) code stack n))
		(not (consp x)))
	   (equal (msteps (compile-forms x cenv top) code stack n)
		  stack))
          :hints (("Goal" :use (compile-forms-on-nil msteps-nil))))

(defthm evlist-on-nil
  (implies (and (not (consp x)) (defined (evlist x genv env n)))
	   (null (evlist x genv env n)))
     :hints (("Goal" :in-theory (enable evlist))))

(defthm evlist-on-nil-1
  (implies (and (not (consp x)) (defined (evlist x genv env n)))
	   (equal (append (rev (evlist x genv env n)) stack) stack))
     :hints (("Goal" :use evlist-on-nil)))

(defthm machine-on-nil-evlist
  (implies (and (not (consp x))
		(not (defined (evlist x genv env n))))
	   (not (defined (msteps (compile-forms x cenv top) code stack n))))
     :hints (("Goal" :use evlist-on-non-conses-2)))


;;===========================================================================
;; The compiler correctness for forms and form lists. Note that "cc-theorem"
;; and "forms-theorem" are macros defined in "proof1.lisp" and above,
;; respectively. These macros define the concrete correctness conjecture.
;;===========================================================================

(defthm compiler-correctness-form-forms

  (if flag

      (cc-theorem x cenv env top dcls stack n)

    (forms-theorem x cenv env top dcls stack n))

  :hints (("Goal"
	   :induct (compiler-induction flag x cenv env top dcls stack n)
	   :in-theory
	   (disable evlist evl defined get-stack-frame bind
		    compile-form compile-forms construct-genv download
		    wellformed-form wellformed-forms mstep msteps
		    operatorp get-body get-vars wellformed-form-eqn
		    wellformed-forms-eqn base-form function-callp operator-callp
		    natp compile-def compile-defs mstep-eqn msteps-eqn
		    formp form-listp definitionp definition-listp
		    instructionp instruction-listp codep evlop opr)))
  :rule-classes nil)


(defthm compiler-correctness-for-forms

  (cc-theorem x cenv env top dcls stack n)

  :hints (("Goal" :by (:instance compiler-correctness-form-forms (flag t)))))


;;===========================================================================
;; The compiler correctness for programs
;;===========================================================================


(defthm butlst-and-append-1
  (implies (true-listp cdcls)
	   (equal (butlst (append cdcls (list cf))) cdcls)))

(defthm butlst-and-append-2
  (equal (car (last (append cdcls (list cf)))) cf))

(defthm compile-defs-true-lists
  (implies (true-listp dcls) (true-listp (compile-defs dcls))))

(defthm definition-lists-are-true-lists
  (implies (definition-listp dcls)
	   (true-listp dcls))
     :hints (("Goal" :in-theory (disable definitionp))))

(defthm wf-defs-are-true-lists
  (implies (wellformed-defs dcls (construct-genv dcls))
	   (true-listp dcls))
     :hints (("Goal" :use definition-lists-are-true-lists)))

(defthm wf-progs-wf-defs-wf-main
  (implies (wellformed-program dcls vars main)
	   (and (wellformed-defs dcls (construct-genv dcls))
		(wellformed-form main (construct-genv dcls) vars))))

(defthm execute-lemma
  (implies
   (and (wellformed-program dcls vars main)
	(defined
	  (execute (compile-program dcls vars main)
		   (append (rev inputs) stack) n))
	(true-listp inputs) (equal (len vars) (len inputs)))
   (equal (execute (compile-program dcls vars main)
		   (append (rev inputs) stack) n)
	  (cons (car (evl main (construct-genv dcls)
			  (bind vars
				inputs
				env)
			  n))
		stack)))
  :hints (("Goal"
	   :in-theory
	   (disable msteps download compile-defs
		    compiler-correctness-for-forms
		    get-stack-frame evl bind natp
		    construct-genv
		    msteps-eqn wellformed-program)
	   :use (:instance compiler-correctness-for-forms
			    (x main)
			    (cenv vars)
			    (top 0)
			    (stack (append (rev inputs) stack))))))

(defthm execute-lemma-nil
  (implies
   (and (wellformed-program dcls vars main)
	(defined
	  (execute (compile-program dcls vars main)
		   (append (rev inputs) stack) n))
	(true-listp inputs) (equal (len vars) (len inputs)))
   (equal (execute (compile-program dcls vars main)
		   (append (rev inputs) stack) n)
	  (cons (car (evl main (construct-genv dcls)
			  (bind vars
				inputs
				nil)
			  n))
		stack)))
  :hints (("Goal" :by (:instance execute-lemma (env nil)))))

(defthm evaluate-is-evl-main
  (equal (evaluate dcls vars main inputs n)
	 (evl main (construct-genv dcls) (bind vars inputs nil) n)))

;;---------------------------------------------------------------------------
;; If we execute a compiled well-formed program on the machine with the
;; correct number of input values on top of the stack in reverse order, then,
;; if this execution succeeds, it will return the semantics of the program on
;; top of stack after popping the inputs.
;;---------------------------------------------------------------------------

(defthm compiler-correctness-for-programs
  (implies
   (and (wellformed-program dcls vars main)
	(defined (execute (compile-program dcls vars main)
			  (append (rev inputs) stack)
			  n))
	(true-listp inputs)
	(equal (len vars) (len inputs)))
   (equal (execute (compile-program dcls vars main)
		   (append (rev inputs) stack) n)
	  (cons (car (evaluate dcls vars main inputs n)) stack)))
  :hints
  (("Goal"
    :use (execute-lemma-nil evaluate-is-evl-main)
    :in-theory
    (disable compiler-correctness-for-forms get-stack-frame evl bind
	     natp construct-genv msteps-eqn wellformed-program))))

