;;===========================================================================
;; Copyright (C) 1999 Institut fuer Informatik, University of Kiel, Germany
;;===========================================================================
;; File:         compiler.lisp
;; Author:       Wolfgang Goerigk
;; Content:      ACL2 implementation of a simple mini-ComLisp compiler
;; as of:        14/04/99, University of Texas at Austin, Texas, U.S.A.
;;---------------------------------------------------------------------------
;; $Revision: 1.5 $
;; $Id: compiler.lisp,v 1.5 1999/10/02 20:05:13 wg Exp wg $
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
;; "Using the ACL2 Theorem Prover: A Tutorial Introduction and Case Studies"
;; edited by Matt Kaufmann, Pete Manolios and J Strother Moore.
;;
;;===========================================================================
;;
;; Compiling applicative mini-ComLisp (SL) to abstract machine code (TL)
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;; This book contains the compiler from applicative mini-ComLisp (SL) to the
;; abstract machine code (TL) defined in the book "machine".
;;
;; The compiler consists of six functions (see below). We will show that it is
;; able to compile itself, and that there exists (that we can construct) an
;; incorrect version of the compiler target code (with an intruded Trojan
;; Horse). This "incorrect" compiler target program generates "bad" code for
;; one particular program, and reproduces its own code whenever applied to the
;; "correct" compiler source code, i.e. it passes the so called "compiler
;; bootstrap test". So this is very much in the sense of Ken Thompson's
;; "Reflections on Trusting Trust", his Turing Award Lecture given in
;; 1984. This book also contains the proofs mentioned in the article.
;;
;;===========================================================================

(in-package "ACL2")
(include-book "machine")

;;===========================================================================
;;
;; Programs:
;; ~~~~~~~~~
;;   prog == ((decl_1 decl_n) (x_1 ... x_k) form)
;;   decl == (DEFUN f (x_1 ... x_n) form)
;;   form == x | c | (op form_1 ... form_n) | (f form_1 ... form_n)
;;           (IF form_1 form_2 form_3)
;;
;; where constants (c) are as Lisp constants, i.e. NIL, T, numbers, strings,
;; and quoted s-expressions including symbols. Function (f) and variable (v)
;; names are symbols, and in any case above n or k are greater or equal to
;; 0. Operators (o) are those recognized by operatorp (see below). Programs
;; declare input variables (x_1 ... x_k) which are used in the top level form,
;; but not as global variables within function bodies.
;;
;; Actually, the compiler has a slightly different interface: instead of a
;; program (prog, above) it takes three arguments: the list of declarations
;; (decls), the list of global variables (vars) and the top level form
;; (main). See below.
;;
;;===========================================================================
;; The Compiler
;;===========================================================================
;;
;; The compiler generates machine code for an abstract machine defined in
;; "machine.lisp". The generated machine program assumes an initial stack
;; which contains at least as many items as global variables have to be bound
;; (in reverse order).
;;
;;---------------------------------------------------------------------------

;;===========================================================================
;; Syntactical programs
;;===========================================================================
;;
;; The following set of recognizers define the syntax of (the data type for)
;; programs, function definitions and forms. This is to be able to define and
;; to verify guards for the compiler functions.
;;
;;===========================================================================

(mutual-recursion
(defun formp (form)
  (declare (xargs :guard t))
  (or (atom form)
      (and (equal (car form) 'QUOTE) (consp (cdr form)))
      (and (equal (car form) 'IF)
	   (consp (cdr form)) (formp (cadr form))
	   (consp (cddr form)) (formp (caddr form))
	   (consp (cdddr form)) (formp (cadddr form)))
      (and (symbolp (car form)) (form-listp (cdr form)))))

(defun form-listp (forms)
  (declare (xargs :guard t))
  (if (consp forms)
      (and (formp (car forms)) (form-listp (cdr forms)))
    (null forms)))
)

(defun definitionp (def)
  (declare (xargs :guard t))
  (and (consp def) (equal (car def) 'defun)
       (consp (cdr def)) (symbolp (cadr def))
       (consp (cddr def)) (symbol-listp (caddr def))
       (consp (cdddr def)) (formp (cadddr def))
       (null (cdr (cdddr def)))))

(defun definition-listp (defs)
  (declare (xargs :guard t))
  (if (consp defs)
      (and (definitionp (car defs))
	   (definition-listp (cdr defs)))
    (null defs)))


;;---------------------------------------------------------------------------
;; We need versions of "list" with a fixed number of arguments
;;

(defun list1 (x) (declare (xargs :guard t)) (cons x nil))
(defun list2 (x y) (declare (xargs :guard t)) (list x y))


;;===========================================================================
;; The Compiler
;; ~~~~~~~~~~~~
;;
;; The following six functions define the ACL2 implementation of the
;; compiler. In order to make this file a certified book, we added guard
;; declarations and some stuff for guard verification.
;;
;; You'll find the compiler as a raw SL-program (actually as the list of its
;; six function definitions with the guards stuff deleted) in the definition
;; of the function "compiler-source" below.
;;
;;---------------------------------------------------------------------------

(defun operatorp (name)
  (declare (xargs :guard (symbolp name)))
  (member name
	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

(mutual-recursion
(defun compile-forms (forms env top)
  (declare (xargs :guard (and (form-listp forms) (symbol-listp env) (natp top))
		  :verify-guards nil))
  (if (consp forms)
      (append (compile-form (car forms) env top)
	      (compile-forms (cdr forms) env (1+ top)))
    nil))

(defun compile-form (form env top)
  (declare (xargs :guard (and (formp form) (symbol-listp env) (natp top))
		  :verify-guards nil))
  (if (equal form 'nil) (list1 '(PUSHC NIL))
  (if (equal form 't) (list1 '(PUSHC T))
  (if (symbolp form)
      (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
  (if (atom form)
      (list1 (list2 'PUSHC form))
  (if (equal (car form) 'QUOTE)
      (list1 (list2 'PUSHC (cadr form)))
  (if (equal (car form) 'IF)
      (append (compile-form (cadr form) env top)
	      (list1 (cons 'IF
			   (list2 (compile-form (caddr form) env top)
				  (compile-form (cadddr form) env top)))))
  (if (operatorp (car form))
      (append (compile-forms (cdr form) env top)
	      (list1 (list2 'OPR (car form))))
      (append (compile-forms (cdr form) env top)
	      (list1 (list2 'CALL (car form))))))))))))
)

;;
;; Guard verification. We use a particular (structural) induction scheme in
;; order to prove that both functions return true lists (for append to be
;; well-defined in Common Lisp). Thus, we had to postpone guard verification
;; for these two functions until we proved the theorems "true-listp-form" and
;; "true-listp-forms" below. Maybe the use of structural induction for guard
;; verification in this case is kind of an overkill, but at least it works.
;;

(defun true-listp-form-induction (flag x env top)
  (if (atom x)
      (list x env top)
    (if flag
	(list (true-listp-form-induction t (cadr x) env top)
	      (true-listp-form-induction t (caddr x) env top)
	      (true-listp-form-induction t (cadddr x) env top)
	      (true-listp-form-induction nil (cdr x) env top))
      (list (true-listp-form-induction t (car x) env top)
	    (true-listp-form-induction nil (cdr x) env (1+ top))))))

(defthm list-append
  (implies (and (true-listp x) (true-listp y))
	   (true-listp (append x y))))

(defthm true-listp-form-forms
  (if flag (true-listp (compile-form x env top))
    (true-listp (compile-forms x env top)))
  :hints (("Goal" :induct (true-listp-form-induction flag x env top)))
  :rule-classes nil)

(defthm true-listp-form
  (true-listp (compile-form form env top))
  :hints (("Goal" :by (:instance true-listp-form-forms (flag t)))))

(defthm true-listp-forms
  (true-listp (compile-forms forms env top))
  :hints (("Goal" :by (:instance true-listp-form-forms (flag nil)))))

(verify-guards compile-form)


;;
;; Compiling Definitions
;;----------------------
(defun compile-def (def)
  (declare (xargs :guard (definitionp def)))
  (list1
   (cons 'defcode
	 (list2 (cadr def)
		(append
		 (compile-form (cadddr def) (caddr def) 0)
		 (list1 (list2 'POP (len (caddr def)))))))))

(defun compile-defs (defs)
  (declare (xargs :guard (definition-listp defs)))
  (if (consp defs)
      (append (compile-def (car defs))
	      (compile-defs (cdr defs)))
    nil))

;; Compiling Programs
;;-------------------
(defun compile-program (defs vars main)
  (declare (xargs :guard (and (definition-listp defs)
			      (symbol-listp vars)
			      (formp main))))
  (append (compile-defs defs)
	  (list1 (append (compile-form main vars 0)
			 (list1 (list2 'POP (len vars)))))))


;;---------------------------------------------------------------------------
;; Now we can start with some sample program executions. We run the compiled
;; code for even-odd and the factorial function on the machine. (even 10) is
;; T, (even 11) is NIL, and (fac 6) is 720. Note that the machine returns the
;; stack with those results on top. "compile-program" is called with three
;; arguments, the list of function definitions, the list of input variables,
;; and the main program expression. Then, the machine ("execute") is called
;; again with three arguments, which are the result of "compile-program", the
;; initial stack, and a number of computation steps large enough not to run
;; out of resources.
;;---------------------------------------------------------------------------

(defthm compile-even-10
  (equal (execute
	  (compile-program
	   '((defun even (n) (if (equal n 0) t (odd (1- n))))
	     (defun odd (n) (if (equal n 0) nil (even (1- n)))))
	   '(n)
	   '(even n))
	  '(10)
	  1000000)
	 '(T))
  :rule-classes nil)

(defthm compile-even-11
  (equal (execute
	  (compile-program
	   '((defun even (n) (if (equal n 0) t (odd (1- n))))
	     (defun odd (n) (if (equal n 0) nil (even (1- n)))))
	   '(n)
	   '(even n))
	  '(11)
	  1000000)
	 '(NIL))
  :rule-classes nil)

(defthm compile-fac-6
  (equal (execute
	  (compile-program
	   '((defun fac (n) (if (equal n 0) 1 (* n (fac (1- n))))))
	   '(n)
	   '(fac n))
	  '(6)
	  1000000)
	 '(720))
  :rule-classes nil)

;;---------------------------------------------------------------------------
;; This following function is a constant that returns the compiler source code
;; as a data structure. We copied the above list of six function definitions
;; that belong to the compiler into a constant list which this function
;; returns.
;;---------------------------------------------------------------------------
(defun compiler-source ()
  (declare (xargs :guard t))
 '((defun operatorp (name)
     (member name
   	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
   	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
   	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

   (defun compile-forms (forms env top)
     (if (consp forms)
         (append (compile-form (car forms) env top)
   	      (compile-forms (cdr forms) env (1+ top)))
       nil))


   (defun compile-form (form env top)
     (if (equal form 'nil) (list1 '(PUSHC NIL))
     (if (equal form 't) (list1 '(PUSHC T))
     (if (symbolp form)
         (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
     (if (atom form)
         (list1 (list2 'PUSHC form))
     (if (equal (car form) 'QUOTE)
         (list1 (list2 'PUSHC (cadr form)))
     (if (equal (car form) 'IF)
         (append (compile-form (cadr form) env top)
   	      (list1 (cons 'IF
   			   (list2 (compile-form (caddr form) env top)
   				  (compile-form (cadddr form) env top)))))
     (if (operatorp (car form))
         (append (compile-forms (cdr form) env top)
   	      (list1 (list2 'OPR (car form))))
         (append (compile-forms (cdr form) env top)
   	      (list1 (list2 'CALL (car form))))))))))))

   ;; Compiling Definitions
   ;;----------------------
   (defun compile-def (def)
     (list1
      (cons 'defcode
   	 (list2 (cadr def)
   		(append
   		 (compile-form (cadddr def) (caddr def) 0)
   		 (list1 (list2 'POP (len (caddr def)))))))))

   (defun compile-defs (defs)
     (if (consp defs)
         (append (compile-def (car defs))
   	      (compile-defs (cdr defs)))
       nil))

   ;; Compiling Programs
   ;;-------------------
   (defun compile-program (defs vars main)
     (append (compile-defs defs)
   	  (list1 (append (compile-form main vars 0)
   			 (list1 (list2 'POP (len vars)))))))
   ))

;;---------------------------------------------------------------------------
;;
;; Now we come to the more interesting parts of this script. The following
;; theorem, which is proved by simple evaluation, reads as follows: If we
;; compile the factorial program, we will get the code
;;
;;    ((DEFCODE FAC
;;       ((PUSHV 0)
;;        (PUSHC 0)
;;        (OPR EQUAL)
;;        (IF ((PUSHC 1))
;;  	  ((PUSHV 0)
;;  	   (PUSHV 1)
;;  	   (OPR 1-)
;;  	   (CALL FAC)
;;  	   (OPR *)))
;;        (POP 1)))
;;     ((PUSHV 0) (CALL FAC) (POP 1))))
;;
;; (The main program code pushes the input, calls FAC, and returns the
;; result. The code of FAC first pushes the argument, then the constant 0, and
;; calls EQUAL. If the argument was 0, the code pushes 1 ((fac 0) = 1) and
;; returns. Otherwise, it pushes the argument, pushes it again, calls 1-, then
;; FAC, and finally *. This code corresponds to the reverse polish notation of
;; (* n (fac (1- n))), i.e. (n n 1- fac *). Note that the relative address of
;; "n" changes with the number of used auxiliary stack cells.)
;;
;; But we did not just get this result by using the compiler function on the
;; factorial program. We did first compile the compiler program to machine
;; code, which is done by calling the compiler on the result of
;; "compiler-source", with "(defs vars main)" as input variables and the main
;; expression "(compile-program defs vars main)". Then we execute the
;; resulting machine code on the machine, compiling the factorial
;; program. "execute" is called with the compiled compiler and an initial
;; stack that contains the factorial program (actually the definition(s)), the
;; input variables and the main expression of the factorial program in reverse
;; order (note that the "stack list" grows to the left).
;;
;; Thus, in the theorem below, the machine executes the compiler target code
;; and returns the compiled factorial program. The proof is by evaluation,
;; i.e. ACL2 just uses the :executable-counterparts of COMPILER-SOURCE,
;; COMPILE-PROGRAM, EXECUTE, CAR and EQUAL.
;;
;;---------------------------------------------------------------------------

(defthm machine-compiles-fac
  (equal (car
	  (execute
	   (compile-program (compiler-source)
			    '(defs vars main)
			    '(compile-program defs vars main))
	   '((fac n)
	     (n)
	     ((defun fac (n) (if (equal n 0) 1 (* n (fac (1- n)))))))
	   1000000))
	 '((DEFCODE FAC
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
	   ((PUSHV 0) (CALL FAC) (POP 1))))
  :rule-classes nil)


;;---------------------------------------------------------------------------
;;
;; Let us now compute the result of the compiler bootstrap test. Actually, we
;; follow the description of the general procedure from the paper and go one
;; step too far (see the note below). But anyway. First we apply the compiler
;; once to get an initial machine program m_0 = (compiler-target). Now we can
;; execute m_0 on the machine, apply it to the source code and obtain
;;
;;   m_1 = (car
;;          (execute
;;           (compiler-target)
;;           (list '(compile-program defs vars main)
;;         	'(defs vars main)
;;         	(compiler-source))
;;           1000000))
;;
;; Then we can execute m_1 on the machine, apply it to the source code again
;; and obtain
;;
;;   m_2 = (car
;;          (execute
;;           m_1
;;           (list '(compile-program defs vars main)
;;         	'(defs vars main)
;;         	(compiler-source))
;;           1000000))
;;
;; If everything works correctly, m_1 should be equal to m_2.
;;
;; Note: We have a special situation here. In general, we would use a
;; different existing (maybe optimizing) compiler in order to generate the
;; initial executable m_0. And the unknown optimizing compiler probably does
;; not generate the same code as ours.
;;
;; Since we directly execute the compiler source program within ACL2 for this
;; initial step in our case, m_0 is actually already equal to m_1, and of
;; course executing m_1 returns nothing different from executing m_0. So the
;; theorem "bootstrap-test" below goes one step too far in our special case,
;; and we can prove a short version as well (m_0 = m_1).
;;
;;---------------------------------------------------------------------------

(defun compiler-target ()
  (declare (xargs :guard t))
  (compile-program (compiler-source)
		   '(defs vars main)
		   '(compile-program defs vars main)))

(defthm bootstrap-test
  (let ((m_1 (car
	      (execute
	       (compiler-target)
	       (list '(compile-program defs vars main)
		     '(defs vars main)
		     (compiler-source))
	       1000000))))
    (let ((m_2 (car
		(execute
		 m_1
		 (list '(compile-program defs vars main)
		       '(defs vars main)
		       (compiler-source))
		 1000000))))
      (equal m_1 m_2)))
  :rule-classes nil)


(defthm bootstrap-test-short-version
  (let ((m_1 (car
	      (execute
	       (compiler-target)
	       (list '(compile-program defs vars main)
		     '(defs vars main)
		     (compiler-source))
	       1000000))))
    (equal (compiler-target) m_1))
  :rule-classes nil)


;;===========================================================================
;;
;; Now we define the incorrect compiler. Actually, we are interested in its
;; target code.  But we will produce it by compilation. Thus, we express the
;; Trojan Horse in source code, using conditionally self-reproducing
;; programs. For the effect that we want to show here this is not
;; essential. But it is interesting to see that we are able to express the
;; virus even in our simple source language, and maybe it is even easier to
;; understand it this way.
;;
;; Let us recall the goal: Starting from the original compiler we want to
;; construct an incorrect implementation which works in nearly every case like
;; the original correct compiler, but with two important exceptions, which we
;; call "reproduction" and "catastrophe". The Trojan Horse actually is the
;; code used to generate a wrong implementation for a particular program
;; (called "login"), which might eventually cause a real catastrophe. However,
;; in order to completely hide this code in the (machine) implementation, we
;; need also the reproduction case. We do not want to see the virus in the
;; source code. We want the wrong implementation reproduce itself when applied
;; to the correct source code (that it passes the so called "bootstrap test"),
;; that is, we want a compiler implementation that probably will pass every
;; known compiler test and in particular any source level scrutiny (including
;; verification, see "proof1" and "proof" for the source level verification of
;; our compiler). We want
;;
;;  (a) If applied to the original source code, it reproduces itself
;;      (reproduction),
;;
;;  (b) If applied to the "login" program, it generates incorrect target
;;      code (catastrophe),
;;
;;  (c) and in any other case it generates the expected correct target
;;      code (normal)
;;
;; We construct the wrong compiler source exactly the way the paper describes,
;; which is quite straight-forward. In order to read the function definition
;; of "incorrect-compiler-source" below, you should best use a text editor
;; which can find matching parentheses, because the function contains a lot of
;; large constant copies of program text.
;;
;; Let us start to explain what we did, or even better, let us just do it
;; again: The function "incorrect-compiler-source" below is to return the list
;; of function definitions for the wrong compiler.
;;
;; We start with the correct compiler, that is the following function is just
;; a renamed version of the function "compiler-source" which you can find
;; above in this script. For now, the only interesting function is
;; "compile-program". The other functions will not be changed at all.
;;
;;  (defun incorrect-compiler-source ()
;;    '(
;;
;;      ...
;;
;;      (defun compile-program (defs vars main)
;;        (append (compile-defs defs)
;;  	      (list1 (append (compile-form main vars 0)
;;  			     (list1 (list2 'POP (len vars)))))))
;;
;;      ))
;;
;; We modify "compile-program". Instead of compiling every program correctly,
;; we want to identify two particular programs, that is the correct compiler
;; (the reproduction case) and the correct login-program (the catastrophic
;; case). In the other (normal) case we compile correctly.
;;
;; (a) In the reproduction case we compile the wrong compiler source, using
;;     the technique of constructing self-reproducing code.  But note that the
;;     code below is not yet complete. In the final step, we will replace the
;;     two occurrences of 2000 by the entire list of function definitions.
;;
;; (b) In the catastrophe case we just compile the incorrect login program, and
;;
;; (c) in any other (normal) case we compile as we did before.
;;
;;
;;  (defun incorrect-compiler-source ()
;;   '(
;;
;;     ...
;;
;;     (defun compile-program (defs vars main)
;;      ;; reproduction
;;      ;;-------------
;;      (if (equal defs (compiler-source))
;; 	 (append (compile-defs
;;                 (subst
;;                   '2000
;;                   (+ 1999 1)
;;                   '2000))
;; 		 (list1 (append (compile-form main vars 0)
;; 				(list1 (list2 'POP (len vars))))))
;;      ;; catastrophe
;;      ;;------------
;;      (if (equal defs (login-source))
;; 	 (append (compile-defs
;; 		    '((defun login () '(This is the INCORRECT login))))
;; 		 (list1 (append (compile-form main vars 0)
;; 				  (list1 (list2 'POP (len vars))))))
;;      ;; normal
;;      ;;-------
;;      (append (compile-defs defs)
;; 	     (list1 (append (compile-form main vars 0)
;; 			    (list1 (list2 'POP (len vars)))))))))
;;      ))
;;
;; Now we have to add three functions ("compiler-source", "login-source", and
;; "subst") which we used but did not define yet. The first two are constants
;; which return the function definitions of the corresponding programs. The
;; function "compile-program" is again just a copy of the equally-named
;; function that we used already earlier in this script. Moreover, we did not
;; define the function "subst" to be a built-in function in our language, just
;; to avoid any suspicious facts. So we need to define this function here as
;; well. But that's it. As the result we get the following "pre-program",
;; which is to be completed by two final copy-and-paste steps.
;;
;;
;; (defun incorrect-compiler-source ()
;;   '(
;;
;;     ...
;;
;;     (defun compiler-source () ... )
;;
;;     (defun login-source ()
;;      '((defun login () '(This is the CORRECT login))))
;;
;;     (defun subst (new old tree)
;;      (if (equal old tree) new
;;        (if (atom tree) tree
;; 	 (cons (subst new old (car tree))
;; 	       (subst new old (cdr tree))))))
;;
;;     (defun compile-program (defs vars main)
;;      ;; reproduction
;;      ;;-------------
;;      (if (equal defs (compiler-source))
;; 	 (append (compile-defs
;;                 (subst
;;                   '2000
;;                   (+ 1999 1)
;;                   '2000))
;; 		 (list1 (append (compile-form main vars 0)
;; 				(list1 (list2 'POP (len vars))))))
;;      ;; catastrophe
;;      ;;------------
;;      (if (equal defs (login-source)) ...
;;      ;; normal
;;      ;;-------
;;       ( ... ))))
;;      ))
;;
;; The final step is copy-and-paste. The two occurrences of 2000 in the form
;; "(subst '2000 (+ 1999 1) '2000)" in the reproduction case of
;; "compile-program" have to be replaced by the entire list of function
;; definitions constructed so far. This will make the program text large and
;; messy. So, if you ever change something in such a program, here is an
;; advice: first undo the final copy and paste, then change your program as
;; you like, and finally redo the copy-and-paste step. Otherwise you probably
;; will get lost. Anyway. The complete function looks as follows, and you'll
;; find the ACL2 definition below.
;;
;; (defun incorrect-compiler-source ()
;;   '(
;;
;;     ...
;;
;;     (defun compiler-source () ... )
;;
;;     (defun login-source () ... )
;;
;;     (defun subst (new old tree) ... )
;;
;;     (defun compile-program (defs vars main)
;;      ;; reproduction
;;      ;;-------------
;;      (if (equal defs (compiler-source))
;; 	 (append (compile-defs
;;                 (subst
;;                   '((defun compiler-source () ... ) ... )
;;                   (+ 1999 1)
;;                   '((defun compiler-source () ... ) ... )))
;; 		 (list1 (append (compile-form main vars 0)
;; 				(list1 (list2 'POP (len vars))))))
;;      ;; catastrophe
;;      ;;------------
;;      (if (equal defs (login-source)) ...
;; 	 ( ... )
;;      ;; normal
;;      ;;-------
;;       ( ... ))))
;;      ))
;;
;; This finishes the construction of the source code for the incorrect compiler
;; program. We now define this function, and after that, we will compile it to
;; machine code using the (correct) compiler. Then, we can execute the
;; incorrect compiler target program on the machine. We will prove, that this
;; machine program reproduces itself if applied to the correct compiler, and
;; that it generates incorrect code for the login program.
;;
;; Note: "compile-program" is the only function that we
;; changed. "compiler-source" (which we defined already earlier) and
;; "login-source" are just constants, and if we would make "subst" part of the
;; language (as it is in ACL2) we would not need to define it here as well.
;;


(defun incorrect-compiler-source ()
  (declare (xargs :guard t))
  '((defun operatorp (name)
     (member name
   	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
   	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
   	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

    (defun compile-forms (forms env top)
      (if (consp forms)
	  (append (compile-form (car forms) env top)
		  (compile-forms (cdr forms) env (1+ top)))
	nil))

    (defun compile-form (form env top)
      (if (equal form 'nil) (list1 '(PUSHC NIL))
      (if (equal form 't) (list1 '(PUSHC T))
      (if (symbolp form)
          (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
      (if (atom form)
          (list1 (list2 'PUSHC form))
      (if (equal (car form) 'QUOTE)
          (list1 (list2 'PUSHC (cadr form)))
      (if (equal (car form) 'IF)
          (append (compile-form (cadr form) env top)
    	      (list1 (cons 'IF
    			   (list2 (compile-form (caddr form) env top)
    				  (compile-form (cadddr form) env top)))))
      (if (operatorp (car form))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'OPR (car form))))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'CALL (car form))))))))))))

    (defun compile-def (def)
      (list1
       (cons 'defcode
	     (list2 (cadr def)
		    (append
		     (compile-form (cadddr def) (caddr def) 0)
		     (list1 (list2 'POP (len (caddr def)))))))))

    (defun compile-defs (defs)
      (if (consp defs)
	  (append (compile-def (car defs))
		  (compile-defs (cdr defs)))
	nil))

    (defun login-source ()
      '((defun login () '(This is the CORRECT login))))

    (defun compiler-source ()
     '((defun operatorp (name)
         (member name
       	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
       	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
       	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

       (defun compile-forms (forms env top)
         (if (consp forms)
             (append (compile-form (car forms) env top)
       	      (compile-forms (cdr forms) env (1+ top)))
           nil))


       (defun compile-form (form env top)
         (if (equal form 'nil) (list1 '(PUSHC NIL))
         (if (equal form 't) (list1 '(PUSHC T))
         (if (symbolp form)
             (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
         (if (atom form)
             (list1 (list2 'PUSHC form))
         (if (equal (car form) 'QUOTE)
             (list1 (list2 'PUSHC (cadr form)))
         (if (equal (car form) 'IF)
             (append (compile-form (cadr form) env top)
       	      (list1 (cons 'IF
       			   (list2 (compile-form (caddr form) env top)
       				  (compile-form (cadddr form) env top)))))
         (if (operatorp (car form))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'OPR (car form))))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'CALL (car form))))))))))))

       (defun compile-def (def)
         (list1
          (cons 'defcode
       	 (list2 (cadr def)
       		(append
       		 (compile-form (cadddr def) (caddr def) 0)
       		 (list1 (list2 'POP (len (caddr def)))))))))

       (defun compile-defs (defs)
         (if (consp defs)
             (append (compile-def (car defs))
       	      (compile-defs (cdr defs)))
           nil))

       (defun compile-program (defs vars main)
         (append (compile-defs defs)
       	  (list1 (append (compile-form main vars 0)
       			 (list1 (list2 'POP (len vars)))))))
       ))

    (defun subst (new old tree)
      (if (equal old tree) new
	(if (atom tree) tree
	  (cons (subst new old (car tree))
		(subst new old (cdr tree))))))

    (defun compile-program (defs vars main)
      ;; reproduction
      ;;-------------
      (if (equal defs (compiler-source))
	  (append (compile-defs
		   (subst
		    '((defun operatorp (name)
     (member name
   	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
   	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
   	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

    (defun compile-forms (forms env top)
      (if (consp forms)
	  (append (compile-form (car forms) env top)
		  (compile-forms (cdr forms) env (1+ top)))
	nil))

    (defun compile-form (form env top)
      (if (equal form 'nil) (list1 '(PUSHC NIL))
      (if (equal form 't) (list1 '(PUSHC T))
      (if (symbolp form)
          (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
      (if (atom form)
          (list1 (list2 'PUSHC form))
      (if (equal (car form) 'QUOTE)
          (list1 (list2 'PUSHC (cadr form)))
      (if (equal (car form) 'IF)
          (append (compile-form (cadr form) env top)
    	      (list1 (cons 'IF
    			   (list2 (compile-form (caddr form) env top)
    				  (compile-form (cadddr form) env top)))))
      (if (operatorp (car form))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'OPR (car form))))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'CALL (car form))))))))))))

    (defun compile-def (def)
      (list1
       (cons 'defcode
	     (list2 (cadr def)
		    (append
		     (compile-form (cadddr def) (caddr def) 0)
		     (list1 (list2 'POP (len (caddr def)))))))))

    (defun compile-defs (defs)
      (if (consp defs)
	  (append (compile-def (car defs))
		  (compile-defs (cdr defs)))
	nil))

    (defun login-source ()
      '((defun login () '(This is the CORRECT login))))

    (defun compiler-source ()
     '((defun operatorp (name)
         (member name
       	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
       	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
       	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

       (defun compile-forms (forms env top)
         (if (consp forms)
             (append (compile-form (car forms) env top)
       	      (compile-forms (cdr forms) env (1+ top)))
           nil))


       (defun compile-form (form env top)
         (if (equal form 'nil) (list1 '(PUSHC NIL))
         (if (equal form 't) (list1 '(PUSHC T))
         (if (symbolp form)
             (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
         (if (atom form)
             (list1 (list2 'PUSHC form))
         (if (equal (car form) 'QUOTE)
             (list1 (list2 'PUSHC (cadr form)))
         (if (equal (car form) 'IF)
             (append (compile-form (cadr form) env top)
       	      (list1 (cons 'IF
       			   (list2 (compile-form (caddr form) env top)
       				  (compile-form (cadddr form) env top)))))
         (if (operatorp (car form))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'OPR (car form))))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'CALL (car form))))))))))))

       (defun compile-def (def)
         (list1
          (cons 'defcode
       	 (list2 (cadr def)
       		(append
       		 (compile-form (cadddr def) (caddr def) 0)
       		 (list1 (list2 'POP (len (caddr def)))))))))

       (defun compile-defs (defs)
         (if (consp defs)
             (append (compile-def (car defs))
       	      (compile-defs (cdr defs)))
           nil))

       (defun compile-program (defs vars main)
         (append (compile-defs defs)
       	  (list1 (append (compile-form main vars 0)
       			 (list1 (list2 'POP (len vars)))))))
       ))

    (defun subst (new old tree)
      (if (equal old tree) new
	(if (atom tree) tree
	  (cons (subst new old (car tree))
		(subst new old (cdr tree))))))

    (defun compile-program (defs vars main)
      ;; reproduction
      ;;-------------
      (if (equal defs (compiler-source))
	  (append (compile-defs
		   (subst
		    '2000
		    (+ 1999 1)
		    '2000))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; catastrophe
      ;;------------
      (if (equal defs (login-source))
	  (append (compile-defs
		   '((defun login () '(This is the INCORRECT login))))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; normal
      ;;-------
      (append (compile-defs defs)
	      (list1 (append (compile-form main vars 0)
			     (list1 (list2 'POP (len vars)))))))))

    )
		    (+ 1999 1)
		    '((defun operatorp (name)
     (member name
   	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
   	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
   	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

    (defun compile-forms (forms env top)
      (if (consp forms)
	  (append (compile-form (car forms) env top)
		  (compile-forms (cdr forms) env (1+ top)))
	nil))

    (defun compile-form (form env top)
      (if (equal form 'nil) (list1 '(PUSHC NIL))
      (if (equal form 't) (list1 '(PUSHC T))
      (if (symbolp form)
          (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
      (if (atom form)
          (list1 (list2 'PUSHC form))
      (if (equal (car form) 'QUOTE)
          (list1 (list2 'PUSHC (cadr form)))
      (if (equal (car form) 'IF)
          (append (compile-form (cadr form) env top)
    	      (list1 (cons 'IF
    			   (list2 (compile-form (caddr form) env top)
    				  (compile-form (cadddr form) env top)))))
      (if (operatorp (car form))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'OPR (car form))))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'CALL (car form))))))))))))

    (defun compile-def (def)
      (list1
       (cons 'defcode
	     (list2 (cadr def)
		    (append
		     (compile-form (cadddr def) (caddr def) 0)
		     (list1 (list2 'POP (len (caddr def)))))))))

    (defun compile-defs (defs)
      (if (consp defs)
	  (append (compile-def (car defs))
		  (compile-defs (cdr defs)))
	nil))

    (defun login-source ()
      '((defun login () '(This is the CORRECT login))))

    (defun compiler-source ()
     '((defun operatorp (name)
         (member name
       	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
       	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
       	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

       (defun compile-forms (forms env top)
         (if (consp forms)
             (append (compile-form (car forms) env top)
       	      (compile-forms (cdr forms) env (1+ top)))
           nil))


       (defun compile-form (form env top)
         (if (equal form 'nil) (list1 '(PUSHC NIL))
         (if (equal form 't) (list1 '(PUSHC T))
         (if (symbolp form)
             (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
         (if (atom form)
             (list1 (list2 'PUSHC form))
         (if (equal (car form) 'QUOTE)
             (list1 (list2 'PUSHC (cadr form)))
         (if (equal (car form) 'IF)
             (append (compile-form (cadr form) env top)
       	      (list1 (cons 'IF
       			   (list2 (compile-form (caddr form) env top)
       				  (compile-form (cadddr form) env top)))))
         (if (operatorp (car form))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'OPR (car form))))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'CALL (car form))))))))))))

       (defun compile-def (def)
         (list1
          (cons 'defcode
       	 (list2 (cadr def)
       		(append
       		 (compile-form (cadddr def) (caddr def) 0)
       		 (list1 (list2 'POP (len (caddr def)))))))))

       (defun compile-defs (defs)
         (if (consp defs)
             (append (compile-def (car defs))
       	      (compile-defs (cdr defs)))
           nil))

       (defun compile-program (defs vars main)
         (append (compile-defs defs)
       	  (list1 (append (compile-form main vars 0)
       			 (list1 (list2 'POP (len vars)))))))
       ))

    (defun subst (new old tree)
      (if (equal old tree) new
	(if (atom tree) tree
	  (cons (subst new old (car tree))
		(subst new old (cdr tree))))))

    (defun compile-program (defs vars main)
      ;; reproduction
      ;;-------------
      (if (equal defs (compiler-source))
	  (append (compile-defs
		   (subst
		    '2000
		    (+ 1999 1)
		    '2000))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; catastrophe
      ;;------------
      (if (equal defs (login-source))
	  (append (compile-defs
		   '((defun login () '(This is the INCORRECT login))))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; normal
      ;;-------
      (append (compile-defs defs)
	      (list1 (append (compile-form main vars 0)
			     (list1 (list2 'POP (len vars)))))))))

    )))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; catastrophe
      ;;------------
      (if (equal defs (login-source))
	  (append (compile-defs
		   '((defun login () '(This is the INCORRECT login))))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; normal
      ;;-------
      (append (compile-defs defs)
	      (list1 (append (compile-form main vars 0)
			     (list1 (list2 'POP (len vars)))))))))

    ))


;;---------------------------------------------------------------------------
;; Now we can generate the desired target machine code for the incorrect
;; compiler by compilation. The function "incorrect-compiler-target" returns
;; the target code for the above source program. The main expression is
;; "(compile-program defs vars main)", and thus the input variables are "(defs
;; vars main)".
;;---------------------------------------------------------------------------

(defun incorrect-compiler-target ()
  (declare (xargs :guard t))
  (compile-program (incorrect-compiler-source)
		   '(defs vars main)
		   '(compile-program defs vars main)))


;;---------------------------------------------------------------------------
;; A first test is to execute the incorrect compiler target program on the
;; machine, apply it to the factorial program and compare the result to what
;; the correct compiler generates. So the incorrect compiler executable works
;; correctly on the factorial program.
;;---------------------------------------------------------------------------

(defthm incorrect-compiler-on-factorial
  (equal
   (car (execute
	 (incorrect-compiler-target)
	 '((fac n)
	   (n)
	   ((defun fac (n)
	      (if (equal n 0) 1 (* n (fac (1- n)))))))
	 1000000))
   (compile-program
    '((defun fac (n)
	(if (equal n 0) 1 (* n (fac (1- n)))))) '(n) '(fac n)))
  :rule-classes nil)


;;---------------------------------------------------------------------------
;; A second test is to execute both compiler programs on the machine and apply
;; them to the factorial program. We see that both compiler executables
;; generate the same correct target code.
;;---------------------------------------------------------------------------

(defthm both-compilers-on-the-machine
  (equal
   (car (execute
	 (incorrect-compiler-target)
	 '((fac n)
	   (n)
	   ((defun fac (n)
	      (if (equal n 0) 1 (* n (fac (1- n)))))))
	 1000000))
   (car (execute
	 (compiler-target)
	 '((fac n)
	   (n)
	   ((defun fac (n)
	      (if (equal n 0) 1 (* n (fac (1- n)))))))
	 1000000)))
  :rule-classes nil)


;;---------------------------------------------------------------------------
;; The Catastrophy Case
;; ~~~~~~~~~~~~~~~~~~~~
;;
;; Now we are going to prove two of our main theorems. Again, ACL2 proves them
;; just by execution. First we prove, that the incorrect compiler target
;; program actually generates the wrong code for the login function. The
;; target code returns the list "(This is the INCORRECT login)" instead of
;; "(This is the CORRECT login)".
;;
;;---------------------------------------------------------------------------

(defthm incorrect-compiler-catastrophy
  (equal
   (car (execute
	 (incorrect-compiler-target)
	 '((login)
	   ()
	   ((defun login () '(This is the CORRECT login))))
	 1000000))
   '((defcode login
       ((pushc (This is the INCORRECT login)) (pop 0)))
     ((call login) (pop 0))))
  :rule-classes nil)



;;---------------------------------------------------------------------------
;; The Reproduction Case
;; ~~~~~~~~~~~~~~~~~~~~~
;;
;; If we apply the incorrect compiler executable to the "verified" compiler
;; source we get the incorrect binary back. This theorem has been our main
;; goal and tells the message of the entire effort.
;;
;;---------------------------------------------------------------------------


(defthm incorrect-compiler-reproduction
  (equal
   (car (execute (incorrect-compiler-target)
		    (list '(compile-program defs vars main)
			  '(defs vars main)
			  (compiler-source))
		    1000000))
   (incorrect-compiler-target))
  :rule-classes nil)

;;
;; We can now play a bit with ACL2 and even prove that we can bootstrap
;; arbitrarily often :-)
;;

(defun boot-n-times (n)
  (declare (xargs :guard (natp n)
		  :verify-guards nil))
  (if (zp n)
      (incorrect-compiler-target)
    (car (execute (boot-n-times (1- n))
		    (list '(compile-program defs vars main)
			  '(defs vars main)
			  (compiler-source))
		    1000000))))

(defthm bootstrap-for-any-n
  (implies (natp n)
	   (equal (boot-n-times n)
		  (incorrect-compiler-target))))

(verify-guards boot-n-times)

;;---------------------------------------------------------------------------
;; The Normal Case
;; ~~~~~~~~~~~~~~~
;;
;; There is one fact that we additionally want to prove, namely that the
;; incorrect compiler actually returns the correct result for any but the two
;; exceptional programs. We prove that theorem for source program and give an
;; informal argument for the machine executable below. A formal proof for the
;; latter would cause a lot of additional theorems to be proved and goes
;; beyond the scope of this script.
;;
;; First we admit the missing two functions "login-source" and
;; "compile-program" from the incorrect compiler source to ACL2. The other
;; functions have been defined already. We just copy the functions from the
;; source code above, but we have to rename "compile-program" because there is
;; the correct "compile-program" function already in use:
;;
;;---------------------------------------------------------------------------

(defun login-source ()
  (declare (xargs :guard t))
  '((defun login () '(This is the CORRECT login))))

(defun incorrectly-compile-program (defs vars main)
  (declare (xargs :guard (and (definition-listp defs)
			      (symbol-listp vars)
			      (formp main))))
      ;; reproduction
      ;;-------------
      (if (equal defs (compiler-source))
	  (append (compile-defs
		   (subst
		    '((defun operatorp (name)
     (member name
   	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
   	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
   	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

    (defun compile-forms (forms env top)
      (if (consp forms)
	  (append (compile-form (car forms) env top)
		  (compile-forms (cdr forms) env (1+ top)))
	nil))

    (defun compile-form (form env top)
      (if (equal form 'nil) (list1 '(PUSHC NIL))
      (if (equal form 't) (list1 '(PUSHC T))
      (if (symbolp form)
          (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
      (if (atom form)
          (list1 (list2 'PUSHC form))
      (if (equal (car form) 'QUOTE)
          (list1 (list2 'PUSHC (cadr form)))
      (if (equal (car form) 'IF)
          (append (compile-form (cadr form) env top)
    	      (list1 (cons 'IF
    			   (list2 (compile-form (caddr form) env top)
    				  (compile-form (cadddr form) env top)))))
      (if (operatorp (car form))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'OPR (car form))))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'CALL (car form))))))))))))

    (defun compile-def (def)
      (list1
       (cons 'defcode
	     (list2 (cadr def)
		    (append
		     (compile-form (cadddr def) (caddr def) 0)
		     (list1 (list2 'POP (len (caddr def)))))))))

    (defun compile-defs (defs)
      (if (consp defs)
	  (append (compile-def (car defs))
		  (compile-defs (cdr defs)))
	nil))

    (defun login-source ()
      '((defun login () '(This is the CORRECT login))))

    (defun compiler-source ()
     '((defun operatorp (name)
         (member name
       	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
       	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
       	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

       (defun compile-forms (forms env top)
         (if (consp forms)
             (append (compile-form (car forms) env top)
       	      (compile-forms (cdr forms) env (1+ top)))
           nil))


       (defun compile-form (form env top)
         (if (equal form 'nil) (list1 '(PUSHC NIL))
         (if (equal form 't) (list1 '(PUSHC T))
         (if (symbolp form)
             (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
         (if (atom form)
             (list1 (list2 'PUSHC form))
         (if (equal (car form) 'QUOTE)
             (list1 (list2 'PUSHC (cadr form)))
         (if (equal (car form) 'IF)
             (append (compile-form (cadr form) env top)
       	      (list1 (cons 'IF
       			   (list2 (compile-form (caddr form) env top)
       				  (compile-form (cadddr form) env top)))))
         (if (operatorp (car form))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'OPR (car form))))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'CALL (car form))))))))))))

       (defun compile-def (def)
         (list1
          (cons 'defcode
       	 (list2 (cadr def)
       		(append
       		 (compile-form (cadddr def) (caddr def) 0)
       		 (list1 (list2 'POP (len (caddr def)))))))))

       (defun compile-defs (defs)
         (if (consp defs)
             (append (compile-def (car defs))
       	      (compile-defs (cdr defs)))
           nil))

       (defun compile-program (defs vars main)
         (append (compile-defs defs)
       	  (list1 (append (compile-form main vars 0)
       			 (list1 (list2 'POP (len vars)))))))
       ))

    (defun subst (new old tree)
      (if (equal old tree) new
	(if (atom tree) tree
	  (cons (subst new old (car tree))
		(subst new old (cdr tree))))))

    (defun compile-program (defs vars main)
      ;; reproduction
      ;;-------------
      (if (equal defs (compiler-source))
	  (append (compile-defs
		   (subst
		    '2000
		    (+ 1999 1)
		    '2000))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; catastrophe
      ;;------------
      (if (equal defs (login-source))
	  (append (compile-defs
		   '((defun login () '(This is the INCORRECT login))))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; normal
      ;;-------
      (append (compile-defs defs)
	      (list1 (append (compile-form main vars 0)
			     (list1 (list2 'POP (len vars)))))))))

    )
		    (+ 1999 1)
		    '((defun operatorp (name)
     (member name
   	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
   	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
   	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

    (defun compile-forms (forms env top)
      (if (consp forms)
	  (append (compile-form (car forms) env top)
		  (compile-forms (cdr forms) env (1+ top)))
	nil))

    (defun compile-form (form env top)
      (if (equal form 'nil) (list1 '(PUSHC NIL))
      (if (equal form 't) (list1 '(PUSHC T))
      (if (symbolp form)
          (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
      (if (atom form)
          (list1 (list2 'PUSHC form))
      (if (equal (car form) 'QUOTE)
          (list1 (list2 'PUSHC (cadr form)))
      (if (equal (car form) 'IF)
          (append (compile-form (cadr form) env top)
    	      (list1 (cons 'IF
    			   (list2 (compile-form (caddr form) env top)
    				  (compile-form (cadddr form) env top)))))
      (if (operatorp (car form))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'OPR (car form))))
          (append (compile-forms (cdr form) env top)
    	      (list1 (list2 'CALL (car form))))))))))))

    (defun compile-def (def)
      (list1
       (cons 'defcode
	     (list2 (cadr def)
		    (append
		     (compile-form (cadddr def) (caddr def) 0)
		     (list1 (list2 'POP (len (caddr def)))))))))

    (defun compile-defs (defs)
      (if (consp defs)
	  (append (compile-def (car defs))
		  (compile-defs (cdr defs)))
	nil))

    (defun login-source ()
      '((defun login () '(This is the CORRECT login))))

    (defun compiler-source ()
     '((defun operatorp (name)
         (member name
       	  '(CAR CDR CADR CADDR CADAR CADDAR CADDDR
       	    1- 1+ LEN SYMBOLP CONSP ATOM CONS EQUAL
       	    APPEND MEMBER ASSOC + - * LIST1 LIST2)))

       (defun compile-forms (forms env top)
         (if (consp forms)
             (append (compile-form (car forms) env top)
       	      (compile-forms (cdr forms) env (1+ top)))
           nil))


       (defun compile-form (form env top)
         (if (equal form 'nil) (list1 '(PUSHC NIL))
         (if (equal form 't) (list1 '(PUSHC T))
         (if (symbolp form)
             (list1 (list2 'PUSHV (+ top (1- (len (member form env))))))
         (if (atom form)
             (list1 (list2 'PUSHC form))
         (if (equal (car form) 'QUOTE)
             (list1 (list2 'PUSHC (cadr form)))
         (if (equal (car form) 'IF)
             (append (compile-form (cadr form) env top)
       	      (list1 (cons 'IF
       			   (list2 (compile-form (caddr form) env top)
       				  (compile-form (cadddr form) env top)))))
         (if (operatorp (car form))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'OPR (car form))))
             (append (compile-forms (cdr form) env top)
       	      (list1 (list2 'CALL (car form))))))))))))

       (defun compile-def (def)
         (list1
          (cons 'defcode
       	 (list2 (cadr def)
       		(append
       		 (compile-form (cadddr def) (caddr def) 0)
       		 (list1 (list2 'POP (len (caddr def)))))))))

       (defun compile-defs (defs)
         (if (consp defs)
             (append (compile-def (car defs))
       	      (compile-defs (cdr defs)))
           nil))

       (defun compile-program (defs vars main)
         (append (compile-defs defs)
       	  (list1 (append (compile-form main vars 0)
       			 (list1 (list2 'POP (len vars)))))))
       ))

    (defun subst (new old tree)
      (if (equal old tree) new
	(if (atom tree) tree
	  (cons (subst new old (car tree))
		(subst new old (cdr tree))))))

    (defun compile-program (defs vars main)
      ;; reproduction
      ;;-------------
      (if (equal defs (compiler-source))
	  (append (compile-defs
		   (subst
		    '2000
		    (+ 1999 1)
		    '2000))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; catastrophe
      ;;------------
      (if (equal defs (login-source))
	  (append (compile-defs
		   '((defun login () '(This is the INCORRECT login))))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; normal
      ;;-------
      (append (compile-defs defs)
	      (list1 (append (compile-form main vars 0)
			     (list1 (list2 'POP (len vars)))))))))

    )))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; catastrophe
      ;;------------
      (if (equal defs (login-source))
	  (append (compile-defs
		   '((defun login () '(This is the INCORRECT login))))
		  (list1 (append (compile-form main vars 0)
				 (list1 (list2 'POP (len vars))))))
      ;; normal
      ;;-------
      (append (compile-defs defs)
	      (list1 (append (compile-form main vars 0)
			     (list1 (list2 'POP (len vars)))))))))



;;---------------------------------------------------------------------------
;;
;; The next theorem is to prove that the incorrect compiler source program
;; actually generates correct code for any but the two exceptional
;; arguments. So there are exactly two source programs for which the incorrect
;; compiler generates wrong target code: the correct compiler and the
;; login program.
;;
;;---------------------------------------------------------------------------


(defthm acl2-incorrect-compiler-normal
  (implies
    (not (or (equal defs (login-source))
	     (equal defs (compiler-source))))
   (equal (incorrectly-compile-program defs vars main)
	  (compile-program defs vars main)))
  :rule-classes nil)


;;---------------------------------------------------------------------------
;;
;; We also redo the proofs for the reproduction and catastrophe cases for the
;; incorrect source program.
;;
;;---------------------------------------------------------------------------


(defthm acl2-incorrect-compiler-catastrophy
  (equal
   (incorrectly-compile-program
    '((defun login () '(This is the CORRECT login)))
    '()
    '(login))
   '((defcode login
       ((pushc (This is the INCORRECT login)) (pop 0)))
     ((call login) (pop 0))))
  :rule-classes nil)


(defthm acl2-incorrect-compiler-reproduction
  (equal
   (incorrectly-compile-program
    (compiler-source)
    '(defs vars main)
    '(compile-program defs vars main))
   (incorrect-compiler-target))
  :rule-classes nil)



;;---------------------------------------------------------------------------
;;
;; We do not want to give a formal proof that the incorrect compiler, if
;; executed on the machine, gives the same result as the correct one for any
;; (normal) program. But the idea is as follows:
;;
;; Let us assume an argument program (defs vars main) s.t. defs is neither
;; equal to (compiler-source) nor to (login-source). Let us further assume,
;; that the termination arguments given to execute are large enough so that
;; both machine executions do not run out of space. In that case we find that
;; the two programs basically execute the same code:
;;
;; Both executables have been generated by applying the correct compiler to
;; their definition list and the same list "(defs vars main)" of input
;; variables and the same main expression "(compile-program defs vars
;; main)". Thus, if we look at the generated target code, we will find
;; identical main programs
;;
;;  ((PUSHV 2)
;;   (PUSHV 2)
;;   (PUSHV 2)
;;   (CALL COMPILE-PROGRAM)
;;   (POP 3))
;;
;; and for the functions of the correct compiler (except "compile-program") we
;; observe that the same target code has been generated in both machine
;; programs. Furthermore, the correct "compile-program" function has been
;; compiled to
;;
;;  (DEFCODE COMPILE-PROGRAM
;;           ((PUSHV 2)
;;            (CALL COMPILE-DEFS)
;;            (PUSHV 1)
;;            (PUSHV 3)
;;            (PUSHC 0)
;;            (CALL COMPILE-FORM)
;;            (PUSHC POP)
;;            (PUSHV 4)
;;            (OPR LEN)
;;            (OPR LIST2)
;;            (OPR LIST1)
;;            (OPR APPEND)
;;            (OPR LIST1)
;;            (OPR APPEND)
;;            (POP 3)))
;;
;; and the code for the incorrect "compile-program" is
;;
;;  (DEFCODE
;;    COMPILE-PROGRAM
;;    ((PUSHV 2)
;;     (CALL COMPILER-SOURCE)
;;     (OPR EQUAL)
;;     (IF
;;      ( ... )
;;      ((PUSHV 2)
;;       (CALL LOGIN-SOURCE)
;;       (OPR EQUAL)
;;       (IF ( ... )
;;           ((PUSHV 2)
;;            (CALL COMPILE-DEFS)
;;            (PUSHV 1)
;;            (PUSHV 3)
;;            (PUSHC 0)
;;            (CALL COMPILE-FORM)
;;            (PUSHC POP)
;;            (PUSHV 4)
;;            (OPR LEN)
;;            (OPR LIST2)
;;            (OPR LIST1)
;;            (OPR APPEND)
;;            (OPR LIST1)
;;            (OPR APPEND)))))
;;     (POP 3)))
;;
;; We omitted the large parts which will not be executed. The body of
;; COMPILER-SOURCE pushes the result of (compiler-source), and LOGIN-SOURCE
;; pushes the result of (login-source) both of which are assumed not to be
;; EQUAL to the argument defs, which is the list of definitions to be
;; compiled. Thus, both programs basically execute the same code on the same
;; input stack. Therefore we conclude, that they both will return the same
;; result if they do not run into an ERROR.
;;
;; Of course, we take some obvious facts for granted. So for instance we
;; assume that we may simplify conditionals, and that the machine execution
;; of a piece of code does not depend on bindings for function symbols which
;; are not called. And so forth...
;;
;;===========================================================================
;;


