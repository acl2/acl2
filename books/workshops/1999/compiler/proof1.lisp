;;===========================================================================
;; Copyright (C) 1999 Institut fuer Informatik, University of Kiel, Germany
;;===========================================================================
;; File:         proof1.lisp
;; Author:       Wolfgang Goerigk
;; Content:      ACL2 Austin CP correctness proof
;; as of:        15/09/99, University of Kiel, Germany
;;---------------------------------------------------------------------------
;; $Revision: 1.4 $
;; $Id: proof1.lisp,v 1.4 1999/10/02 11:46:57 wg Exp wg $
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
;; The Compiler Correctness Proof - Part 1
;;
;;===========================================================================
;;
;; This file contains parts of the compiler correctness proof for the
;; miniComLisp (called SL in the paper) compiler defined in "compiler.lisp"
;; with respect to the semantics of miniComLisp as defined in "evaluator.lisp"
;; and the machine semantics as defined in "machine.lisp". In this book we
;; prove the base case of the induction, i.e. we prove (cc-theorem form ...)
;; for program constants and variables. You will also find some additional
;; technical lemmas which we need for the proof (see "proof.lisp").
;;
;;===========================================================================

(in-package "ACL2")
(include-book "evaluator")


;;---------------------------------------------------------------------------
;; For proving correct variable access, we need the fact that variables are
;; bound within well-formed programs. Thus, we prove that in well-formed
;; programs every variable is bound, i.e. member of the environment.
;;---------------------------------------------------------------------------
(defthm variables-are-bound
  (implies (and (symbolp form) form (not (eql form t))
		(wellformed-form form genv env))
	   (member form env)))

;;===========================================================================
;; In the following we prove theorems about the evaluation and execution of
;; operator calls which allow us to disable the large conditionals evlop and
;; opr. So far, these theorems are not used, because we only succeeded in
;; proving the induction base case yet. Perhaps these theorems have to
;; reformulated in order to really help for the proof.
;;---------------------------------------------------------------------------

(defthm cc-operators-unary
  (implies (member op '(CAR CDR CADR CADDR CADAR CADDAR CADDDR 1- 1+
			    LEN SYMBOLP CONSP ATOM LIST1))
	   (equal (opr op code (list* arg stack))
		  (cons (car (evlop op (list arg) genv1 env1 n1)) stack))))

(defthm cc-operators-binary
  (implies (member op '(CONS EQUAL APPEND MEMBER ASSOC + - * LIST2))
	   (equal (opr op code (list* a2 a1 stack))
		  (cons (car (evlop op (list a1 a2) genv1 env1 n1)) stack))))


;;===========================================================================
;; The following definitions and lemmas are w.r.t. correct addressing of
;; variables. The idea of the correctness proof that we try is to relate both,
;; the result of associating a variable in the environment of the evaluator,
;; and the variable access in the stack, to the position of that variable in
;; the compiletime environment. Although there is a (tail recursive)
;; definition of the Lisp function position available, we prefer to define our
;; own my-position recursively for the same reason we already defined mytake
;; instead of using take: the proofs we need just do not work if we use the
;; standard Lisp (ACL2) functions. Note: We use my-position only in the proof,
;; so this definition is harmless. But mytake (replacing take) is used by
;; get-stack-frame and thus for formulating the correctness theorem. We have
;; to be careful to really espress what we want. Anyway.
;;---------------------------------------------------------------------------

(defun my-position (x l)
  (cond ((endp l) nil)
	((eql x (car l)) 0)
	(t (1+ (my-position x (cdr l))))))

(defun address (var cenv top)
  (+ top (1- (len (member var cenv)))))


(defun mytake (n list)
  (if (zp n) nil (cons (car list) (mytake (1- n) (cdr list)))))

(defun get-stack-frame (cenv top stack)
  (mytake (len cenv) (nthcdr top stack)))

(defthm position-right-shift
  (implies (and (not (equal var (car cenv)))
		(member var cenv))
	   (equal (nth (my-position var cenv) vals)
		  (nth (my-position var (cdr cenv)) (cdr vals))))
  :rule-classes nil)

(defthm position-cdr
  (implies (and (not (equal var (car cenv)))
		(member var cenv))
	   (equal (my-position var cenv)
		  (1+ (my-position var (cdr cenv))))))

;;---------------------------------------------------------------------------
;; This theorem relates the variable lookup by association to the position of
;; the variable in the compile time environment. Thus, evaluation of a
;; variable content is actually based on the position of that variable in the
;; environment as well.
;;---------------------------------------------------------------------------
(defthm lookup-position-bridge
  (implies (member var cenv)
	   (equal (cdr (assoc var (bind cenv vals rest)))
		  (nth (my-position var cenv) vals)))
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (just a goal name change).]
  :hints (("Subgoal *1/4"
	   :use ((:instance position-right-shift)))))

;;---------------------------------------------------------------------------
;; This theorem relates the address of a variable computed by the compiler to
;; the position of the variable in the compile time environment. Thus,
;; variable access in the stack is actually based on the position of that
;; variable in the compiletime environment (i.e. the formal parameter list).
;;---------------------------------------------------------------------------
(defthm address-position-bridge
  (equal (+ -1 top (len (member var cenv)))
	 (+ -1 top (- (len cenv) (my-position var cenv)))))

;;---------------------------------------------------------------------------
;; The same holds for accessing the stack with that address, of course.
;; But we don't need this one.
;;---------------------------------------------------------------------------
;; (defthm address-position-bridge
;;   (equal (nth (+ -1 top (len (member var cenv))) stack)
;;	  (nth (+ -1 top (- (len cenv) (my-position var cenv))) stack))
;;   :hints (("Goal" :use ((:instance address-bridge)))))


(include-book "../../../arithmetic/equalities")


;;===========================================================================
;; We need the following lemmas in order to prove the compiler correctness for
;; variable access. Actually, I did not yet completely check whether every
;; theorem is really used. Anyway.
;;---------------------------------------------------------------------------

(defthm skip-elements
  (equal (nth (len l1) (append l1 l2)) (car l2)))

(defthm skip-irrelevant-elements
  (implies (equal (len l1) (len l3))
	   (equal (nth (len l1) (append l3 l2)) (car l2))))

(defthm reverse-equal-len
  (implies (true-listp l) (equal (len (rev l)) (len l))))

(defthm skip-irrelevant-rest
  (implies (and (natp n) (< n (len cenv)))
	      (equal (nth n (append cenv c1))
		     (nth n cenv))))

(defthm position-n-rev-1-append
  (implies (and (natp n)
		(< n k)
		(equal (len vals) k)
		(true-listp vals))
	   (equal (nth n (rev vals))
		  (nth (- (1- k) n)
		       (append vals l2)))))

(defthm mytake-n-takes-n
  (implies (and (natp n) (true-listp vals))
	   (equal (len (mytake n vals)) n)))

(defthm ccc-1-append
  (implies (and (natp n) (< n (len cenv)) (true-listp vals))
	   (equal (nth n (rev (mytake (len cenv) vals)))
		  (nth (- (1- (len cenv)) n)
		       (append (mytake (len cenv) vals) l2)))))

(defthm my-position-<-len-cenv
  (implies (member var cenv)
	   (and (natp (my-position var cenv))
		(< (my-position var cenv) (len cenv)))))

(defthm nth-of-shorter-lists
  (implies (and (natp n) (natp k) (< n k))
	   (equal (nth n (append (mytake k vals) l2))
		  (nth n vals))))

(defthm position-is-below-length
  (implies (member var cenv)
	   (and (natp (+ -1 (len cenv) (- (my-position var cenv))))
		(natp (len cenv))
		(< (+ -1 (len cenv) (- (my-position var cenv))) (len cenv)))))

(defthm correct-addressing-2
  (implies (and (member var cenv) (true-listp vals))
	   (equal (nth (my-position var cenv) (rev (mytake (len cenv) vals)))
		  (nth (- (1- (len cenv)) (my-position var cenv))
		       vals))))

(defthm nth-of-sums
  (implies (and (natp n) (natp top))
	   (equal (nth (+ top n) stack) (nth n (nthcdr top stack)))))

(defthm true-listp-of-nthcdrs
  (implies (true-listp l) (true-listp (nthcdr n l))))


;;===========================================================================
;; The following macro defines our compiler correctness notion for forms:
;; Evaluating a form (in genv and env with n) gives us a value (actually a
;; list with that value). We want to prove, that this is the same value that's
;; been pushed on top of the stack when executing (compile-form form cenv top)
;; in an appropriate global machine environment and on a stack that at least
;; contains the reverse of unbinding the bindings of cenv in env. But we prove
;; this only for well-formed forms, and if the machine evaluation of the
;; compiled code does not abort. That corresponds to proving preservation of
;; partial correctness (2).
;;---------------------------------------------------------------------------

(defmacro cc-theorem (form cenv env top dcls stack n)
  `(implies (and (natp top)
		 (wellformed-defs ,dcls (construct-genv ,dcls))
		 (wellformed-form ,form (construct-genv ,dcls) ,cenv)
		 (defined (msteps (compile-form ,form ,cenv ,top)
				    (download (compile-defs ,dcls));; code
				    ,stack
				    ,n)))
	    (and
	     (defined (evl ,form
			   (construct-genv ,dcls);; genv (evaluator)
			   (bind ,cenv (rev (get-stack-frame ,cenv ,top ,stack))
				 ,env);; (nthcdr (+ ,top (len ,cenv)) ,stack))
			   ,n))
	     (equal
	      (msteps (compile-form ,form ,cenv ,top)
		      (download (compile-defs ,dcls));; code
		      ,stack
		      ,n)
	      (cons (car (evl ,form
			      (construct-genv ,dcls);; genv (evaluator)
			      (bind ,cenv (rev (get-stack-frame ,cenv ,top ,stack))
				    ,env);; (nthcdr (+ ,top (len ,cenv)) ,stack))
			      ,n))
		    ,stack))
	     )))


;; We prove "cc-theorem" for all induction base cases, i.e. for constants
;; (including quoted s-expression constants) and variables (!). The
;; correctness proof ("proof.lisp") uses this theorem in the base case.
;;

(defun base-form (form)
  (or (atom form) (equal (car form) 'QUOTE)))

(defthm cc-base-case
  (implies (and	(base-form form))
	   (cc-theorem form cenv env top dcls stack n))
  :hints (("Goal" :in-theory
	   (disable evlist compile-forms construct-genv download
		    wellformed-form wellformed-forms wellformed-forms-eqn
		    mstep msteps operatorp))))



;;---------------------------------------------------------------------------
;; Induction over instruction sequences.
;;---------------------------------------------------------------------------

(defun msteps-induction (m1 m2 code stack n)
  (if (endp m1) (list m1 m2 code stack n)
    (msteps-induction (cdr m1) m2 code
		      (msteps (list (car m1)) code stack n) n)))

;;---------------------------------------------------------------------------
;; msteps distributes over append. This uses msteps-equation from "machine".
;; The rule normalizes msteps-calls. Whenever we prove something about (msteps
;; (append m1 m2), the rewriter rewrites it to (msteps m2 (msteps m1 ..).

(defthm msteps-distributes-over-append
  (equal (msteps (append m1 m2) code stack n)
	 (msteps m2 code (msteps m1 code stack n) n))
  :hints (("Goal" :induct (msteps-induction m1 m2 code stack n))))


;;---------------------------------------------------------------------------
;; The machine is error strict
;;---------------------------------------------------------------------------

(defthm msteps-strictness
  (implies (defined (msteps forms code stack n)) (defined stack)))

;; simple corollary from msteps-strictness
;; --------------------------------------
;;(defthm msteps-error
;;  (implies (not (defined stack)) (equal (msteps forms code stack n) 'error)))


;; we have msteps-strictness from proof1.lisp which is more general. This one
;; is used by body-strictness-new and we should replace it there by an
;; instance of msteps-strictness
;;
(defthm machine-strictness1
  (implies (defined (msteps m2 code (msteps m1 code stack n) n))
	   (defined (msteps m1 code stack n))))


;;---------------------------------------------------------------------------
;; We prove that the compiler generates syntactically correct code. Some of
;; the properties of machine code we need depend on the code to be
;; syntactically well-formed. So we want to make sure that the compiler
;; generates such code. We need "instructionp" and "instruction-listp" for
;; compiled forms, and codep for downloaded compiled subroutine definitions.
;;---------------------------------------------------------------------------

(defthm instruction-listp-and-append
  (implies (and (instruction-listp m1)
		(instruction-listp m2))
	   (instruction-listp (append m1 m2))))

(defthm wellformed-form-formp
  (implies (wellformed-form x genv cenv) (formp x)))

(defun form-listp-induction (forms)
  (if (consp forms)
      (form-listp-induction (cdr forms))
    t))

(defthm wellformed-forms-form-listp
  (implies (wellformed-forms x genv cenv)
	   (form-listp x))
  :hints (("Goal" :induct (form-listp-induction x))))

(defun compile-induction (flag x env top)
  (if (atom x)
      (list env top)
    (if flag
	(list (compile-induction t (cadr x) env top)
	      (compile-induction t (caddr x) env top)
	      (compile-induction t (cadddr x) env top)
	      (compile-induction nil (cdr x) env top))
      (list (compile-induction t (car x) env top)
	    (compile-induction nil (cdr x) env (1+ top))))))


;;---------------------------------------------------------------------------
;; The machine code compiled for (IF cond then else) works as
;; expected. Moreover, if the compiled code for (IF cond then else) is defined
;; on the machine, then both branches are. Note that for this we NEED the
;; value of the condition.
;;---------------------------------------------------------------------------

(defthm machine-on-if-nil
  (equal (msteps (cons (list 'IF m2 m3) m) code (cons nil stack) n)
	 (msteps (append m3 m) code stack n)))

(defthm machine-on-if-t
  (implies c
	   (equal (msteps (cons (list 'IF m2 m3) m) code (cons c stack) n)
		  (msteps (append m2 m) code stack n))))

(defthm code-for-if-works-correctly
  (implies
   (defined (msteps (append m1 (cons (list 'if m2 m3) m)) code stack n))
   (equal (msteps (cons (list 'if m2 m3) m) code (msteps m1 code stack n) n)
	  (if (car (msteps m1 code stack n))
	      (msteps (append m2 m) code (cdr (msteps m1 code stack n)) n)
	    (msteps (append m3 m) code (cdr (msteps m1 code stack n)) n)))))

