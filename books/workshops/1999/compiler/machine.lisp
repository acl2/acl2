;;=========================================================================
;; Copyright (C) 1999 Institut fuer Informatik, University of Kiel, Germany
;;===========================================================================
;; File:         machine.lisp
;; Author:       Wolfgang Goerigk
;; Content:      ACL2 implementation of a simple abstract machine
;; as of:        14/04/99, University of Texas at Austin, Texas, U.S.A.
;;---------------------------------------------------------------------------
;; $Revision: 1.4 $
;; $Id: machine.lisp,v 1.4 1999/09/26 11:28:16 wg Exp wg $
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
;; The Abstract Stack Machine
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~
;; This book defines the executable ACL2 model of an abstract stack machine
;; and the machine code (TL) used as target code for the compilers in the book
;; "compiler".
;;
;;===========================================================================

(in-package "ACL2")
(include-book "../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;;===========================================================================
;; We use our own version of butlast and call it butlst.
;;---------------------------------------------------------------------------

(defun butlst (x)
  (declare (xargs :guard (true-listp x)))
  (if (consp x)
      (if (consp (cdr x))
	  (if (consp (cddr x))
	      (cons (car x) (butlst (cdr x)))
	    (list (car x)))
	nil)
    nil))

;;===========================================================================
;; The Abstract Machine (Program Semantics)
;;===========================================================================
;;
;; Abstract Machine Programs:
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~
;;   prog  == (decl_1 ... decl_n (instr_1 ... instr_k))
;;   decl  == (DEFCODE <name> (instr_1 ... instr_k))
;;
;; where in both cases n >= 0 and instructions are as defined below.
;;
;; Abstract Machine Configuration:
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;   code  == ((fn_1 . code_1) (fn_2 . code_2) ... (fn_n . code_n))
;;   stack == (top top_1 top_2 ... bottom)
;;
;; Operator calls including calls of user defined procedures consume (pop)
;; their arguments from the stack and push their result on top of the
;; stack. Instructions are
;;
;; Abstract Machine Instructions and Evaluation
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;   (PUSHC <constant>)      ; push <constant> onto the stack
;;   (PUSHV <index>)         ; push the value of the <index>'th stack cell
;;   (CALL <name>)           ; execute the code associated with <name> in code
;;   (OPR <name>)            ; execute the Lisp operator <name> on the stack
;;   (IF <then> <else>)      ; execute <else>, if top = nil, otherwise <then>
;;   (POP <n>)               ; (top d1 ... dn . rest) -> (top . rest)
;;
;; The functions mstep executes a single instruction, applied to the stack and
;; returning the new stack.  msteps executes a sequence of instructions by
;; subsequently executing each of them.
;;
;; Since in general machine programs may not terminate, an additional
;; <number-of-steps> argument (n) forces execution to terminate. Actually, we
;; decrease n only if a user defined subroutine is called, i.e. if we start to
;; execute its body. This is sufficient to guarantee termination since it is
;; the only case, where a structural induction would fail. So the measure
;; functions we use to admit mstep and msteps are (cons (1+ (acl2-count n))
;; (acl2-count form)) and (cons (1+ (acl2-count n)) (acl2-count seq)), i.e. we
;; use the lexicographical ordering of the depth of the call-tree and the
;; complexity of the syntactical structure.  Note that the 1+ is necessary for
;; these conses to be e0-ordinalp's.
;;
;; The instruction (IF <then> <else>) assumes the condition's value on top of
;; stack.  The abstract machine language has structured code.  Operators are
;; those recognized by the function "operatorp" which is defined in
;; "compiler.lisp".
;;
;;---------------------------------------------------------------------------

;;---------------------------------------------------------------------------
;; The Lisp operators
;; ~~~~~~~~~~~~~~~~~~
;; for simplicity we could just use the ACL2 functions that correspond to our
;; operators (see definition of operatorp in "compiler") in order to implement
;; the operators. However, we would not be able to verify the guards because
;; we can not guarantee that the machine program uses the operators within
;; their Common Lisp domains. Therefore we define our own functions but prove
;; them to be equal to the ACL2 versions. The former makes sure that we can
;; certify this book, whereas the latter makes sure that the machine (and
;; hence the evaluator and the compiler) do something reasonable.
;;

(defun MCAR (x)
  (declare (xargs :guard t))
  (if (or (consp x) (equal x nil)) (car x) nil))

(defun MCDR (x)
  (declare (xargs :guard t))
  (if (or (consp x) (equal x nil)) (cdr x) nil))

(defmacro MCADR (X) (LIST 'MCAR (LIST 'MCDR X)))
(defmacro mcddr (X) (LIST 'MCDR (LIST 'MCDR X)))
(defmacro mcdar (X) (LIST 'MCDR (LIST 'MCAR X)))
(defmacro MCADDR (X) (LIST 'MCAR (LIST 'mcddr X)))
(defmacro MCADAR (X) (LIST 'MCAR (LIST 'mcdar X)))
(defmacro mcddar (X) (LIST 'MCDR (LIST 'mcdar X)))
(defmacro mcdddr (X) (LIST 'MCDR (LIST 'mcddr X)))
(defmacro MCADDAR (X) (LIST 'MCAR (LIST 'mcddar X)))
(defmacro MCADDDR (X) (LIST 'MCAR (LIST 'mcdddr X)))

(defun M1+ (n)
  (declare (xargs :guard t))
  (if (acl2-numberp n) (1+ n) 1))

(defun M1- (n)
  (declare (xargs :guard t))
  (if (acl2-numberp n) (1- n) -1))

(defmacro MLEN (X) (LIST 'LEN X))
(defmacro MSYMBOLP (X) (LIST 'SYMBOLP X))
(defmacro MCONSP (X) (LIST 'CONSP X))
(defmacro MATOM (X) (LIST 'ATOM X))
(defmacro MCONS (X Y) (LIST 'CONS X Y))
(defmacro MEQUAL (X Y) (LIST 'EQUAL X Y))

(defun MAPPEND (x y)
  (declare (xargs :guard t))
  (cond ((atom x) y)
	(t (cons (car x)
		 (MAPPEND (cdr x) y)))))

(defun MMEMBER (x l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
	((equal x (car l)) l)
	(t (MMEMBER x (cdr l)))))

(defun MASSOC (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
	((equal x (mcar (car alist))) (car alist))
	(t (MASSOC x (cdr alist)))))

(defun M+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (if (acl2-numberp x) x
      (if (acl2-numberp y) y
	0))))

(defun M- (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (- x y)
    (if (acl2-numberp x) x
      (if (acl2-numberp y) (- y)
	0))))

(defun M* (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (* x y)
    0))

;;---------------------------------------------------------------------------
;; As mentioned above, we now prove that the operators defined by functions
;; are actually as in ACL2, that is that they are equal to the corresponding
;; ACL2 functions. Then we disable them, because we don't want the prover to
;; look into our definitions but let it use what it knows about the original
;; ACL2 functions instead.
;;

(defthm mcar-is-like-car (equal (MCAR x) (car x)))
(defthm mcdr-is-like-cdr (equal (MCDR x) (cdr x)))
(defthm m1+-is-like-1+ (equal (M1+ n) (1+ n)))
(defthm m1--is-like-1- (equal (M1- n) (1- n)))
(defthm mappend-is-like-append (equal (MAPPEND x y) (append x y)))
(defthm mmember-is-like-member (equal (MMEMBER x l) (member x l)))
(defthm massoc-is-like-assoc (equal (MASSOC x alist) (assoc x alist)))
(defthm m+-is-like-+ (equal (M+ x y) (+ x y)))
(defthm m--is-like-- (equal (M- x y) (- x y)))
(defthm m*-is-like-* (equal (M* x y) (* x y)))

(in-theory (disable MCAR MCDR M1+ M1- M+ M* M- MAPPEND MMEMBER MASSOC))


;;---------------------------------------------------------------------------
;; The next is to define some data types, that is to say recognizers for
;; programs, declaration lists, instructions and instruction-lists, and
;; code. This is to be able to express the guards we want to verify. The
;; syntax of machine programs and of the code part of the machine's
;; configuration are as in the comment at the beginning of this book.
;;

(mutual-recursion
(defun instructionp (form)
  (declare (xargs :guard t))
  (and (consp form)
       (consp (cdr form))
       (cond ((equal (car form) 'PUSHC) t)
	     ((equal (car form) 'PUSHV) (natp (cadr form)))
	     ((equal (car form) 'CALL) (symbolp (cadr form)))
	     ((equal (car form) 'OPR) (symbolp (cadr form)))
	     ((equal (car form) 'POP) (natp (cadr form)))
	     ((equal (car form) 'IF)
	      (and (consp (cdr form))
		   (instruction-listp (cadr form))
		   (consp (cddr form))
		   (instruction-listp (caddr form))))
	     (t nil))))


(defun instruction-listp (seq)
  (declare (xargs :guard t))
  (if (consp seq)
    (and (instructionp (car seq))
	 (instruction-listp (cdr seq)))
    (null seq)))
)

(defun codep (l)
  (declare (xargs :guard t))
  (cond ((atom l) (equal l nil))
	(t (and (consp (car l))
		(symbolp (caar l))
		(instruction-listp (cdar l))
		(codep (cdr l))))))

(defun declsp (dcls)
  (declare (xargs :guard t))
  (if (consp dcls)
      (and (consp (car dcls))
	   (equal (caar dcls) 'DEFCODE)
	   (consp (cdar dcls))
	   (symbolp (cadar dcls))
	   (consp (cddar dcls))
	   (instruction-listp (caddar dcls))
	   (declsp (cdr dcls)))
    (null dcls)))

(defun progp (prog)
  (declare (xargs :guard t))
  (and (true-listp prog)
       (declsp (butlst prog))
       (instruction-listp (car (last prog)))))

;;---------------------------------------------------------------------------
;; The function get-code returns the instruction list associated with f within
;; "code".
;;

(defun get-code (f code)
  (declare (xargs :guard (and (symbolp f) (alistp code))))
  (cdr (assoc f code)))


;;---------------------------------------------------------------------------
;; We need the following three theorems in order to be able to verify the
;; guards.
;;

(defthm codep-implies-good-code
  (implies (codep l) (instruction-listp (cdr (assoc f l)))))
(defthm codep-implies-alistp
  (implies (codep code) (alistp code)))
(defthm codep-implies-consp-assoc
  (implies (and (codep l) (assoc sym l)) (consp (assoc sym l))))


;;===========================================================================
;; Now we may start and define the machine. opr applies an operator to the
;; topmost stack cell(s), mstep executes one instruction, msteps an
;; instruction sequence (see the comment at the beginning of this script).
;;

(defun opr (op code stack)
  (declare (ignore code)
	   (xargs :guard (true-listp stack)))
  (cond
   ((equal op 'CAR) (cons (MCAR (car stack)) (cdr stack)))
   ((equal op 'CDR) (cons (MCDR (car stack)) (cdr stack)))
   ((equal op 'CADR) (cons (MCADR (car stack)) (cdr stack)))
   ((equal op 'CADDR) (cons (MCADDR (car stack)) (cdr stack)))
   ((equal op 'CADAR) (cons (MCADAR (car stack)) (cdr stack)))
   ((equal op 'CADDAR) (cons (MCADDAR (car stack)) (cdr stack)))
   ((equal op 'CADDDR) (cons (MCADDDR (car stack)) (cdr stack)))
   ((equal op '1-) (cons (M1- (car stack)) (cdr stack)))
   ((equal op '1+) (cons (M1+ (car stack)) (cdr stack)))
   ((equal op 'LEN) (cons (MLEN (car stack)) (cdr stack)))
   ((equal op 'SYMBOLP) (cons (MSYMBOLP (car stack)) (cdr stack)))
   ((equal op 'CONSP) (cons (MCONSP (car stack)) (cdr stack)))
   ((equal op 'ATOM) (cons (MATOM (car stack)) (cdr stack)))
   ((equal op 'CONS) (cons (MCONS (cadr stack) (car stack)) (cddr stack)))
   ((equal op 'EQUAL) (cons (MEQUAL (cadr stack) (car stack)) (cddr stack)))
   ((equal op 'APPEND) (cons (MAPPEND (cadr stack) (car stack)) (cddr stack)))
   ((equal op 'MEMBER) (cons (MMEMBER (cadr stack) (car stack)) (cddr stack)))
   ((equal op 'ASSOC) (cons (MASSOC (cadr stack) (car stack)) (cddr stack)))
   ((equal op '+) (cons (M+ (cadr stack) (car stack)) (cddr stack)))
   ((equal op '-) (cons (M- (cadr stack) (car stack)) (cddr stack)))
   ((equal op '*) (cons (M* (cadr stack) (car stack)) (cddr stack)))
   ((equal op 'LIST1) (cons (CONS (car stack) nil) (cdr stack)))
   ((equal op 'LIST2) (cons (CONS (cadr stack) (CONS (car stack) nil)) (cddr stack)))
   ))


(mutual-recursion

(defun mstep (form code stack n)
  (declare (xargs :measure (cons (1+ (acl2-count n)) (acl2-count form))
		  :guard (and (instructionp form) (codep code) (natp n))))
  (cond
   ((or (zp n) (not (true-listp stack))) 'ERROR)
   ((equal (car form) 'PUSHC) (cons (cadr form) stack))
   ((equal (car form) 'PUSHV) (cons (nth (cadr form) stack) stack))
   ((equal (car form) 'CALL)
    (msteps (cdr (assoc (cadr form) code)) code stack (1- n)))
   ((equal (car form) 'OPR) (opr (cadr form) code stack))
   ((equal (car form) 'IF)
    (if (car stack)
	(msteps (cadr form) code (cdr stack) n)
      (msteps (caddr form) code (cdr stack) n)))
   ((equal (car form) 'POP) (cons (car stack) (nthcdr (cadr form) (cdr stack))))))

(defun msteps (seq code stack n)
  (declare (xargs :measure (cons (1+ (acl2-count n)) (acl2-count seq))
		  :guard (and (instruction-listp seq) (codep code) (natp n))))

  (cond ((or (zp n) (not (true-listp stack))) 'ERROR)
	((endp seq) stack)
	(t (msteps (cdr seq) code (mstep (car seq) code stack n) n))))

)

;;---------------------------------------------------------------------------
;; In order to download a machine program's subroutine definitions we have to
;; construct the code part of the machine configuration, which is a true
;; association list binding the procedure names to their instruction
;; sequences. That is we have get rid of the DEFCODE's and construct a true
;; association list:
;;
;;    ((DEFCODE f1 code1) (DEFCODE f2 code2) ...)  ->
;;    ((f1 . code1) (f2 . code2) ...)
;;

(defun download (dcls)
  (declare (xargs :guard (declsp dcls)))
  (if (consp dcls)
      (cons (cons (cadar dcls) (caddar dcls))
	    (download (cdr dcls)))
    nil))

;;---------------------------------------------------------------------------
;; Execution of an abstract machine program is executing the top level
;; instruction sequence with the code (download (butlast prog 1)) and the
;; initial stack.
;;

(defun execute (prog stack n)
  (declare (xargs :guard (and (progp prog) (natp n))))
  (let ((code (download (butlst prog))))
    (msteps (car (last prog)) code stack n)))

;;===========================================================================
;;
;; This finishes the definition of the abstract machine.
;;
;; The following two theorems install the definitional equations of "mstep"
;; and "msteps" from the above mutual recursion as :definition rules.
;;
;;---------------------------------------------------------------------------

(defthm msteps-eqn
  (equal (msteps seq code stack n)
	 (cond ((or (zp n) (not (true-listp stack))) 'ERROR)
	       ((endp seq) stack)
	       (t (msteps
		   (cdr seq) code (mstep (car seq) code stack n) n))))
  :rule-classes ((:definition
		  :clique (mstep msteps)
		  :controller-alist
		  ((msteps t nil nil nil) (mstep t nil nil nil)))))


(defthm mstep-eqn
  (equal (mstep form code stack n)
	 (cond
   ((or (zp n) (not (true-listp stack))) 'ERROR)
   ((equal (car form) 'PUSHC) (cons (cadr form) stack))
   ((equal (car form) 'PUSHV) (cons (nth (cadr form) stack) stack))
   ((equal (car form) 'CALL)
    (msteps (cdr (assoc (cadr form) code)) code stack (1- n)))
   ((equal (car form) 'OPR) (opr (cadr form) code stack))
   ((equal (car form) 'IF)
    (if (car stack)
	(msteps (cadr form) code (cdr stack) n)
      (msteps (caddr form) code (cdr stack) n)))
   ((equal (car form) 'POP)
    (cons (car stack) (nthcdr (cadr form) (cdr stack))))))
  :rule-classes ((:definition
		  :clique (mstep msteps)
		  :controller-alist
		  ((msteps t nil nil nil) (mstep t nil nil nil)))))


;;---------------------------------------------------------------------------
;; Now, we may disable mstep and msteps.
;;

(in-theory (disable mstep msteps))

;;---------------------------------------------------------------------------
;; The following function is used to suggest a combined computational and
;; structural induction on the termination argument n and the structural depth
;; of machine instructions and machine instruction sequences.
;;

(defun machine-induction (flag x code stack n)
  (declare (xargs :mode :logic
	          :measure (cons (1+ (acl2-count n)) (acl2-count x))))
  (if (or (atom x) (zp n))
      (list code stack n)
    (if flag
	(if (equal (car x) 'CALL)
	    (machine-induction nil
			       (cdr (assoc (cadr x) code))
			       code stack (1- n))
	  (if (equal (car x) 'IF)
	      (list (machine-induction nil
				       (cadr x)
				       code (cdr stack) n)
		    (machine-induction nil
				       (caddr x)
				       code (cdr stack) n))
	    (list code stack n)))
      (list (machine-induction t (car x) code stack n)
	    (machine-induction nil (cdr x)
			       code
			       (mstep (car x) code stack n)
			       n)))))









