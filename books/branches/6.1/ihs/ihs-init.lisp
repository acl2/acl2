; ihs-init.lisp -- root of the IHS libraries
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    ihs-init.lisp
;;;
;;;    The root of the IHS (Integer Hardware Specification) library
;;;    hierarchy.  This file is divided into 4 parts, as documented in the
;;;    IHS-INIT label below.
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West Sixth Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "ihs-doc-topic")
(include-book "data-structures/utilities" :dir :system)


(deflabel ihs-init
  :doc ":doc-section ihs
  The root of the IHS (Integer Hardware Specification) library hierarchy.~/

  Documented topics include:
  ~/

  This book is included by every book in the IHS hierarchy.

  The book \"ihs-init\" contains

  1.  Definitions of CLTL functions that should be part of the Acl2
  BOOT-STRAP theory.  Since Acl2 won't let us redefine any Common Lisp
  symbol, these functions are uniformly named by <CLTL name>$.

  2.  Functions that are not defined by CLTL, but that are otherwise
  candidates for the Acl2 boot-strap theory.

  3.  Unassigned functions that are general purpose, and will probably
  find a place in another book someday.

  4.  Definition of macros, macro helper-functions, and utility functions
  that are used throughout the IHS libraries.  We have no thought of ever
  verifying any of these.  Thus, the guards of certain functions may be just
  strong enough to get the functions admitted.~/")


;;;****************************************************************************
;;;
;;;  Part 1. -- Common Lisp Functions.  Page references are to CLTL.
;;;
;;;****************************************************************************

;;;  WHEN test &REST forms [Macro]
;;;
;;;  p. 115
;;;
;;;  I prefer to use WHEN rather than the alternatives: I think it's more
;;;  compact and mnemonic, and it indents nicely.  I don't necessarily agree
;;;  with Steele's `style note' about when to WHEN.
;;;
;;;  A PROGN is only generated if there is more that one form. The user will
;;;  have to know if PROGN's are allowed in the context in which WHEN is used.

(defmacro when$ (test &rest forms)
  (if (consp forms)
      (if (consp (cdr forms))
	  `(IF ,test (PROGN ,@forms) NIL)
	`(IF ,test ,@forms NIL))
    `(IF ,test NIL NIL)))		;This is a wierd case, maybe an error?

;;;  UNLESS test &REST forms [Macro]
;;;
;;;  p. 115
;;;
;;;  See notes on WHEN above.

(defmacro unless$ (test &rest forms)
  (if (consp forms)
      (if (consp (cdr forms))
	  `(IF ,test NIL (PROGN ,@forms))
	`(IF ,test NIL ,@forms))
    `(IF ,test NIL NIL)))

;;;  LET* bindings &REST body
;;;
;;;  A more robust version of LET*.

(defun pairwise-list (x y)
  "Like PAIRLIS, but LISTs instead of CONSes."
  (declare (xargs :guard (and (true-listp x)
			      (true-listp y)
			      (eql (length x) (length y)))))
  (cond ((endp x) ())
	(t (cons (list (car x) (car y))
		 (pairwise-list (cdr x) (cdr y))))))

(defun let*$fn (bindings body)
  "LET* for the case that BODY is a single form."
  (declare (xargs :guard (eqlable-alistp bindings)))
  (cond ((endp bindings) body)
	(t `(LET (,(car bindings)) ,(let*$fn (cdr bindings) body)))))

(defmacro let*$ (bindings &rest body)
  "A redefinition of LET* that handles declarations, and removes the old
  `no-duplicatesp' guard."
  (declare (xargs :guard (eqlable-alistp bindings)))
  (cond
   ((and (consp body) (consp (cdr body))) ;Body contains multiple forms.
    (let ((unique-vars (remove-duplicates (strip-cars bindings))))
      (let ((unique-bindings (pairwise-list unique-vars unique-vars)))
	(let ((new-body `(LET ,unique-bindings ,@body)))
	  (let*$fn bindings new-body)))))
   (t (let*$fn bindings (car body)))))


;;;****************************************************************************
;;;
;;;  Part 2. -- Extensions to Acl2 for inclusion later (hopefully).
;;;
;;;****************************************************************************


;;;****************************************************************************
;;;
;;;  Part 3. -- Unassigned.
;;;
;;;****************************************************************************

(defun constant-syntaxp (x)
  ":doc-section ihs-init
  A recognizer for Acl2 constants for use with SYNTAXP.
  ~/
  We define CONSTANT-SYNTAXP as a :LOGIC function, rather than a macro, for the
  most efficient execution possible.~/~/"

  (declare (xargs :guard t))

  (and (consp x) (eq (car x) 'QUOTE)))


;;;****************************************************************************
;;;
;;;  Part 4. -- Macros, macro-helpers, and utility functions.
;;;
;;;****************************************************************************

(deflabel ihs-utilities
  :doc ":doc-section ihs-init
  Utility macros and functions used throughout the IHS-BOOKS hierarchy.~/~/~/")

;;;  Import some utilties from the public "utilities" book.

(u::import-as-macros
 U::A-UNIQUE-SYMBOL-IN-THE-U-PACKAGE
 bomb
 defloop
 pack-intern
 pack-string)

;;;  MLAMBDA args term

(defun mlambda-fn (args form)
  (declare (xargs :guard (symbol-listp args)))
  (cond ((atom form)
	 (cond ((member form args) form)
	       (t (list 'QUOTE form))))
	(t (list 'CONS (mlambda-fn args (car form))
		 (mlambda-fn args (cdr form))))))

(defmacro mlambda (args form)
  ":doc-section ihs-init
  Macro LAMBDA form.
  ~/
  Example:

  (DEFMACRO X/Y-GUARD (X Y)
    (MLAMBDA (X Y) (AND (RATIONALP X) (RATIONALP Y) (NOT (EQUAL Y 0)))))

  =

  (DEFMACRO X/Y-GUARD (X Y)
    (LIST 'AND (LIST 'RATIONALP X) (LIST 'RATIONALP Y)
          (LIST (LIST 'NOT (LIST 'EQUAL Y 0)))))

  =

  (DEFMACRO X/Y-GUARD (X Y)
    `(AND (RATIONALP ,X) (RATIONALP ,Y) (NOT (EQUAL ,Y 0))))
  ~/
  MLAMBDA is a macro LAMBDA.  MLAMBDA converts form to a lisp macro body,
  substituting all symbols except those that appear in the args with the
  quoted symbol.~/"

  (declare (xargs :guard (symbol-listp args)))
  (mlambda-fn args form))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Theory Manipulation
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;;;  E/D -- An ENABLE/DISABLE macro.

;;; The E/D macro has been incorporated into ACL2 Version  2.7.

#|
(defun e/d-fn (theory e/d-list enable-p)
  "Constructs the theory expression for the E/D macro."
  (declare (xargs :guard (and (true-listp e/d-list)
			      (or (equal enable-p t)
				  (equal enable-p nil)))
		  :verify-guards nil))
  (cond ((atom e/d-list) theory)
	((not (listp (car e/d-list)))
	 (er hard 'e/d
	     "The arguments to the E/D macro must all be lists.
         This ==> ~p0, is not a list." (car e/d-list)))
	(enable-p (e/d-fn `(UNION-THEORIES ,theory ',(car e/d-list))
			  (cdr e/d-list) nil))
	(t (e/d-fn `(SET-DIFFERENCE-THEORIES ,theory ',(car e/d-list))
		   (cdr e/d-list) t))))

(defmacro e/d (&rest theories)
  "doc-section ihs-utilities
  ENABLE/DISABLE theories.~/
  E/D creates theory expressions for use in IN-THEORY events, :IN-THEORY
  hints, etc.  It provides a convenient way to ENABLE and DISABLE
  simultaneously, without having to write arcane theory expressions.

  Examples:
  ~bv[]
  (e/d (lemma1 lemma2))                 ;Equivalent to (ENABLE lemma1 lemma2).
  (e/d () (lemma))                      ;Equivalent to (DISABLE lemma).
  (e/d (lemma1) (lemma2 lemma3))        ;ENABLE lemma1 then DISABLE lemma2 and
                                        ;lemma3.
  (e/d () (theory1) (theory2))          ;DISABLE theory1 then ENABLE
                                        ;theory2.~/
  ~ev[]

  General Form:
  ~bv[]
  (E/D enables-0 disables-0 ... enables-n disables-n)
  ~ev[]

  The E/D macro takes any number of lists suitable for the ENABLE and DISABLE
  macros (see :doc ENABLE and :doc DISABLE), and creates a theory that is
  equal to (CURRENT-THEORY :HERE) after executing the following commands:

  ~bv[]
  (IN-THEORY (ENABLE . enables-0))
  (IN-THEORY (DISABLE . disables-0))
  ...
  (IN-THEORY (ENABLE . enables-n))
  (IN-THEORY (DISABLE . disables-n))
  ~ev[]~/"

  (declare (xargs :guard (true-listp theories)))

  (cond
   ((atom theories) '(CURRENT-THEORY :HERE))
   (t (e/d-fn '(CURRENT-THEORY :HERE) theories t))))
|#

;;;  ENABLE-THEORY
;;;  DISABLE-THEORY

(defmacro enable-theory (theory-expression)
  ":doc-section ihs-utilities
   Creates an IN-THEORY event that is equivalent to ENABLEing the
   theory-expression.  Note that theory-expression is evaluated.~/~/~/
   "

  `(IN-THEORY (UNION-THEORIES (CURRENT-THEORY :HERE) ,theory-expression)))

(defmacro disable-theory (theory-expression)
  ":doc-section ihs-utilities
   Creates an IN-THEORY event that is equivalent to DISABLEing
   the theory-expression.  Note that theory-expression is evaluated.~/~/~/
   "

  `(IN-THEORY (SET-DIFFERENCE-THEORIES
	       (CURRENT-THEORY :HERE)
	       ,theory-expression)))

;;;  REWRITE-THEORY name
;;;  REWRITE-FREE-THEORY name

(defun rewrite-theory (theory)
  ":doc-section ihs-utilities
  Collects all of the :REWRITE runes from theory.~/~/~/
  "

  (declare (xargs :guard (true-listp theory)))
  (cond ((endp theory) ())
	((and (consp (car theory))
	      (equal (caar theory) :rewrite))
	 (cons (car theory)
	       (rewrite-theory (cdr theory))))
	(t (rewrite-theory (cdr theory)))))

(defun rewrite-free-theory (theory)
  ";doc-section ihs-utilities
  Returns the theory with all :REWRITE rules deleted.~/~/~/
  "

  ;;  The guard is provided only to admit the function.
  (declare (xargs :guard (true-listp theory)))
  (set-difference-equal theory (rewrite-theory theory)))

;;;  DEFINITION-THEORY name
;;;  DEFINITION-FREE-THEORY name

(defun definition-theory (theory)
  ":doc-section ihs-utilities
  Collects all of the :DEFINITION runes from theory.~/~/~/
  "

  (declare (xargs :guard (true-listp theory)))
  (cond ((endp theory) ())
	((and (consp (car theory))
	      (equal (caar theory) :definition))
	 (cons (car theory)
	       (definition-theory (cdr theory))))
	(t (definition-theory (cdr theory)))))

(defun definition-free-theory (theory)
  "doc-section ihs-utilities
  Returns the theory with all :DEFINITION rules deleted.~/~/~/
  "
  ;;  The guard is provided only to admit the function.
  (declare (xargs :guard (true-listp theory)))
  (set-difference-equal theory (definition-theory theory)))

;;;  DEFUN-THEORY

(defun defun-theory-fn (names theory quiet missing)
  ;;  The guard is provided only to admit the function.
  (declare (xargs :guard (symbol-listp names)
		  :verify-guards nil))
  (cond ((endp names)
	 (cond ((or quiet (null missing)) nil)
	       (t (er hard 'DEFUN-THEORY
		      "The following names you supplied to ~
                          DEFUN-THEORY do not have a :DEFINITION ~
                          in the theory you ~
                          supplied.  Check to make sure that the theory is ~
                          correct (it defaults to (UNIVERSAL-THEORY :HERE)) ~
                          and that these are not the names of macros. ~
                          To avoid this message specify :QUIET T in the ~
                          call to DEFUN-THEORY. ~
                          Missing names: ~p0" missing))))
	(t
	 (let*
	     ((name (car names))
	      (defrune `(:DEFINITION ,name))
	      (execrune `(:EXECUTABLE-COUNTERPART ,name))
	      (inductrune `(:INDUCTION ,name))
	      (typerune `(:TYPE-PRESCRIPTION ,name))
	      (tail (member-equal defrune theory)))
	   (cond
	    ((not tail) (defun-theory-fn
			  (cdr names) theory quiet (cons name missing)))
	    (t (cons
		defrune
		(append
		 (if (member-equal execrune tail) (list execrune) nil)
		 (if (member-equal inductrune tail) (list inductrune) nil)
		 (if (member-equal typerune tail) (list typerune) nil)
		 (defun-theory-fn (cdr names) theory quiet missing)))))))))

(defmacro defun-theory
  (names &key
	 (theory '(UNIVERSAL-THEORY :HERE))
	 quiet)

  ":doc-section ihs-utilities
  Collects and returns a special set of runes.~/~/
  DEFUN-THEORY searches the theory and collects the :DEFINITION, :INDUCTION,
  :TYPE-PRESCRIPTION, and :EXECUTABLE-COUNTERPART runes that were put into
  the theory by (DEFUN name ... ), for each name in names.  The default for
  the theory argument is (UNIVERSAL-THEORY :HERE).  Normally the function
  will crash if any of the names in names do not have a :DEFINITION in the
  theory.  Call with :QUIET T to avoid this behavior.  Note however that
  limitations in Acl2 make it impossible to produce even a warning message if
  you specify :QUIET T.~/

  "

  `(DEFUN-THEORY-FN ,names ,theory ,quiet ()))

;;;  DEFUN-TYPE/EXEC-THEORY

(defun defun-type/exec-theory-fn (names theory quiet missing)
  ;;  The guard is provided only to admit the function.
  (declare (xargs :guard (symbol-listp names)
		  :verify-guards nil))
  (cond ((endp names)
	 (cond ((or quiet (null missing)) nil)
	       (t (er hard 'DEFUN-TYPE/EXEC-THEORY
		      "The following names you supplied to ~
                       DEFUN-TYPE/EXEC-THEORY do not have an ~
                      :INDUCTION, ~
                      :EXECUTABLE-COUNTERPART, or any ~
                      :TYPE-PRESECRIPTIONs in the theory you ~
                      supplied.  Check to make sure that the theory is ~
                      correct (it defaults to (UNIVERSAL-THEORY :HERE)) ~
                      and that these are not the names of macros. ~
                      To avoid this message specify :QUIET T in the ~
                      call to DEFUN-TYPE/EXEC-THEORY. ~
                      Missing names: ~p0" missing))))
	(t
	 (let* ((name (car names))
		(execrune `(:EXECUTABLE-COUNTERPART ,name))
		(inductrune `(:INDUCTION ,name))
		(typerune `(:TYPE-PRESCRIPTION ,name))
		(thy
		 (append
		  (if (member-equal execrune theory) (list execrune) nil)
		  (if (member-equal inductrune theory) (list inductrune) nil)
		  (if (member-equal typerune theory) (list typerune) nil))))
	   (cond ((null thy)
		  (defun-type/exec-theory-fn
		    (cdr names) theory quiet (cons name missing)))
	    (t (append
		thy
		(defun-type/exec-theory-fn (cdr names)
		  theory quiet missing))))))))

(defmacro defun-type/exec-theory
  (names &key
	 (theory '(UNIVERSAL-THEORY :HERE))
	 quiet)

  ":doc-section ihs-utilities
  Collects and returns a special set of runes.~/~/

  DEFUN-TYPE/EXEC-THEORY searches the theory and collects the
  :TYPE-PRESCRIPTION, :EXECUTABLE-COUNTERPART, and :INDUCTION runes that were
  put into the theory by (DEFUN name ... ), for each name in names.  Thus,
  DEFUN-TYPE/EXEC-THEORY is a \"constructive\" dual of (DIASBLE . names).
  The default for the theory argument is (UNIVERSAL-THEORY :HERE).  Normally
  the function will crash if any of the names in names do not have a single
  rune in the theory. Call with :QUIET T to avoid this behavior.  Note
  however that limitations in Acl2 make it impossible to produce even a
  warning message if you specify :QUIET T.~/

  "

  `(DEFUN-TYPE/EXEC-THEORY-FN ,names ,theory ,quiet ()))

#|
Examples.

(let ((world (w state))) (defun-theory '(length)))
(let ((world (w state))) (defun-theory '(length cond)))
(let ((world (w state))) (defun-theory '(length cond) :quiet t))
(let ((world (w state))) (defun-theory '(length cond)
			   :theory
			   (universal-theory 'exit-boot-strap-mode)
			   :quiet t))

(let ((world (w state))) (defun-type/exec-theory '(length)))
(let ((world (w state))) (defun-type/exec-theory '(length cond)))
(let ((world (w state))) (defun-type/exec-theory '(length cond) :quiet t))
(let ((world (w state))) (defun-type/exec-theory '(length cond)
			   :theory (universal-theory 'exit-boot-strap-mode)
			   :quiet t))

|#
