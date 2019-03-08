; ihs-init.lisp -- root of the IHS libraries
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

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
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")
(include-book "ihs-doc-topic")
(include-book "data-structures/utilities" :dir :system)

(defxdoc ihs-init
  :parents (ihs)
  :short "The root of the IHS (Integer Hardware Specification) library hierarchy."

  :long "<p>The @('ihs-init') book is included by every book in the IHS
hierarchy.  It contains:</p>

<ul>

<li>Definitions of CLTL functions that should be part of the ACL2 BOOT-STRAP
theory.  Since ACL2 won't let us redefine any Common Lisp symbol, these
functions are uniformly named by @('<CLTL name>$').</li>

<li>Functions that are not defined by CLTL, but that are otherwise candidates
for the ACL2 boot-strap theory.</li>

<li>Unassigned functions that are general purpose, and will probably find a
place in another book someday.</li>

<li>Definition of macros, macro helper-functions, and utility functions that
are used throughout the IHS libraries.  We have no thought of ever verifying
any of these.  Thus, the guards of certain functions may be just strong enough
to get the functions admitted.</li>

</ul>")


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

(defmacro when$cl (test &rest forms)
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

(defmacro unless$cl (test &rest forms)
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
;;;  Part 2. -- Extensions to ACL2 for inclusion later (hopefully).
;;;
;;;****************************************************************************

;;;****************************************************************************
;;;
;;;  Part 3. -- Unassigned.
;;;
;;;****************************************************************************

(defun constant-syntaxp (x)
  ;; [Jared] removing documentation because this is identical to QUOTEP and
  ;; there is no reason to use it instead of QUOTEP.
  (declare (xargs :guard t))
  (and (consp x) (eq (car x) 'QUOTE)))

;;;****************************************************************************
;;;
;;;  Part 4. -- Macros, macro-helpers, and utility functions.
;;;
;;;****************************************************************************

(defxdoc ihs-utilities
  :parents (ihs-init)
  :short "Utility macros and functions used throughout the IHS books.")

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

(defsection mlambda
  :parents (ihs-utilities)
  :short "Macro LAMBDA form."
  :long "<p>Example:</p>

   @({

  (DEFMACRO X/Y-GUARD (X Y)
    (MLAMBDA (X Y) (AND (RATIONALP X) (RATIONALP Y) (NOT (EQUAL Y 0)))))

    =

  (DEFMACRO X/Y-GUARD (X Y)
    (LIST 'AND (LIST 'RATIONALP X) (LIST 'RATIONALP Y)
          (LIST (LIST 'NOT (LIST 'EQUAL Y 0)))))

  =

  (DEFMACRO X/Y-GUARD (X Y)
    `(AND (RATIONALP ,X) (RATIONALP ,Y) (NOT (EQUAL ,Y 0))))
  })

  <p>MLAMBDA is a macro LAMBDA.  MLAMBDA converts form to a lisp macro body,
  substituting all symbols except those that appear in the args with the quoted
  symbol.</p>"

  (defmacro mlambda (args form)
    (declare (xargs :guard (symbol-listp args)))
    (mlambda-fn args form)))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Theory Manipulation
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

; [Jared] removed commented out definition of e/d, which has been incorporated
; into ACL2 Version 2.7.

(defsection enable-theory
  :parents (ihs-utilities)
  :short "Creates an @(see IN-THEORY) event that is equivalent to ENABLEing the
   theory-expression.  Note that theory-expression is evaluated."

  (defmacro enable-theory (theory-expression)
    `(in-theory (union-theories (current-theory :here) ,theory-expression))))

(defsection disable-theory
  :parents (ihs-utilities)
  :short "Creates an IN-THEORY event that is equivalent to DISABLEing the
  theory-expression.  Note that theory-expression is evaluated."

  (defmacro disable-theory (theory-expression)
    `(IN-THEORY (SET-DIFFERENCE-THEORIES
                 (CURRENT-THEORY :HERE)
                 ,theory-expression))))


(defsection rewrite-theory
  :parents (ihs-utilities)
  :short "Collects all of the :REWRITE runes from theory."

  (defun rewrite-theory-rec (theory ans)
    (declare (xargs :guard (and (true-listp theory)
                                (true-listp ans))))
    (cond ((endp theory) (reverse ans))
          ((and (consp (car theory))
                (equal (caar theory) :rewrite))
           (rewrite-theory-rec (cdr theory)
                               (cons (car theory) ans)))
          (t (rewrite-theory-rec (cdr theory) ans))))

  (defun rewrite-theory (theory)
    ;; Changed by Matt K. 9/2014 to use tail recursion.
    (declare (xargs :guard (true-listp theory)))
    (rewrite-theory-rec theory nil)))


(defsection rewrite-free-theory
  :parents (ihs-utilities)
  :short "Returns the theory with all :REWRITE rules deleted."

; Changed by Matt K. 9/2014 to use tail recursion.

; Old comment:

; Change by Matt K. mod, 6/9/2014: The use of set-difference-equal here and/or
; in definition-free-theory caused a stack overflow in Allegro CL.  Even in
; CCL, we found that it took over 10 seconds on a reasonably modern machine to
; evaluate the form
; (rewrite-free-theory (definition-free-theory (universal-theory 'ihs-theories)))
; after
; (include-book "centaur/vl/top" :dir :system)
; and
; (include-book "ihs/ihs-theories" :dir :system).
; After the change to this function and definition-free-theory, the time was
; reduced to 0.05 seconds (realtime and runtime) -- reduction by more than two
; orders of magnitude!  The above evaluation produced the same result, up to
; ordering, after the changes.

; (set-difference-equal theory (rewrite-theory theory)

  (defun rewrite-free-theory-rec (theory ans)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (and (true-listp theory)
                                (true-listp ans))))
    (cond ((endp theory) (reverse ans))
          ((and (consp (car theory))
                (equal (caar theory) :rewrite))
           (rewrite-free-theory-rec (cdr theory) ans))
          (t (rewrite-free-theory-rec (cdr theory)
                                      (cons (car theory) ans)))))

  (defun rewrite-free-theory (theory)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (true-listp theory)))
    (rewrite-free-theory-rec theory nil)))


(defsection definition-theory
  :parents (ihs-utilities)
  :short "Collects all of the :DEFINITION runes from theory."

  (defun definition-theory-rec (theory ans)
    ;; Changed by Matt K. 9/2014 to use tail recursion.
    (declare (xargs :guard (and (true-listp theory)
                                (true-listp ans))))
    (cond ((endp theory) (reverse ans))
          ((and (consp (car theory))
                (equal (caar theory) :definition))
           (definition-theory-rec (cdr theory) (cons (car theory) ans)))
          (t (definition-theory-rec (cdr theory) ans))))

  (defun definition-theory (theory)
    ;; Changed by Matt K. 9/2014 to use tail recursion.
    (declare (xargs :guard (true-listp theory)))
    (definition-theory-rec theory nil)))



(defsection definition-free-theory
  :parents (ihs-utilities)
  :short "Returns the theory with all :DEFINITION rules deleted."

; Changed by Matt K. 9/2014 to use tail recursion.

; Earlier change by Matt K. mod, 6/9/2014: Also see rewrite-free-theory for why
; we didn't use this:

; (set-difference-equal theory (definition-theory theory)

  (defun definition-free-theory-rec (theory ans)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (and (true-listp theory)
                                (true-listp ans))))
    (cond ((endp theory) (reverse ans))
          ((and (consp (car theory))
                (equal (caar theory) :definition))
           (definition-free-theory-rec (cdr theory) ans))
          (t (definition-free-theory-rec (cdr theory) (cons (car theory) ans)))))

  (defun definition-free-theory (theory)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (true-listp theory)))
    (definition-free-theory-rec theory nil)))



;;;  DEFUN-THEORY

(defsection defun-theory
  :parents (ihs-utilities)
  :short "Collects and returns a special set of runes."
  :long "<p>@(call defun-theory) searches the theory and collects
the :DEFINITION, :INDUCTION, :TYPE-PRESCRIPTION, and :EXECUTABLE-COUNTERPART
runes that were put into the theory by (DEFUN name ... ), for each name in
@('names').</p>

<p>The default for the theory argument is (UNIVERSAL-THEORY :HERE).  Normally
the function will crash if any of the names in names do not have a :DEFINITION
in the theory.  Call with :QUIET T to avoid this behavior.  Note however that
limitations in ACL2 make it impossible to produce even a warning message if you
specify :QUIET T.</p>"

  (defun defun-theory-fn-rec (names theory quiet missing ans)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (and (symbol-listp names)
                                (true-listp ans))
                    :verify-guards nil))
    (cond ((endp names)
           (cond ((or quiet (null missing)) (reverse ans))
                 (t (er hard 'DEFUN-THEORY
                        "The following names you supplied to DEFUN-THEORY do ~
                       not have a :DEFINITION in the theory you supplied.  ~
                       Check to make sure that the theory is correct (it ~
                       defaults to (UNIVERSAL-THEORY :HERE)) and that these ~
                       are not the names of macros. To avoid this message ~
                       specify :QUIET T in the call to DEFUN-THEORY. Missing ~
                       names: ~p0"
                        missing))))
          (t
           (let*
               ((name (car names))
                (defrune `(:DEFINITION ,name))
                (execrune `(:EXECUTABLE-COUNTERPART ,name))
                (inductrune `(:INDUCTION ,name))
                (typerune `(:TYPE-PRESCRIPTION ,name))
                (tail (member-equal defrune theory)))
             (cond
              ((not tail) (defun-theory-fn-rec
                            (cdr names) theory quiet (cons name missing) ans))
              (t (defun-theory-fn-rec (cdr names) theory quiet missing
                   (append
                    (if (member-equal typerune tail) (list typerune) nil)
                    (if (member-equal inductrune tail) (list inductrune) nil)
                    (if (member-equal execrune tail) (list execrune) nil)
                    (cons defrune ans)))))))))

  (defun defun-theory-fn (names theory quiet missing)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (symbol-listp names)
                    :verify-guards nil))
    ;; Changed by Matt K. 9/2014 to use tail recursion.
    (defun-theory-fn-rec names theory quiet missing nil))

  (defmacro defun-theory
    (names &key
           (theory '(UNIVERSAL-THEORY :HERE))
           quiet)
    `(DEFUN-THEORY-FN ,names ,theory ,quiet ())))



(defsection defun-type/exec-theory
  :parents (ihs-utilities)
  :short "Collects and returns a special set of runes."
  :long "<p>@(call DEFUN-TYPE/EXEC-THEORY) searches the theory and collects
the :TYPE-PRESCRIPTION, :EXECUTABLE-COUNTERPART, and :INDUCTION runes that were
put into the theory by (DEFUN name ... ), for each name in names.  Thus,
DEFUN-TYPE/EXEC-THEORY is a \"constructive\" dual of (DIASBLE . names).</p>

<p>The default for the theory argument is (UNIVERSAL-THEORY :HERE).  Normally
the function will crash if any of the names in names do not have a single rune
in the theory. Call with :QUIET T to avoid this behavior.  Note however that
limitations in ACL2 make it impossible to produce even a warning message if you
specify :QUIET T.</p>"

  (defun defun-type/exec-theory-fn-rec (names theory quiet missing ans)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (and (symbol-listp names)
                                (true-listp ans))
                    :verify-guards nil))
    ;; Changed by Matt K. 9/2014 to use tail recursion.
    (cond ((endp names)
           (cond ((or quiet (null missing)) (reverse ans))
                 (t (er hard 'DEFUN-TYPE/EXEC-THEORY
                        "The following names you supplied to ~
                       DEFUN-TYPE/EXEC-THEORY do not have an :INDUCTION, ~
                       :EXECUTABLE-COUNTERPART, or any :TYPE-PRESECRIPTIONs ~
                       in the theory you supplied.  Check to make sure that ~
                       the theory is correct (it defaults to ~
                       (UNIVERSAL-THEORY :HERE)) and that these are not the ~
                       names of macros. To avoid this message specify :QUIET ~
                       T in the call to DEFUN-TYPE/EXEC-THEORY. Missing ~
                       names: ~p0"
                        missing))))
          (t
           (let* ((name (car names))
                  (execrune `(:EXECUTABLE-COUNTERPART ,name))
                  (inductrune `(:INDUCTION ,name))
                  (typerune `(:TYPE-PRESCRIPTION ,name))
                  (thy
                   (append
                    (if (member-equal typerune theory) (list typerune) nil)
                    (if (member-equal inductrune theory) (list inductrune) nil)
                    (if (member-equal execrune theory) (list execrune) nil))))
             (cond ((null thy)
                    (defun-type/exec-theory-fn-rec
                      (cdr names) theory quiet (cons name missing) ans))
                   (t (defun-type/exec-theory-fn-rec
                        (cdr names) theory quiet missing
                        (append thy ans))))))))

  (defun defun-type/exec-theory-fn (names theory quiet missing)
    ;;  The guard is provided only to admit the function.
    (declare (xargs :guard (symbol-listp names)
                    :verify-guards nil))
    ;; Changed by Matt K. 9/2014 to use tail recursion.
    (defun-type/exec-theory-fn-rec names theory quiet missing nil))

  (defmacro defun-type/exec-theory
    (names &key
           (theory '(UNIVERSAL-THEORY :HERE))
           quiet)
    `(DEFUN-TYPE/EXEC-THEORY-FN ,names ,theory ,quiet ())))

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
