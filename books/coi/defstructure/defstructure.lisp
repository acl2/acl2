#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
; defstructure.lisp -- a book about typed structures (came from a book called structures.lisp and had the defstructure+ macro added)
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bishop Brock
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    defstructure.lisp (was structures.lisp)
;;;
;;;    Define and characterize a general purpose record structure with typed
;;;    slots.
;;;
;;;    The on-line documentation only contains examples and a formal syntax
;;;    description. The complete documentation for DEFSTRUCTURE is a report
;;;    entitled "DEFSTRUCTURE for ACL2." This report is distributed with the
;;;    ACL2 release, and is also available from the ACL2 home page:
;;;
;;;    http://www.cs.utexas.edu/users/moore/acl2
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;  Package Note:
;;;
;;;  The majority of the following code resides in the "STRUCTURES" package.
;;;  The macro exported by this book, DEFSTRUCTURE, resides in the "ACL2"
;;;  package.
;;;
;;;  Among other reasons for placing this code in a separate package is that
;;;  these macros often need to create variable names.  As long as one does
;;;  not attempt to define structures in the "STRUCTURES" package these names
;;;  will not collide with the user's slot names.
;;;
;;;  This book can only be loaded in an environment that includes the
;;;  "STRUCTURES" package and the "U" package (from the utilities book).
;;;  To define the "STRUCTURES" package, see define-structures-package.lsp

;;;
;;;  Style Note:
;;;
;;;  These macros generate a lot of Acl2 code, and backquote is used
;;;  extensively to do this.  You will see some cases where backquote is used
;;;  to do simple stuff, like `(,x) as opposed to (LIST x).  The convention
;;;  is that every symbolic `result' created by these macros is created using
;;;  backquote, to make it clear that this result is Acl2 code, and not just
;;;  some internal data structure used by the macros and functions.
;;;
;;;  All constant symbols are always uppercased, e.g., 'SYMBOL.  This
;;;  convention extends to backquoted forms, where constant symbols are
;;;  uppercased, but forms in the scope of a comma are lowercased.  This
;;;  convention provides a visual clue as to what is constant and what is
;;;  variable.
;;;

(in-package "STRUCTURES")

(include-book "../paths/path")
(include-book "data-structures/utilities" :dir :system)

(program)

(set-ignore-ok t)


;;;****************************************************************************
;;;
;;;   Documentation
;;;
;;;****************************************************************************

(include-book "xdoc/top" :dir :system)
(defmacro defxdoc (&rest args)
  `(acl2::defxdoc ,@args))

; This legacy doc string was replaced Nov. 2014 by auto-generated defxdoc form
; below.
;(defdoc defstructure
;
; ":doc-section defstructure
;Define and characterize a general purpose record structure with typed slots.

;The on-line documentation only contains examples and a formal syntax
;description. The complete documentation for DEFSTRUCTURE is a report entitled
;\"DEFSTRUCTURE for ACL2.\"  This report is distributed with the ACL2 release,
;and is also available from the ACL2 home page:

;http://www.cs.utexas.edu/users/moore/acl2
;~/
;Examples:

;(DEFSTRUCTURE SHIP X-POSITION Y-POSITION X-VELOCITY Y-VELOCITY MASS)
;
;(DEFSTRUCTURE MC-STATE
;  \"The state of the MC68020.\"
;  (STATUS (:ASSERT (SYMBOLP STATUS) :TYPE-PRESCRIPTION))
;  (RFILE  (:ASSERT (RFILEP RFILE) :REWRITE))
;  (PC     (:ASSERT (LONGWORD-P PC) :REWRITE
;                   (:TYPE-PRESCRIPTION (NATURALP PC))))
;  (CCR    (:ASSERT (CCR-P CCR) :REWRITE
;                   (:TYPE-PRESCRIPTION (NATURALP CCR))))
;  (MEM    (:ASSERT (MEMORYP MEM) :REWRITE))
;
;  (:OPTIONS :GUARDS (:CONC-NAME MC-)))
;
;(DEFSTRUCTURE S&ADDR
;  \"An MC68020 effective address abstraction.\"
;  (S     (:ASSERT (MC-STATE-P S) :REWRITE))
;  (LOC   (:ASSERT (SYMBOLP LOC)  :TYPE-PRESCRIPTION))
;  (ADDR  (:ASSERT ((LAMBDA (LOC ADDR)
;                     (CASE LOC
;                       ((D A) (RN-NUMBERP ADDR))
;                       ((M I) (LONGWORD-P ADDR))
;                       (OTHERWISE (NULL ADDR))))
;                   LOC ADDR)
;                  (:REWRITE
;                   (IMPLIES
;                    (OR (EQUAL LOC 'D) (EQUAL LOC 'A))
;                    (RN-NUMBERP ADDR)))
;                  (:REWRITE
;                   (IMPLIES
;                    (OR (EQUAL LOC 'M) (EQUAL LOC 'I))
;                    (LONGWORD-P ADDR)))))
;
;  (:OPTIONS :GUARDS))
;
;(DEFSTRUCTURE V&CVZNX
;  \"An MC68020 value abstraction.\"
;  (V     (:ASSERT (LONGWORD-P V) :REWRITE
;                  (:TYPE-PRESCRIPTION (NATURALP V))))
;  (CVZNX (:ASSERT (CCR-P CVZNX) :REWRITE
;                  (:TYPE-PRESCRIPTION (NATURALP CVZNX))))
;
;  ;;  These options make this nothing more than a typed CONS.
;
;  (:OPTIONS :GUARDS (:REPRESENTATION (V . CVZNX)) (:DO-NOT :TAG)))

;~/
;Syntax:

;DEFSTRUCTURE name [documentation] {slot-and-options}* [option-list]

; option-list ::= (:OPTIONS [[options]])

; options ::= guards-option |
;             verify-guards-option |
;             slot-writers-option |
;             inline-option |
;             mix-option |
;             conc-name-option |
;             set-conc-name-option |
;             keyword-constructor-option |
;             keyword-updater-option |
;             predicate-option |
;             weak-predicate-option |
;             force-option |
;             representation-option |
;             do-not-option |
;             mv-intro-macro-option
;             update-method-option |
;             assertion-lemma-hints-option |
;             predicate-guard-hints-option |
;             prefix-option |
;             {assert-option}*

; slot-and-options ::= slot-name | (slot-name [[slot-options]])

; slot-options ::= default-option |
;                  read-only-option |
;                  {assert-option}*

; default-option ::= :DEFAULT | (:DEFAULT) | (:DEFAULT slot-initform)

; read-only-option ::= :READ-ONLY

; assert-option ::= (:ASSERT assertion {assertion-rule-descriptor}*)

; assertion-rule-descriptor ::= rule-token |
;                               (rule-token corollary [other-rule-forms])

; rule-token ::= NIL | :REWRITE | :LINEAR | :LINEAR-ALIAS |
;                :WELL-FOUNDED-RELATION | :BUILT-IN-CLAUSE |
;                :COMPOUND-RECOGNIZER | :ELIM | :GENERALIZE | :META |
;                :FORWARD-CHAINING | :EQUIVALENCE | :REFINEMENT |
;                :CONGRUENCE | :TYPE-PRESCRIPTION | :DEFINITION | :INDUCTION |
;                :TYPE-SET-INVERTER

; guards-option ::= :GUARDS

; verify-guards-option ::= :VERIFY-GUARDS | (:VERIFY-GUARDS) |
;                          (:VERIFY-GUARDS T) | (:VERIFY-GUARDS NIL)

; slot-writers-option ::= :SLOT-WRITERS

; inline-option ::= :INLINE

; mix-option ::= :MIX

; conc-name-option ::= :CONC-NAME | (:CONC-NAME) | (:CONC-NAME conc-name)

; set-conc-name-option ::= :SET-CONC-NAME | (:SET-CONC-NAME) |
;                          (:SET-CONC-NAME set-conc-name)

; keyword-constructor-option ::= :KEYWORD-CONSTRUCTOR |
;                                (:KEYWORD-CONSTRUCTOR) |
;                                (:KEYWORD-CONSTRUCTOR keyword-constructor)

; keyword-updater-option ::= :KEYWORD-UPDATER | (:KEYWORD-UPDATER) |
;                         (:KEYWORD-UPDATER keyword-updater)

; predicate-option ::=  :PREDICATE | (:PREDICATE) | (:PREDICATE predicate)

; weak-predicate-option ::=  :WEAK-PREDICATE | (:WEAK-PREDICATE) |
;                            (:WEAK-PREDICATE weak-predicate)

; force-option ::= :FORCE

; do-not-option ::= (:DO-NOT [[do-not-options]])

; do-not-options ::= :TAG | :READ-WRITE | :WRITE-WRITE

; representation-option ::= :REPRESENTATION | (:REPRESENTATION) |
;                           (:REPRESENTATION representation)

; representation ::= :LIST | :MV | :DOTTED-LIST | :TREE | template

; mv-intro-macro-option ::=  :MV-INTRO-MACRO |
;                            (:MV-INTRO-MACRO) |
;                            (:MV-INTRO-MACRO mv-intro-macro)

; update-method-option ::= :UPDATE-METHOD | (:UPDATE-METHOD) |
;                          (:UPDATE-METHOD update-method)

; update-method ::= :HEURISTIC | :SET | :COPY

; assertion-lemma-hints-option ::=
;   :ASSERTION-LEMMA-HINTS | (:ASSERTION-LEMMA-HINTS) |
;   (:ASSERTION-LEMMA-HINTS hints)

; predicate-guard-hints-option ::=
;   :PREDICATE-GUARD-HINTS | (:PREDICATE-GUARD-HINTS) |
;   (:PREDICATE-GUARD-HINTS hints)

; prefix-option ::= :PREFIX | (:PREFIX) | (:PREFIX prefix)

;Arguments and Values:

;assertion -- a slots-assertion.

;corollary -- a slots-assertion.

;conc-name -- a string-designator.

;documentation -- a string; not evaluated.

;hints -- an acl2-hints.

;keyword-constructor -- a symbol.

;keyword-updater -- a symbol.

;name -- a symbol.

;mv-intro-macro -- a symbol.

;other-rule-forms -- Some acl2-rule-forms.

;predicate -- a symbol.

;prefix -- a string-designator.

;read-write-lemma -- a symbol.

;set-conc-name -- a string-designator.

;slot-initform -- a form; not evaluated.

;slot-name -- a valid-slot-name.

;tag -- a symbol.

;template -- A slots-template.

;weak-predicate -- a symbol.

;write-write-lemma -- a symbol.

;Definitions:

;acl2-hints -- any form valid as the hints argument of defthm.  See the
;documentation for HINTS in the ACL2 documentation.

;acl2-rule-forms -- Any forms that would be valid in an ACL2 rule-classes
;form, except for the rule class itself, or a corollary and formula.  See the
;documentation for the DEFSTRUCTURE assertion theory in the DEFSTRUCTURE
;document,and the ACL2 documentations for RULE-CLASSES.

;slots-assertion -- DEFSTRUCTURE assertions are covered in the DEFSTRUCTURE
;document.

;slots-template -- A cons tree whose flattened form (by STRUCTURES::FLATTEN) is
;a permutation of the list of slot names of the structure.

;string-designator -- a character, string or symbol, it designates the string
;obtained by (STRING STRING-DESIGNATOR) except that by convention the symbol
;NIL designates the empty string.

;valid-slot-name -- Any symbol valid for use as a formal parameter of a
;function. This is any symbol not in the \"keyword\" package, neither T nor NIL,
;neither beginning nor ending with `*', and not beginning with `&'.  In
;addition, no slot-name may be the same as the structure name, and all
;slot-names must have unique print names, i.e., it is illegal to duplicate
;slot names, and it is illegal to use symbols from different packages that
;have the same print name.

; ~/"
; )

(defxdoc defstructure
  :parents (defstructure)
  :short "Define and characterize a general purpose record structure with typed slots.

The on-line documentation only contains examples and a formal syntax
description. The complete documentation for DEFSTRUCTURE is a report entitled
\"DEFSTRUCTURE for ACL2.\"  This report is distributed with the ACL2 release,
and is also available from the ACL2 home page:

http://www.cs.utexas.edu/users/moore/acl2"
  :long "<p>Examples:</p>

 <p>(DEFSTRUCTURE SHIP X-POSITION Y-POSITION X-VELOCITY Y-VELOCITY MASS)

  (DEFSTRUCTURE MC-STATE
    \"The state of the MC68020.\"
    (STATUS (:ASSERT (SYMBOLP STATUS) :TYPE-PRESCRIPTION))
    (RFILE  (:ASSERT (RFILEP RFILE) :REWRITE))
    (PC     (:ASSERT (LONGWORD-P PC) :REWRITE
                     (:TYPE-PRESCRIPTION (NATURALP PC))))
    (CCR    (:ASSERT (CCR-P CCR) :REWRITE
                     (:TYPE-PRESCRIPTION (NATURALP CCR))))
    (MEM    (:ASSERT (MEMORYP MEM) :REWRITE))

    (:OPTIONS :GUARDS (:CONC-NAME MC-)))

  (DEFSTRUCTURE S&amp;ADDR
    \"An MC68020 effective address abstraction.\"
    (S     (:ASSERT (MC-STATE-P S) :REWRITE))
    (LOC   (:ASSERT (SYMBOLP LOC)  :TYPE-PRESCRIPTION))
    (ADDR  (:ASSERT ((LAMBDA (LOC ADDR)
                       (CASE LOC
                         ((D A) (RN-NUMBERP ADDR))
                         ((M I) (LONGWORD-P ADDR))
                         (OTHERWISE (NULL ADDR))))
                     LOC ADDR)
                    (:REWRITE
                     (IMPLIES
                      (OR (EQUAL LOC 'D) (EQUAL LOC 'A))
                      (RN-NUMBERP ADDR)))
                    (:REWRITE
                     (IMPLIES
                      (OR (EQUAL LOC 'M) (EQUAL LOC 'I))
                      (LONGWORD-P ADDR)))))

    (:OPTIONS :GUARDS))

  (DEFSTRUCTURE V&amp;CVZNX
    \"An MC68020 value abstraction.\"
    (V     (:ASSERT (LONGWORD-P V) :REWRITE
                    (:TYPE-PRESCRIPTION (NATURALP V))))
    (CVZNX (:ASSERT (CCR-P CVZNX) :REWRITE
                    (:TYPE-PRESCRIPTION (NATURALP CVZNX))))

    ;;  These options make this nothing more than a typed CONS.

    (:OPTIONS :GUARDS (:REPRESENTATION (V . CVZNX)) (:DO-NOT :TAG)))</p>

 <p>Syntax:</p>

 <p>DEFSTRUCTURE name [documentation] {slot-and-options}* [option-list]</p>

 <p>option-list ::= (:OPTIONS [[options]])</p>

 <p>options ::= guards-option | verify-guards-option | slot-writers-option |
               inline-option | mix-option | conc-name-option |
               set-conc-name-option | keyword-constructor-option |
               keyword-updater-option | predicate-option |
               weak-predicate-option | force-option | representation-option |
               do-not-option | mv-intro-macro-option update-method-option |
               assertion-lemma-hints-option | predicate-guard-hints-option |
               prefix-option | {assert-option}*</p>

 <p>slot-and-options ::= slot-name | (slot-name [[slot-options]])</p>

 <p>slot-options ::= default-option | read-only-option | {assert-option}*</p>

 <p>default-option ::= :DEFAULT | (:DEFAULT) | (:DEFAULT slot-initform)</p>

 <p>read-only-option ::= :READ-ONLY</p>

 <p>assert-option ::= (:ASSERT assertion {assertion-rule-descriptor}*)</p>

 <p>assertion-rule-descriptor ::= rule-token | (rule-token corollary
                                 [other-rule-forms])</p>

 <p>rule-token ::= NIL | :REWRITE | :LINEAR | :LINEAR-ALIAS |
                  :WELL-FOUNDED-RELATION | :BUILT-IN-CLAUSE |
                  :COMPOUND-RECOGNIZER | :ELIM | :GENERALIZE | :META |
                  :FORWARD-CHAINING | :EQUIVALENCE | :REFINEMENT | :CONGRUENCE
                  | :TYPE-PRESCRIPTION | :DEFINITION | :INDUCTION |
                  :TYPE-SET-INVERTER</p>

 <p>guards-option ::= :GUARDS</p>

 <p>verify-guards-option ::= :VERIFY-GUARDS | (:VERIFY-GUARDS) |
                            (:VERIFY-GUARDS T) | (:VERIFY-GUARDS NIL)</p>

 <p>slot-writers-option ::= :SLOT-WRITERS</p>

 <p>inline-option ::= :INLINE</p>

 <p>mix-option ::= :MIX</p>

 <p>conc-name-option ::= :CONC-NAME | (:CONC-NAME) | (:CONC-NAME conc-name)</p>

 <p>set-conc-name-option ::= :SET-CONC-NAME | (:SET-CONC-NAME) |
                            (:SET-CONC-NAME set-conc-name)</p>

 <p>keyword-constructor-option ::= :KEYWORD-CONSTRUCTOR |
                                  (:KEYWORD-CONSTRUCTOR) |
                                  (:KEYWORD-CONSTRUCTOR
                                  keyword-constructor)</p>

 <p>keyword-updater-option ::= :KEYWORD-UPDATER | (:KEYWORD-UPDATER) |
                           (:KEYWORD-UPDATER keyword-updater)</p>

 <p>predicate-option ::= :PREDICATE | (:PREDICATE) | (:PREDICATE predicate)</p>

 <p>weak-predicate-option ::= :WEAK-PREDICATE | (:WEAK-PREDICATE) |
                              (:WEAK-PREDICATE weak-predicate)</p>

 <p>force-option ::= :FORCE</p>

 <p>do-not-option ::= (:DO-NOT [[do-not-options]])</p>

 <p>do-not-options ::= :TAG | :READ-WRITE | :WRITE-WRITE</p>

 <p>representation-option ::= :REPRESENTATION | (:REPRESENTATION) |
                             (:REPRESENTATION representation)</p>

 <p>representation ::= :LIST | :MV | :DOTTED-LIST | :TREE | template</p>

 <p>mv-intro-macro-option ::= :MV-INTRO-MACRO | (:MV-INTRO-MACRO) |
                              (:MV-INTRO-MACRO mv-intro-macro)</p>

 <p>update-method-option ::= :UPDATE-METHOD | (:UPDATE-METHOD) |
                            (:UPDATE-METHOD update-method)</p>

 <p>update-method ::= :HEURISTIC | :SET | :COPY</p>

 <p>assertion-lemma-hints-option ::= :ASSERTION-LEMMA-HINTS |
     (:ASSERTION-LEMMA-HINTS) | (:ASSERTION-LEMMA-HINTS hints)</p>

 <p>predicate-guard-hints-option ::= :PREDICATE-GUARD-HINTS |
     (:PREDICATE-GUARD-HINTS) | (:PREDICATE-GUARD-HINTS hints)</p>

 <p>prefix-option ::= :PREFIX | (:PREFIX) | (:PREFIX prefix)</p>

 <p>Arguments and Values:</p>

 <p>assertion -- a slots-assertion.</p>

 <p>corollary -- a slots-assertion.</p>

 <p>conc-name -- a string-designator.</p>

 <p>documentation -- a string; not evaluated.</p>

 <p>hints -- an acl2-hints.</p>

 <p>keyword-constructor -- a symbol.</p>

 <p>keyword-updater -- a symbol.</p>

 <p>name -- a symbol.</p>

 <p>mv-intro-macro -- a symbol.</p>

 <p>other-rule-forms -- Some acl2-rule-forms.</p>

 <p>predicate -- a symbol.</p>

 <p>prefix -- a string-designator.</p>

 <p>read-write-lemma -- a symbol.</p>

 <p>set-conc-name -- a string-designator.</p>

 <p>slot-initform -- a form; not evaluated.</p>

 <p>slot-name -- a valid-slot-name.</p>

 <p>tag -- a symbol.</p>

 <p>template -- A slots-template.</p>

 <p>weak-predicate -- a symbol.</p>

 <p>write-write-lemma -- a symbol.</p>

 <p>Definitions:</p>

 <p>acl2-hints -- any form valid as the hints argument of defthm.  See the
 documentation for HINTS in the ACL2 documentation.</p>

 <p>acl2-rule-forms -- Any forms that would be valid in an ACL2 rule-classes
 form, except for the rule class itself, or a corollary and formula.  See the
 documentation for the DEFSTRUCTURE assertion theory in the DEFSTRUCTURE
 document,and the ACL2 documentations for RULE-CLASSES.</p>

 <p>slots-assertion -- DEFSTRUCTURE assertions are covered in the DEFSTRUCTURE
 document.</p>

 <p>slots-template -- A cons tree whose flattened form (by STRUCTURES::FLATTEN)
 is a permutation of the list of slot names of the structure.</p>

 <p>string-designator -- a character, string or symbol, it designates the
 string obtained by (STRING STRING-DESIGNATOR) except that by convention the
 symbol NIL designates the empty string.</p>

 <p>valid-slot-name -- Any symbol valid for use as a formal parameter of a
 function. This is any symbol not in the \"keyword\" package, neither T nor
 NIL, neither beginning nor ending with `*', and not beginning with `&amp;'.
 In addition, no slot-name may be the same as the structure name, and all
 slot-names must have unique print names, i.e., it is illegal to duplicate slot
 names, and it is illegal to use symbols from different packages that have the
 same print name.</p>

 ")


;;;****************************************************************************
;;;
;;;    Importing
;;;
;;;    The definition of DEFSTRUCTURE requires a few select routines from the
;;;    Acl2 system code and the utilities package.  To avoid having to prefix
;;;    these names with the package name everywhere, we define these
;;;    names in the "STRUCTURES" package as macros that expand into identical
;;;    calls of the native things.
;;;
;;;****************************************************************************

;;;  All imports moved to package declaration.

#|
(u::import-as-macros ACL2::A-SYMBOL-UNIQUE-TO-THE-ACL2-PACKAGE)

(u::import-as-macros U::A-SYMBOL-UNIQUE-TO-THE-U-PACKAGE)
|#


;;;****************************************************************************
;;;
;;;    Macros
;;;
;;;****************************************************************************

(defmacro acons-up (&rest forms)
  (cond
   ((null forms) '())
   (t `(ACONS$ ,(caar forms) ,(cadar forms)
               (ACONS-UP ,@(cdr forms))))))

(defmacro bomb-from (where fmt &rest args)
  `(ER HARD ,where ,fmt ,@args))

(defmacro bomb (fmt &rest args)
  `(BOMB-FROM 'DEFSTRUCTURE ,fmt ,@args))

(mutual-recursion

 (defun mlambda-fn-lst (args list)
   (cond
    ((atom list) ())
    (t (cons (mlambda-fn args (car list))
             (mlambda-fn-lst args (cdr list))))))

 (defun mlambda-fn (args form)
   (declare (xargs :guard (symbol-listp args)))
   (cond ((atom form) (cond ((member form args) form)
                            (t (list 'QUOTE form))))
         ((eq (car form) 'QUOTE) (list 'QUOTE form))
         (t (cons 'LIST
                  (cons (list 'QUOTE (car form))
                        (mlambda-fn-lst args (cdr form))))))))

(defmacro mlambda (args form)
  "A macro lambda that doesn't substitute function symbols or quoted
   constants."
  (declare (xargs :guard (symbol-listp args)))
  (mlambda-fn args form))


;;;****************************************************************************
;;;
;;;    Utility Functions
;;;
;;;****************************************************************************

(defun acons$ (key datum value)
  (cons (cons key datum) value))

(defun ncars (n l)
  "The 1st n CARs of l."
  (cond
   ((= n 0) ())
   ((null l) ())
   (t (cons (car l) (ncars (- n 1) (cdr l))))))

(defun fold (args)
  "Folds a list into a somewhat balanced tree."
  (cond
   ((null args) nil)
   ((null (cdr args)) (car args))
   (t (cons (fold (ncars (truncate (length args) 2) args))
            (fold (nthcdr (truncate (length args) 2) args))))))

(defun flatten (args)
  "An `improper' list flattener.  NIL is always flattened away."
  (cond
   ((atom args) (cond
                 ((null args) nil)
                 (t (list args))))
   (t (append (flatten (car args))
              (flatten (cdr args))))))

(defun dotify (l)
  "Make the last CONS of l a `dotted pair' if possible."
  (cond
   ((atom l) l)
   ((atom (cdr l)) l)
   ((atom (cdr (cdr l))) (cond
                          ((null (cdr (cdr l))) (cons (car l) (cadr l)))
                          (t l)))
   (t (cons (car l) (dotify (cdr l))))))

(defun duplicates-equal (lst)
  (cond
   ((atom lst) nil)
   ((member-equal (car lst) (cdr lst))
    (add-to-set-equal (car lst)
                      (duplicates-equal (cdr lst))))
   (t (duplicates-equal (cdr lst)))))

(defun keywordify (string-designator)
  (intern-in-package-of-symbol (string string-designator) :keyword))

(defloop keywordify-list (l)
  (for ((x in l)) (collect (keywordify x))))

(defun keywordify-tree (tree)
  (cond
   ((atom tree)
    (cond
     ((not tree) nil)
     ((not (symbolp tree)) (bomb-from 'KEYWORDIFY-TREE "Bug. ~p0" tree))
     (t (keywordify tree))))
   (t (cons (keywordify-tree (car tree)) (keywordify-tree (cdr tree))))))

(defloop keywordp-listp (l)
  (for ((x in l)) (always (keywordp x))))

(defloop list-all (l)
  (for ((x in l))
    (collect (list x))))

(defloop map-string (l)
  (for ((x in l)) (collect (string x))))

(defloop remove-strings (l)
  (for ((x in l)) (unless (stringp x) (collect x))))

(defun x-or-car-x (x) (if (atom x) x (car x)))

(defloop map-x-or-car-x (l)
  (for ((x in l)) (collect (x-or-car-x x))))

(defun x-or-cadr-x (x)
  (declare (xargs :guard (or (atom x) (and (consp x) (consp (cdr x))))))
  (if (atom x) x (cadr x)))

(defloop map-x-or-cadr-x (l)
  (for ((x in l)) (collect (x-or-cadr-x x))))

(defun designated-string (string-designator)
  (cond
   ((null string-designator) "")
   (t (string string-designator))))

;;;  NB: Acl2 has the advantage of knowning that all terms have been
;;;  translated, which we can't do here do to lack of access to STATE.
;;;  So we define an `assertion' term, along with a free variable finder and a
;;;  substituter for assertion terms.

(defun lambda-function-p (x)
  (and (true-listp x)
       (equal (length x) 3)
       (equal (first x) 'ACL2::LAMBDA)
       (true-listp (second x))))

(mutual-recursion

 (defun assertion-termp (term)
   (cond
    ((atom term) t)
    ((eq (car term) 'QUOTE) t)
    (t (and (or (symbolp (car term))
                (lambda-function-p (car term)))
            (assertion-termp-list (cdr term))))))

 (defun assertion-termp-list (l)
   (cond
    ((atom l) (null l))
    (t (and (assertion-termp (car l))
            (assertion-termp-list (cdr l)))))))

(mutual-recursion

 (defun reason-for-not-assertion-termp (term)
   (cond
    ((atom term) nil)
    ((eq (car term) 'QUOTE) nil)
    (t (if (or (symbolp (car term))
               (lambda-function-p (car term)))
            (reason-for-not-assertion-termp-list (cdr term))
         (msg "the CAR of ~p0 is neither a symbol nor a LAMBDA function."
              term)))))

 (defun reason-for-not-assertion-termp-list (l)
   (cond
    ((atom l) (or (null l)
                  (msg "it contains an `improper' list terminated by the atom ~
                        ~p0." l)))
    (t (or (reason-for-not-assertion-termp (car l))
           (reason-for-not-assertion-termp-list (cdr l)))))))

(mutual-recursion

 (defun free-vars1 (term ans)
   "A free variable is a symbol that is not a constant, i.e., it excludes T,
    NIL, and *CONST* etc."
   (cond
    ((atom term) (if (and (symbolp term)
                          (not (eq (legal-variable-or-constant-namep term)
                                   'CONSTANT)))
                     (add-to-set-eq term ans)
                   ans))
    ((eq (car term) 'QUOTE) ans)
    (t (free-vars1-lst (cdr term) ans))))

 (defun free-vars1-lst (terms ans)
   (cond
    ((atom terms) ans)
    (t (free-vars1-lst (cdr terms) (free-vars1 (car terms) ans))))))

(defun free-vars (term)
  (free-vars1 term '()))

(mutual-recursion

 (defun subst-expr (new old term)
   (cond
    ((equal term old) new)
    ((atom term) term)
    ((eq (car term) 'QUOTE) term)
    (t (cons (car term) (subst-expr-lst new old (cdr term))))))

 (defun subst-expr-lst (new old args)
   (cond
    ((null args) nil)
    (t (cons (subst-expr new old (car args))
             (subst-expr-lst new old (cdr args)))))))

(defun subst-expr-all (term new-list old-list)
  (cond
   ((atom old-list) term)
   (t (subst-expr-all
       (subst-expr (car new-list) (car old-list) term)
       (cdr new-list) (cdr old-list)))))


;;;****************************************************************************
;;;
;;;   Lemmas
;;;
;;;****************************************************************************

(logic)

(defthm open-mv-nth
  (implies
   (syntaxp (and (consp n) (eq (car n) 'QUOTE)))
   (equal (mv-nth n l)
          (if (zp n)
              (car l)
            (mv-nth (1- n) (cdr l)))))
  :hints
  (("Goal" :in-theory (e/d (mv-nth) (ACL2::MV-NTH-TO-VAL)))))

(in-theory (disable open-mv-nth))

(program)


;;;****************************************************************************
;;;
;;;    Data Base
;;;
;;;    We maintain a `data base' of everything we need to know to process the
;;;    DEFSTRUCTURE.  This data base contains user command options, names,
;;;    code fragments, etc.  By convention the data-base is always bound to
;;;    the variable DB, and always appears as the last argument of any
;;;    function that needs it.
;;;
;;;    The data base is an alist, and contains 2 kinds of entries:
;;;
;;;    (<keyword> . <value>) --  A global entry, where <keyword> is a Lisp
;;;                              keyword.
;;;
;;;    ((<slot> . <keyword>) . <value>) -- An entry for a particular slot.
;;;
;;;    The macro DB can be used either as (DB <keyword>) to retrieve the
;;;    first kind of entry, and (DB <slot> <keyword>) to retrieve the second.
;;;    To help catch programming errors we insist that each requested field
;;;    be in the data base, and DB enforces this restriction.
;;;
;;;    The macro DB-LET, e.g., (DB-LET (NAME (slot READER)), expands into a
;;;    LET that binds a variable with the same name as the keyword entry (or
;;;    slot keyword entry for the given slot) to the appropriate entry.
;;;
;;;    Normally keyword entries are put into DB by ACONS or ACONS-DB.
;;;    Slot-keyword entries are often created by mapping the list of slot
;;;    names, and are attached with APPEND or APPEND-DB.  If the entry is the
;;;    name of a function, macro, or lemma, then by convention a missing or
;;;    NULL entry indicates that the function, macro, or lemma will not be
;;;    generated.
;;;
;;;    The following are lists of all possible entries in DB.  Please keep
;;;    them up to date as the code is modified.  These lists are also stored as
;;;    the constants *DB-FIELDS* and *DB-SLOT-FIELDS*. The phrase "user option"
;;;    below means that this is a keyword option specified by the user either
;;;    for the DEFSTRUCTURE as a whole or for a particular slot, and its
;;;    meaning can be gleaned from the user documentation.
;;;
;;;    Keyword Entries, accessed by (DB <keyword>) :
;;;
;;;    :ACL2-COUNT-LEMMA -- The lemma describing the ACL2-COUNT of the
;;;                         structure.
;;;    :ASSERTIONS -- A list of ASSERTION records recording each assertion
;;;                   about the structure.
;;;    :ASSERTION-LEMMA -- The lemma capturing all assertions about the
;;;      structure.
;;;    :ASSERTION-LEMMA-HINTS -- User option.
;;;    :CONC-NAME -- User option.
;;;    :CONSTRUCTOR-CALL -- A symbolic call of the constructor.
;;;    :DEFINITION-THEORY -- The theory of runes associated with the functions
;;;      defined by the structure that will remain DISABLEd by default.
;;;    :DOC -- The documentation string for the structure, or NIL.
;;;    :ELIMINATION-LEMMA -- The :ELIM lemma for the constructor.
;;;    :FORCE -- Boolean; true to force hypotheses.
;;;    :GUARDS -- User option.
;;;    :INLINE -- User option.
;;;    :MIX    -- User option. ;; DAG -- new option
;;;    :KEYWORD-CONSTRUCTOR -- User option.
;;;    :KEYWORD-SLOT-NAMES -- Slot names mapped to equivalent keyword symbols.
;;;    :KEYWORD-UPDATER -- User option.
;;;    :LIFT-IF-LEMMA -- The name of a lemma that `lifts' IFs through
;;;                      accessor references.
;;;    :LEMMA-THEORY -- The theory of all lemmas created by this DEFSTRUCTURE.
;;;    :MV-INTRO-MACRO -- The name of a macro that generates a lemma that
;;;                       `introduces' MV constructors.
;;;    :NAME -- The structure name.
#|
;;;    :NORMALIZATION-LEMMA -- The lemma the normalizes symbolic writer calls
;;;      to a constructor call.
;;;    :NORMALIZE -- Boolean; true to generate NORMALIZATION-LEMMA (default).
|#
;;;    :PREDICATE -- User option.
;;;    :PREDICATE-CALL -- A symbolic call of the predicate.
;;;    :PREDICATE-CONSTRUCTOR-LEMMA -- A lemma that show that how to satisfy
;;;      the predicate given an explicit instance of the constructor.
;;;    :PREDICATE-GUARD-HINTS -- User option.
;;;    :PREDICATE-SLOT-WRITERS-LEMMA -- The lemma that shows when the
;;;      slot-writers satisfy the predicate.
;;;    :PREDICATE-WEAK-PREDICATE-LEMMA -- A lemma that shows that the
;;;      predicate includes the weak predicate.
;;;    :PREFIX -- User option.
;;;    :READ-LEMMA -- A lemma that simplifies reading an explicit constructor.
;;;    :READ-ONLY -- Derived from :SLOT-WRITERS option.
;;;    :READ-WRITE -- Boolean; true to generate READ-WRITE-LEMMA (default).
;;;    :READ-WRITE-LEMMA -- The READ-WRITE lemma.
;;;    :REPRESENTATION -- User option.
;;;    :REQUIRED-SLOT-NAMES -- The slot names for which no :DEFAULT slot
;;;                            option was specified; required on every call
;;;                            of the keyword-constructor.
;;;    :SET-CONC-NAME -- User option.
;;;    :SLOT-NAMES -- List of slot names in the user-defined order.
;;;    :TAG -- Either the structure name or NIL.
;;;    :TEMPLATE -- A representation of the structure (including the optional
;;;       :TAG) used to create the access/update forms.
;;;    :UPDATE-METHOD -- User option.
;;;    :VALUE-VARIABLE -- A variable which is not one of the slot names of the
;;;       structure name, used as the symbolic variable in terms involving
;;;       the slot writers.
;;;    :VALUE-VARIABLE1 -- Another unique variable.
;;;    :VERIFY-GUARDS -- User option -- T, NIL, or :DEFAULT.
;;;    :WEAK-PREDICATE -- The name of the `weak' predicate on the structure.
;;;    :WEAK-PREDICATE-CALL -- A symbolic call of the weak predicate .
;;;    :WEAK-PREDICATE-CONSTRUCTOR-LEMMA -- The lemma that shows when the
;;;      constructor satisfies the weak predicate.
;;;    :WEAK-PREDICATE-SLOT-WRITERS-LEMMA -- The lemma that shows when the
;;;      slot-writers satisfy the weak predicate.
;;;    :WRITE-LEMMA -- A lemma that simplifies writes to an explicit
;;;      constructor.
;;;    :WRITE-WRITE -- Boolean; true to generate WRITE-WRITE-LEMMA (default).
;;;    :WRITE-WRITE-LEMMA -- A lemma that normalizes multiple writes to a
;;;      structure.
;;;
;;;    Slot/Keyword entries, accessed by (DB <slot> <keyword>):
;;;
;;;    :ASSERTIONS -- A list of ASSERTION records recording each assertion
;;;                   about the slot.
;;;    :DEFAULT -- User option.
;;;    :DEFAULT-SPECIFIED -- Indicates if the user entered a :DEFAULT option
;;;                          for the slot.
;;;    :READER -- The reader function for the slot.
;;;    :READER-CALL -- A symbolic call of the reader for the slot.
;;;    :READ-ONLY -- User option.
;;;    :WRITER -- The writer function for the slot.
;;;    :WRITER-CALL -- A symbolic call of the writer for the slot.

(defconst *db-fields*
  '(:ACL2-COUNT-LEMMA
    :ASSERTIONS :ASSERTION-LEMMA :ASSERTION-LEMMA-HINTS
    :CONC-NAME :CONSTRUCTOR-CALL :DEFINITION-THEORY :DOC
    :ELIMINATION-LEMMA :FORCE :GUARDS :INLINE :MIX
    :INTRO-MACRO
    :KEYWORD-CONSTRUCTOR
    :KEYWORD-SLOT-NAMES
    :KEYWORD-UPDATER :LEMMA-THEORY :LIFT-IF-LEMMA :MV-INTRO-MACRO
    :NAME #|:NORMALIZATION-LEMMA :NORMALIZE|# :PREDICATE
    :PREDICATE-CALL
    :PREDICATE-CONSTRUCTOR-LEMMA :PREDICATE-SLOT-WRITERS-LEMMA
    :PREDICATE-GUARD-HINTS
    :PREDICATE-WEAK-PREDICATE-LEMMA
    :PREFIX :READ-LEMMA :READ-ONLY
    :READ-WRITE :READ-WRITE-LEMMA
    :REPRESENTATION
    :REQUIRED-SLOT-NAMES
    :SET-CONC-NAME :SLOT-NAMES
    :TAG :TEMPLATE :UPDATE-METHOD :VALUE-VARIABLE :VALUE-VARIABLE1
    :VERIFY-GUARDS
    :WEAK-PREDICATE :WEAK-PREDICATE-CALL
    :WEAK-PREDICATE-CONSTRUCTOR-LEMMA :WEAK-PREDICATE-SLOT-WRITERS-LEMMA
    :WRITE-LEMMA
    :WRITE-WRITE :WRITE-WRITE-LEMMA))

(defconst *db-slot-fields*
  '(:ASSERTIONS
    :DEFAULT :DEFAULT-SPECIFIED :READER :READER-CALL :READ-ONLY
    :WRITER :WRITER-CALL))

(defconst *function-names*
  `(:NAME :PREDICATE :WEAK-PREDICATE))

(defconst *slot-function-names*
  '(:READER :WRITER))

(defconst *macro-names*
  '(:KEYWORD-CONSTRUCTOR :KEYWORD-UPDATER))

(defconst *lemma-names*
  '(:ACL2-COUNT-LEMMA
    :ASSERTION-LEMMA
    :ELIMINATION-LEMMA :LIFT-IF-LEMMA #|:NORMALIZATION-LEMMA|#
    :PREDICATE-CONSTRUCTOR-LEMMA :PREDICATE-SLOT-WRITERS-LEMMA
    :PREDICATE-WEAK-PREDICATE-LEMMA :READ-LEMMA :READ-WRITE-LEMMA
    :WEAK-PREDICATE-CONSTRUCTOR-LEMMA :WEAK-PREDICATE-SLOT-WRITERS-LEMMA
    :WRITE-LEMMA :WRITE-WRITE-LEMMA))

(defun db-fn (key form db)
  (let
    ((pair (assoc key db)))
    (cond
     (pair (cdr pair))
     (t (bomb-from 'DB-FN "Key not present at runtime: ~p0." form)))))

(defun db-slot-fn (slot key form db)
  (let
    ((pair (assoc-equal (cons slot key) db)))
    (cond
     (pair (cdr pair))
     (t (bomb-from 'DB-SLOT-FN "Key not present at runtime: ~p0." form)))))

(defmacro db (&whole form &rest args)
  (case (length args)
    (1 (cond
        ((not (member (car args) *DB-FIELDS*))
         (bomb-from 'DB "Unrecognized field: ~p0" form))
        (t `(DB-FN ,(car args) ',form DB))))
    (2 (cond
        ((not (member (cadr args) *DB-SLOT-FIELDS*))
         (bomb-from 'DB "Unrecognized slot field: ~p0" form))
        (t `(DB-SLOT-FN ,(car args) ,(cadr args) ',form DB))))
    (t (bomb-from "DB coded with wrong # of args: ~p0" form))))

(defmacro acons-db (&rest forms)
  "Acons up a list of (<keyword> <value>) pairs, evaluting each successive
   form in the context of the new DB."
  (cond
   ((null forms) 'DB)
   (t (cond
       ((not (member (caar forms) *DB-FIELDS*))
        (bomb-from 'ACONS-DB "Unrecognized field: ~p0" (caar forms)))
       (t `(LET ((DB (ACONS$ ,(caar forms) ,(cadar forms) DB)))
             (ACONS-DB ,@(cdr forms))))))))

(defmacro append-db (&rest forms)
  "APPEND new sublists to DB, evaluting each sucessive form in the context of
   the new DB."
  (cond
   ((null forms) 'DB)
   (t `(LET ((DB (APPEND ,(car forms) DB)))
         (APPEND-DB ,@(cdr forms))))))

(defmacro extend-db (&rest forms)
  "Evaluate each form in the context of the DB that successive forms
   created."
  (cond
   ((null forms) 'DB)
   (t `(LET ((DB ,(car forms)))
         (EXTEND-DB ,@(cdr forms))))))

(defloop db-let-fn (fields)
  (for ((field in fields))
    (collect
     (cond
      ((symbolp field) `(,field (DB ,(keywordify field))))
      ((and (consp field) (consp (cdr field)) (symbolp (cadr field)))
       `(,(cadr field) (DB ,(car field) ,(keywordify (cadr field)))))
      (t (bomb-from 'DB-LET-FN "Illegal field: ~p0" field))))))

(defmacro db-let (fields &rest forms)
  "This macro is a shorthand way to bind fields of the DB to the like-named
   variable.  A field can be a field name, or (slot field)."
  `(LET ,(db-let-fn fields) ,@forms))

(defloop map-slots-db (slot-names key db)
  "Return a list in SLOT order of the indicated key."
  (for ((slot in slot-names))
    (collect (db-slot-fn slot key `(MAP-SLOTS-DB ON ,slot ,key) db))))

(defloop map-if-slots-db (slot-names key db)
  "Return a list in SLOT order of the indicated key if non-NIL."
  (for ((slot in slot-names))
    (append
     (let ((val (db-slot-fn slot key `(MAP-IF-SLOTS-DB ON ,slot ,key) db)))
       (if val (list val) nil)))))


;;;****************************************************************************
;;;
;;;    Code Generation
;;;
;;;****************************************************************************
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Records
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;;  An ASSERTION record records the assertion as provided by the user, the
;;  slots bound by the assertion, the substituted assertion, the slot that
;;  this assertion is associated with (or NIL if a DEFSTRUCTURE assertion),
;;  and a list of RULE records.

(defrec assertion (assertion bound-slots subst-assertion slot rules) nil)

;;  A RULE record contains an ASSERTION record and the ACL2 :RULE-CLASS form
;;  that will implement the rule.

(defrec rule (assertion rule-class) nil)

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Utilities, and MAKE-ers.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defloop required-slot-names (slot-names db)
  "A slot is required by the constructor macro if no default was specified."
  (for ((slot in slot-names))
    (unless (db slot :DEFAULT-SPECIFIED)
      (collect (keywordify slot)))))

(defun make-corollary (assertion db)
  "Create the :COROLLARY rule for the assertion."
  (let*
    ((force (db :FORCE))
     (predicate-call (db :PREDICATE-CALL))
     (hyp (if force `(FORCE ,predicate-call) predicate-call)))
    `(IMPLIES ,hyp ,(access ASSERTION assertion :SUBST-ASSERTION))))

(defmacro make-prefix-name (&rest names)
  `(PACK-INTERN (DB :NAME) (DB :PREFIX) ,@names))

(defun make-template (db)

  "Using the :SLOT-NAMES, :REPRESENTATION, and :TAG, make a template for
   function generation.  If the structure is tagged, the tag is always added
   as the CAR.  We know that the :TAG is a symbol, and that the
   :REPRSENTATION is of the proper form."

  (db-let (representation slot-names tag)

    ;;  Preliminary template.

    (let ((template
           (case representation
             ((:MV :LIST) slot-names)
             (:DOTTED-LIST (dotify slot-names))
             (:TREE (fold slot-names))
             (t representation))))

      ;;  The final template.

      (if tag (cons tag template) template))))

(defloop reader-names (slot-names db)
  (for ((slot in slot-names))
    (collect
     (db-let (name conc-name)
       (cons (cons slot :READER)
             (pack-intern name conc-name slot))))))

(defloop writer-names (slot-names db)
  "Generate the writer name, setting to NIL if either the slot or the
   structure as a whole is :READ-ONLY."
  (for ((slot in slot-names))
    (collect
     (db-let (name set-conc-name (slot read-only))
       (cons (cons slot :WRITER)
             (if (or read-only (db :READ-ONLY))
                 nil
               (pack-intern name set-conc-name slot)))))))

(defloop reader-calls (slot-names db)
  "Create a symbolic access form for a slot.  The default access form for
  slot A of structure FOO looks like (FOO-A FOO)."
  (for ((slot in slot-names))
    (collect
     (db-let (name)
       (cons (cons slot :READER-CALL)
             `(,(db slot :READER) ,name))))))

(defloop writer-calls (slot-names db)
  "Create a symbolic update form for a slot.  The default update form for
  slot A of structure FOO with slots A, B, and C looks like
  (SET-FOO-A FOOABC FOO)."
  (for ((slot in slot-names))
    (collect
     (db-let (name value-variable (slot writer))
       (cons (cons slot :WRITER-CALL)
             (if writer
                 `(,writer ,value-variable ,name)
               nil))))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Macro, Function, and Lemma generators.
;;;
;;;    By convention all of these return a list of forms to be spliced into
;;;    the set of events.  They contain comment strings that will be removed
;;;    by the CAPSULE macro.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun guard-declaration (guard verifyp db)

  "If :GUARDS was specified, declare a guard and verify based on
  :VERIFY-GUARDS.  Note that the default is :DEFAULT."

  (db-let (guards verify-guards)

    (if guards
        (list
         `(DECLARE (XARGS :GUARD ,guard
                          ,@(cond
                             ((or (null verifyp) (null verify-guards))
                              '(:VERIFY-GUARDS NIL))
                             ((eq verify-guards t) '(:VERIFY-GUARDS T))))))
      nil)))


;;;  EXTENSIONALITY

#|

;; these functions were moved to symbol-fns

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defmacro join-symbols (witness &rest rst)
  `(intern-in-package-of-symbol (symbol-list-to-string (list ,@rst))
                                ,witness))

(defun make-numbered-symbol (witness symbol number)
  (intern-in-package-of-symbol (concatenate 'acl2::string
                                     (symbol-name symbol)
                                     (coerce (explode-nonnegative-integer number nil) 'acl2::string))
                        witness))

(defun number-symbol-list (witness list number)
  (if (consp list)
      (cons (make-numbered-symbol witness (car list) number)
            (number-symbol-list witness (cdr list) number))
    nil))

(defun enkey (symbol)
  (declare (type t symbol))
  (if (symbolp symbol)
      (intern-in-package-of-symbol (symbol-name symbol) :)
    :nil))

(defun enkey-field-names (list)
  (declare (type t list))
  (if (consp list)
      (cons (enkey (car list))
            (enkey-field-names (cdr list)))
    nil))

|#

(defun existential-fields (f f1 f2)
  (if (and (consp f)
           (consp f1)
           (consp f2))
      (cons `(cpath::tag-location ,(enkey (car f)) (equal ,(car f1) ,(car f2)))
            (existential-fields (cdr f) (cdr f1) (cdr f2)))
    nil))

(defun strong-existential-fields (fn f x y)
  (if (consp f)
      (cons `(cpath::tag-location ,(enkey (car f)) (equal (,@fn ,(car f) ,x)
                                                   (,@fn ,(car f) ,y)))
            (strong-existential-fields fn (cdr f) x y))
    nil))

(defun enlist (list)
  (declare (type t list))
  (if (consp list)
      (cons (list (car list))
            (enlist (cdr list)))
    nil))

(defloop field-readers (slot-names db)
  (for ((slot in slot-names))
       (collect
        (db-let (name conc-name)
                (pack-intern name conc-name slot)))))

(defun extensionality (db)

  (db-let (name inline slot-names keyword-slot-names mix weak-predicate)

    (let ((paths  (psort (enlist keyword-slot-names)))
          (fields (field-readers slot-names db)))
      (let ((field1 (number-symbol-list name fields 1))
            (field2 (number-symbol-list name fields 2)))

        (cons

       "
;  The extensionality theorems decompose equality of two structures into
;; equality of their respective fields.
 "

        `(

          ;; How expensive is this rule??

          (defthm ,(join-symbols name name '-extensionality! (if mix '|| '-helper))
            (implies
             (and
              (,weak-predicate x)
              (,weak-predicate y))
             (iff
              (equal x y)
              (equal (gp-list '(,@paths) x)
                     (gp-list '(,@paths) y)))))

          ,@(if mix nil
              `((defthm ,(join-symbols name name '-extensionality!)
                  (implies
                   (and
                    (,weak-predicate x)
                    (,weak-predicate y))
                   (iff
                    (equal x y)
                    (and ,@(strong-existential-fields nil fields `x `y)))))
                ; :hints (("goal" :in-theory (disable cpath::sp==r))))

                (in-theory (disable ,(join-symbols name name '-extensionality! '-helper)))))

          ,@(if inline nil
              `(
                (defthm ,(join-symbols name name '-extensionality)
                  (iff
                   (equal (,name ,@field1)
                          (,name ,@field2))
                   (and
                    ,@(existential-fields fields field1 field2)
                    ))
                  :hints (("goal" :in-theory (disable ,weak-predicate ,name))))

                (in-theory (disable ,(join-symbols name name '-extensionality!)))
                ))

          )

         )))))

;;;  CONSTRUCTOR




(defun constructor-body (slot-names keyword-slot-names)
  (if (consp slot-names)
      `(sp (list ,(car keyword-slot-names)) ,(car slot-names)
          ,(constructor-body (cdr slot-names) (cdr keyword-slot-names)))
    'nil))


(defun template-cost (template)
  (cond
   ((atom template) 0)
   (t (+ 1 (template-cost (car template)) (template-cost (cdr template))))))

(defloop acl2-countify-slots (slots)
  (for ((slot in slots))
    (collect `(ACL2-COUNT ,slot))))

(defun constructor (db)

  "If :REPRESENTATION is :MV, create an MV macro.  Else create a
   function or macro under control of the :INLINE option.  For tagged
   structures the tag is in the constructor-body as a free variable, so
   we need to bind it."

  (db-let (name acl2-count-lemma constructor-call slot-names representation
                tag doc template inline keyword-slot-names)

    (cond
     ((eq representation :MV)
      (list
       "
;  The constructor is defined as a macro that expands into an MV form for
;  every slot.
 "
       `(DEFMACRO ,name ,slot-names ,@(if doc (list doc) nil)
          (CONS 'MV (LIST ,@slot-names)))))

     (inline
      (list
       "
;  The constructor is defined as a macro that accepts every slot.
 "
       `(DEFMACRO ,name ,slot-names ,@(if doc (list doc) nil)
          (MLAMBDA ,slot-names ,(constructor-body slot-names keyword-slot-names)))))

     (t (list
         "
;  The constructor is defined as a function that accepts every slot.
 "
         (if tag
             `(DEFUN ,name ,slot-names ,@(if doc (list doc) nil)
                ,@(guard-declaration T t db)
; perhaps the TAG argument doesn't make sense if we're using records?
                ,(constructor-body slot-names keyword-slot-names))
           `(DEFUN ,name ,slot-names ,@(if doc (list doc) nil)
              ,@(guard-declaration T t db)
              ,(constructor-body slot-names keyword-slot-names)))

         )))))

;;;  WEAK-PREDICATE

#| old:
(defun weak-predicate-body (template tree)
  "Traverse the template, creating CONSP and NULL expressions wherever
   needed.  It is necessary for the read/write lemmas that if the template
   contains a NULL entry, that entry must be NULL in every shell.  This
   is initialized with tree = <structure-name> which is the formal parameter
   of the weak predicate."
  (cond
   ((atom template) (cond ((null template) (list `(NULL ,tree)))))
   (t (append (list `(CONSP ,tree))
              (weak-predicate-body (car template) `(CAR ,tree))
              (weak-predicate-body (cdr template) `(CDR ,tree))))))
|#

(defun weak-predicate-body-aux (keyword-slot-names)
  (if (consp keyword-slot-names)
      `(cons (list ,(car keyword-slot-names))
             ,(weak-predicate-body-aux (cdr keyword-slot-names)))
    'nil))

;We changed the weak predicate when we made the conversion to use
;records.  This is kind of gross, but we made it exactly what we
;needed to prove the elim rule.

(defun weak-predicate-body (keyword-slot-names structure-name)
  `(and (wfr ,structure-name)
        (equal (cpath::clrp-list ,(weak-predicate-body-aux keyword-slot-names)
                                ,structure-name)
               nil)))

(defun reader-body (slot template tree)
  "Write a call to G to get slot from a structure."
  (declare (xargs :guard (symbolp slot)) (ignore template))
  `(gp (list ,(keywordify slot)) ,tree))

(defun weak-predicate (db)

  "This is the predicate on the `structure' of the structure. If the
   structure is named, then we include a test that the CAR of the structure
   is the correct name.  We also write a lemma that shows when the
   constructor function satisfies this predicate."

  (db-let (weak-predicate weak-predicate-constructor-lemma
                          constructor-call name template tag
                          inline
                          keyword-slot-names)

    ;;  Note that an untagged, 0-slot structure is defined to be NIL, and an
    ;;  untagged 1-slot structure is a single object.

    (let* ((wp-body (weak-predicate-body keyword-slot-names name))
           (body (cond
                  ((null template) (list `(NULL ,name)))
                  ((atom template) (list `(DECLARE (IGNORE ,name)) T))
                  (tag (list `(AND ,@wp-body (EQ (CAR ,name) ',tag))))
                  (t (list `(AND ,@wp-body))))))
      (list*
       "
;  This predicate defines the `structure' of the structure, and is used as a
;  weak guard on the readers and writers (if defined).
 "

       `(DEFUN ,weak-predicate (,name)
          ,@(guard-declaration T t db)

          ,wp-body ;(or t ,name) ;we only mention name to prevent an error about it being irrelevant but not declared so
          )

       (if inline
           nil
         (list

          "
;  The weak-predicate is satisfied by any explicit reference of the
;  constructor.  We also store this information as a :BUILT-IN-CLAUSE
 "
          `(DEFTHM ,weak-predicate-constructor-lemma
             (EQUAL (,weak-predicate ,constructor-call)
                    T)
             :RULE-CLASSES
             ((:REWRITE)
              (:BUILT-IN-CLAUSE
               :COROLLARY
               (,weak-predicate ,constructor-call))))))))))

;;;  PREDICATE

(defloop map-access-assertion-assertion (assertions)
  (for ((assertion in assertions))
    (collect (access ASSERTION assertion :ASSERTION))))

(defloop slot-assertions (slot-names db)
  (for ((slot in slot-names))
    (append (db-let ((slot assertions))
              (map-access-assertion-assertion assertions)))))

(defloop map-access-assertion-subst-assertion (assertions)
  (for ((assertion in assertions))
    (collect (access ASSERTION assertion :SUBST-ASSERTION))))

(defloop slot-subst-assertions (slot-names db)
  (for ((slot in slot-names))
    (append (db-let ((slot assertions))
              (map-access-assertion-subst-assertion assertions)))))

(defun predicate-body (db)
  "The predicate body is a conjunction of the weak predicate, and all
   assertions about the slots."

  (db-let (weak-predicate weak-predicate-call slot-names assertions)
    `(AND ,weak-predicate-call
          ,@(remove-duplicates-equal
             (append (slot-subst-assertions slot-names db)
                     (map-access-assertion-subst-assertion assertions)))
          T)))

(defun predicate-assertions-explicit (db)

  "The predicate, as the set of assertions for explicit instances of the
   constructor."

  (db-let (slot-names assertions weak-predicate constructor-call)
    (let ((assertions
           (remove-duplicates-equal
            (append (slot-assertions slot-names db)
                    (map-access-assertion-assertion assertions)))))

      ;;  Trying not to introduce redundant conjuncts.

      (cond
       (assertions `(AND ,@assertions T))
       (t 'T)))))

(defun predicate (db)
  (db-let (predicate name predicate-call weak-predicate weak-predicate-call
                     constructor-call predicate-weak-predicate-lemma
                     predicate-constructor-lemma inline)

    (list*
     "
;  This is the predicate, which contains the weak predicate and every
;  assertion made about the slots of the structure.  The final T guarantees
;  that all DEFSTRUCTURE predicates are Boolean.
 "
     `(DEFUN ,predicate (,name)
        ,@(guard-declaration T nil db)
        ,(predicate-body db))


     (if inline
         nil

       ;;  At times it is excessive to require that we prove the entire type
       ;;  predicate for a structure just to show that the weak predicate is
       ;;  satisfied, but this is the most generally useful rule to have
       ;;  around.

       (list
        "
;  This lemma shows that the predicate includes the weak predicate, as
;  :REWRITE, :FORWARD-CHAINING, and :BUILT-IN-CLAUSE rules.  Note that the
;  :REWRITE rule is sometimes implicated in thrashing in conjunction with the
;  normalization lemmas.
 "
        `(DEFTHM ,predicate-weak-predicate-lemma
           (IMPLIES
            ,predicate-call
            ,weak-predicate-call)
           :RULE-CLASSES (:FORWARD-CHAINING :REWRITE :BUILT-IN-CLAUSE))

        "
;  This lemma rewrites the predicate on an explicit reference of
;  the constructor.
 "
        `(DEFTHM ,predicate-constructor-lemma
           (EQUAL (,predicate ,constructor-call)
                  ,(predicate-assertions-explicit db))))))))

;;;  KEYWORD-CONSTRUCTOR
;;;
;;;  The function KEYWORD-CONSTRUCTOR-FN is not a code generator per se, but
;;;  is a helper function for all keyword constructors defined by
;;;  DEFSTRUCTURE.  I had thought about generating a unique helper for each
;;;  structure, thinking that it would be possible to eliminate the
;;;  dependency on the STRUCTURES package.  However, I now realize that at
;;;  present any book that does a DEFSTRUCTURE will have to have a non-local
;;;  INCLUDE-BOOK for this book.  Therefore, all keyword constructors share
;;;  the same helper.  The same goes for KEYWORD-UPDATER.

(defloop default-alist (slot-names db)
  (for ((slot in slot-names))
    (collect (cons (keywordify slot) (db slot :DEFAULT)))))

(defloop keyword-constructor-body (args keyword-slot-names default-alist)
  (for ((keyword-slot in keyword-slot-names))
    (collect
     (let ((tail (assoc-keyword keyword-slot args)))
       (if tail (cadr tail) (cdr (assoc keyword-slot default-alist)))))))

(defun keyword-slot-checker (macro-name form args keyword-slot-names)
  "Check keyword argument list for basic syntax and either bomb or return
   NIL."
  (cond
   ((not (keyword-value-listp args))
    (bomb-from macro-name
               "The argument list in the macro invocation ~p0 ~
                does not match the syntax of a keyword argument ~
                list because ~@1."
               form (reason-for-non-keyword-value-listp args)))
   ((not (subsetp (evens args) keyword-slot-names))
    (bomb-from macro-name
               "The argument list in the macro invocation ~p0 is not ~
                 a valid keyword argument list because it contains the ~
                 ~#1~[keyword~/keywords~] ~&1, which ~#1~[is~/are~] ~
                 not the keyword ~#1~[form~/forms~] of any of the ~
                 slot names ~&2."
               FORM (set-difference-equal (evens args) keyword-slot-names)
               keyword-slot-names))
   (t nil)))


(defun keyword-constructor-fn (form args name keyword-constructor default-alist
                                    keyword-slot-names required-slot-names)
  (cond
   ((keyword-slot-checker keyword-constructor form args keyword-slot-names))
   ((not (subsetp required-slot-names (evens args)))
    (bomb-from keyword-constructor
               "The argument list in the macro invocation ~p0 is not ~
                 valid does not specify a value for the required ~
                 ~#1~[keyword~/keywords~] ~&1. ~
                 Any slot which has no :DEFAULT option at ~
                 DEFSTRUCTURE time must be specified in every ~
                 invocation of the constructor macro."
               form (set-difference-equal
                     required-slot-names (evens args))
               keyword-slot-names))
   (t `(,name ,@(keyword-constructor-body
                 args keyword-slot-names default-alist)))))

(defun keyword-constructor (db)
  (db-let
   (name keyword-constructor slot-names keyword-slot-names
         required-slot-names)

   (if keyword-constructor
       (list
        "
;  This is the keyword constructor macro.  It will expand into a call of the
;  constructor, with appropriate defaulting.
 "
        `(DEFMACRO ,keyword-constructor (&WHOLE FORM &REST ARGS)
           (KEYWORD-CONSTRUCTOR-FN
            FORM ARGS ',name ',keyword-constructor
            ',(default-alist slot-names db)
            ',keyword-slot-names ',required-slot-names)))
     nil)))

;;;  READERS

(defloop reader-definitions (slot-names db)
  (for ((slot in slot-names))
    (collect
     (db-let ((slot reader) name weak-predicate-call template inline mix)
       (if (or mix inline)
           `(DEFMACRO ,reader (,name)
              (MLAMBDA (,name) ,(reader-body slot template name)))
         `(DEFUN ,reader (,name)
            (DECLARE (XARGS :GUARD T));,@(guard-declaration weak-predicate-call t db)
            ,(reader-body slot template name)))))))

(defloop acl2-count-lemma-claims (slot-names db)
  (for ((slot in slot-names))
       (collect
        (db-let ((slot reader) name weak-predicate-call template inline)
                `(and
                  (<= (ACL2-COUNT (,reader ,name)) (ACL2-COUNT ,name))
                  (implies
                   (and
                    ,weak-predicate-call
                    (,reader ,name))
                   (< (ACL2-COUNT (,reader ,name)) (ACL2-COUNT ,name))))))))

(defun readers (db)
  "Define the reader functions"
  (db-let (slot-names acl2-count-lemma)
    (if slot-names
        (append
         (cons
         "
;  These are the `readers' for the structure.
 "
         (reader-definitions slot-names db))

         (and acl2-count-lemma
             (list
              "
;  This lemma justifies recursion on any slot of the structure.  It is
;  unlikely to be used unless the structure is itself recursive.
  "

;This is a different lemma that what we had before the conversion to
;records.  Now it mentions the readers, so it was moved to after the
;readers are defined.

          `(DEFTHM ,acl2-count-lemma

             (AND ,@(acl2-count-lemma-claims slot-names db))
             :rule-classes (:rewrite :linear))


          #|
          `(DEFTHM ,acl2-count-lemma
          (EQUAL (ACL2-COUNT ,constructor-call)
          (+ ,(template-cost template)
          ,@(acl2-countify-slots slot-names))))
          |#
          )))
      nil)))


;;;  WRITERS

(defconst *binding-variable* '|x|)
(defconst *binding-variable1* '|y|)

(defun writer-body (slot template var tree)
  "Write a CONS form to put a new slot into a structure, given the slot,
   the structure template, a variable name (a formal parameter) and the
   `tree'."
  (declare (xargs :guard (symbolp slot)))
  (cond
   ((atom template) (cond ((eq slot template) var)))
   (t (let
        ((car-side (writer-body slot (car template) var `(CAR ,tree)))
         (cdr-side (writer-body slot (cdr template) var `(CDR ,tree))))
        (cond
         (car-side `(CONS ,car-side ,(cond
                                      ((null (cdr template)) nil)
                                      (t `(CDR ,tree)))))
         (cdr-side `(CONS (CAR ,tree) ,cdr-side)))))))

(defun writer-macro-fn (bind slot template value name)
  (if bind
      `(LET ((,*binding-variable*
              (CHECK-VARS-NOT-FREE (,*binding-variable*) ,name)))
         ,(writer-body slot template value *binding-variable*))
    (writer-body slot template value name)))

(defloop writer-definitions (slot-names keyword-slot-names db)
  (for ((slot in slot-names)
        (key  in keyword-slot-names))
    (append
     (db-let ((slot writer) name weak-predicate-call template
              value-variable inline mix)
       (if writer
           (if (or mix inline)
               (list
                `(DEFMACRO ,writer (,value-variable ,name)
                   (MLAMBDA (,value-variable ,name)
                            (sp (list ,key) ,value-variable ,name))))
             (list
              `(DEFUN ,writer (,value-variable ,name)
                 ,@(guard-declaration weak-predicate-call t db)
                 (sp (list ,key) ,value-variable ,name))))
         nil)))))

(defun writers (db)
  "Define the writer functions."
  (db-let (slot-names keyword-slot-names read-only)
    (if read-only
        nil
      (cons
       "
;  These are the `writers' for the structure.
 "
       (writer-definitions slot-names keyword-slot-names db)))))


;;;  KEYWORD-UPDATER

(defloop keyword-writer-map (slot-names db)
  (for ((slot in slot-names))
    (collect (db-let ((slot writer))
               (cons (keywordify slot) writer)))))

(defloop keyword-reader-map (slot-names db)
  (for ((slot in slot-names))
    (collect (db-let ((slot reader))
               (cons (keywordify slot) reader)))))

(defloop read-only-keyword-slots (slot-names db)
  (for ((slot in slot-names))
    (when (db slot :READ-ONLY)
      (collect (keywordify slot)))))

(defun slot-cost (slot template accum)
  "Compute the cost of reading (CAR/CDR) and writing (CONS) a slot."
  (cond
   ((atom template) (cond
                     ((eq slot template) accum)
                     (t nil)))
   (t (or (slot-cost slot (car template) (1+ accum))
          (slot-cost slot (cdr template) (1+ accum))))))

(defun set-cost (slots template)
  (cond
   ((atom slots) 0)
   (t (+ (slot-cost (car slots) template 0)
         (set-cost (cdr slots) template)))))

(defun set-heuristic (keyword-set-slots template)
  (let*
    ((keyword-template (keywordify-tree template))
     (set-cost (set-cost keyword-set-slots keyword-template)))
    (<= set-cost (template-cost keyword-template))))

(defun set-update (args keyword-writer-map struct)
  (cond
   ((atom args) struct)
   (t `(,(cdr (assoc (car args) keyword-writer-map)) ;Writer
        ,(cadr args)                        ;Value
        ,(set-update (cddr args) keyword-writer-map struct)))))

(defloop copy-update-fn
  (keyword-slot-names args keyword-reader-map struct check)
  (for ((keyword-slot in keyword-slot-names))
    (collect
     (let ((assigned? (assoc-keyword keyword-slot args)))
       (if assigned?
           (if check
               `(CHECK-VARS-NOT-FREE
                 (,*binding-variable*)
                 ,(cadr assigned?))
             (cadr assigned?))
         `(,(cdr (assoc keyword-slot keyword-reader-map))
           ,struct))))))

(defloop all-slots-assigned-p (keyword-slot-names args)
  (for ((keyword-slot in keyword-slot-names))
    (always (assoc-keyword keyword-slot args))))

(defun copy-update (name keyword-slot-names args keyword-reader-map struct)
  "If all slots are assigned (equivalent to a constructor call), or the
   updated thing is an atom (variable symbol), then we can simply do the
   copy. Otherwise, bind the struct to a temp and then do the copy."
  (if (or (atom struct)
          (all-slots-assigned-p keyword-slot-names args))
      `(,name ,@(copy-update-fn keyword-slot-names args
                                keyword-reader-map
                                struct nil))
    `(LET ((,*binding-variable* ,struct))
       (,name ,@(copy-update-fn keyword-slot-names args
                                keyword-reader-map
                                *binding-variable* t)))))

(defun inline-update-fn (args template tree check)
  "Write a CONS form to update slots from args, given the structure template
   and tree."
  (cond
   ((atom template) (cond
                     ((null template) (mv nil nil))
                     (t (let* ((keyword-slot (keywordify template))
                               (found (assoc-keyword keyword-slot args))
                               (val (cadr found)))
                          (cond
                           (found
                            (mv t (cond
                                   (check `(CHECK-VARS-NOT-FREE
                                            (,*binding-variable*)
                                            ,val))
                                   (t val))))
                           (t (mv nil tree)))))))
   (t (mv-let (car-found car-result)
        (inline-update-fn args (car template) `(CAR ,tree) check)
        (mv-let (cdr-found cdr-result)
          (inline-update-fn args (cdr template) `(CDR ,tree) check)
          (cond
           ((not (or car-found cdr-found)) (mv nil tree))
           (t (mv
               t
               `(CONS
                 ,(cond
                   (car-found car-result)
                   (t `(CAR ,tree)))
                 ,(cond
                   (cdr-found cdr-result)
                   ((null (cdr template)) nil)
                   (t `(CDR ,tree))))))))))))

(defun inline-update (args template struct keyword-slot-names)
  (let ((bind (and (not (atom struct))
                   (not (all-slots-assigned-p keyword-slot-names args)))))
    (mv-let (found form)
      (inline-update-fn
       args template (if bind *binding-variable* struct) bind)
      (cond
       (bind `(LET ((,*binding-variable* ,struct)) ,form))
       (t form)))))

(defun keyword-updater-fn (form struct args name keyword-updater
                                keyword-slot-names read-only-keyword-slots
                                update-method template keyword-reader-map
                                keyword-writer-map)
  (cond
   ((keyword-slot-checker keyword-updater form args keyword-slot-names))
   ((intersection-eq (evens args) read-only-keyword-slots)
    (bomb-from keyword-updater
               "The argument list in the macro invocation ~p0 is not ~
                valid because it specifies ~#1~[a~/an~] update for the ~
                ~#1~[slot~/slots~] ~&1 which ~#1~[is a~/are~] ~
                :READ-ONLY ~#1~[slot~/slots~]."
               form (intersection-eq (evens args) read-only-keyword-slots)))
   (t

    ;;  Determine the kind of update we're going to do. The :HEURISTIC method
    ;;  always chooses either :SET or :COPY.

    (let*
      ((keyword-set-slots (evens args))
       (method (if (eq update-method :HEURISTIC)
                   (if (set-heuristic keyword-set-slots template)
                       :SET
                     :COPY)
                 update-method)))

      (case method
        (:SET (set-update args keyword-writer-map struct))
        (:COPY (copy-update name keyword-slot-names args
                            keyword-reader-map struct))
        (:INLINE (inline-update args template struct keyword-slot-names))
        (t (bomb-from 'KEYWORD-UPDATER-FN "Illegal method: ~p0."
                      method)))))))

(defun keyword-updater (db)
  (db-let (keyword-updater name keyword-slot-names slot-names
                     update-method template)
    (if keyword-updater
        (list
       "
;  This is the macro that provides for updates of multiple slots of a
;  structure.
 "
       `(DEFMACRO ,keyword-updater (&WHOLE FORM STRUCT &REST ARGS)
          (KEYWORD-UPDATER-FN
           FORM STRUCT ARGS ',name ',keyword-updater
           ',keyword-slot-names ',(read-only-keyword-slots slot-names db)
           ',update-method ',template ',(keyword-reader-map slot-names db)
           ',(keyword-writer-map slot-names db))))
      nil)))

;;;  READ-LEMMA

(defloop read-lemma-body (slot-names db)
  (for ((slot in slot-names))
    (collect (db-let ((slot reader) constructor-call)
               `(EQUAL (,reader ,constructor-call) ,slot)))))

(defun read-lemma (db)
  (db-let (slot-names read-lemma)
    (if read-lemma
        (list
         "
;  This lemma simplifies reads of an explicit constructor.
 "
         `(DEFTHM ,read-lemma
            (AND ,@(read-lemma-body slot-names db))))
      nil)))

;;; WRITE-LEMMA

(defloop write-lemma-body (slot-names db)
  (for ((slot in slot-names))
    (unless (db slot :READ-ONLY)
      (collect
       (db-let ((slot writer) constructor-call value-variable)
         `(EQUAL (,writer ,value-variable ,constructor-call)
                 ,(subst value-variable slot constructor-call)))))))

(defun write-lemma (db)
  (db-let (slot-names write-lemma)
    (if write-lemma
        (list
       "
;  This lemma simplifies writes of an explicit constructor.
 "
       `(DEFTHM ,write-lemma
          (AND ,@(write-lemma-body slot-names db))))
      nil)))

;;;  LIFT-IF-LEMMA

#|

The reasons for lifting IF out are as described below, but we always do it
rather than check for the SYNTAXP hyp.  This was important for Alessandro's
work.  Also added IF lifting for the slot writers, in the hope of winning
some simplifications in that way as well ( we do on his examples ).

; (defun lift-if-syntaxp (left right constructor)
;   ":doc-section lift-if-syntaxp
;   Meta heuristic for `lifting' IF through structure accessors.
;   ~/~/
;
; The `LIFT-IF' lemma is introduced as a heuristic to speed certain proofs
; about specifications involving conditional structure access.  Here is the
; idea.  Imagine a generic structure defined by
;
;  (DEFSTRUCTURE FOO A B C).
;
; Now imaging that the term
;
;  (FOO-A (IF test x y))
;
; appears during a proof about a specification involving the structure.
; This will happen because ACL2 does not normally move IF around during
; simplification.  Instead, ACL2 simplifies, with IF in place, and then
; clausifies out the IFs to produce cases.
;
; Now, if the term above is actually
;
;  (FOO-A (IF test (FOO a b c) (FOO a1 b1 c1))),
;
; i.e., both the left and right branch of the IF are instances of the
; constructor, then we can simplify this term to
;
;  (IF test a a1).
;
; Even though we haven't eliminated the need to clausify away the IF, we have
; at least reduced the size of the term, perhaps substantially.  This is
; important because if we had clausified away to cases involving
;
;  (FOO-A (FOO a b c)) and (FOO-A (FOO a1 b1 c1))
;
; the prover is obligated to examine all of (FOO a b c) and (FOO a1 b1 c1)
; before applying the simple `read lemma' for the structure.  The sizes of
; terms can also have a very significant impact on the amount of time spent on
; I/O.
;
; If it so happened that a = a1, e.g., this slot is invariant in a
; specification, then this would be further simplified to simply
;
; a,
;
; which will potentially result in one less test during clausification.
;
; The heuristic embodied in this lemma is to lift IF through calls of the
; accessors if there is some hope that doing so will reduce the size of the
; resulting term.  If the left and right hand sides of the IF are both
; instances of the constructor, then we know that this will work, thanks to the
; `read lemma' for the structure.  We also lift the IFs out if the left or
; right hand sides are themselves IF, hoping to win further down.  This
; heuristic has been found to result in very significant proof speedups for
; certain types of proofs. ~/"
;
;   (declare (xargs :guard t
;                   :mode :logic))
;
;   (and (consp left)
;        (consp right)
;        (symbolp constructor)
;        (or (eq (car left) 'IF)
;            (eq (car left) constructor))
;        (or (eq (car right) 'IF)
;            (eq (car right) constructor))))
|#

(defloop lift-if-writers (slots test left right db)
  (for ((slot in slots))
    (when (db slot :WRITER)
      (collect
       (db-let (value-variable (slot writer))
         `(EQUAL (,writer ,value-variable (IF ,test ,left ,right))
                 (IF ,test
                     (,writer ,value-variable ,left)
                   (,writer ,value-variable ,right))))))))

(defloop lift-if-readers (slots test left right db)
  (for ((slot in slots))
    (collect
     (db-let ((slot reader))
       `(EQUAL (,reader (IF ,test ,left ,right))
               (IF ,test (,reader ,left) (,reader ,right)))))))

(defun lift-if-lemma-fn (slots test left right db)
  (append (lift-if-readers slots test left right db)
          (lift-if-writers slots test left right db)))

(defun lift-if-lemma (db)
  (db-let (name lift-if-lemma representation slot-names)
    (let ((test (pack-intern name name "-TEST")) ;Makes forms easer to read
          (left (pack-intern name name "-LEFT")) ;w/o package marks.
          (right (pack-intern name name "-RIGHT")))
      (if lift-if-lemma
          (list
           "
;  This lemma lifts IF through calls of the slot accessors.
 "
           `(DEFTHM ,lift-if-lemma
              (AND ,@(lift-if-lemma-fn slot-names test left right db))))
        nil))))

;;;  ELIMINATION-LEMMA

(defun elimination-lemma (db)
  (db-let (elimination-lemma slot-names name force
                             weak-predicate-call)
    (if (and elimination-lemma)
        (list
         "
;  This is the :ELIM lemma for the constructor.
 "
         `(DEFTHM ,elimination-lemma
            (IMPLIES
             ,(if force
                  `(FORCE ,weak-predicate-call)
                weak-predicate-call)
            (EQUAL (,name ,@(map-slots-db slot-names :READER-CALL db))
                   ,name))
            :RULE-CLASSES (:REWRITE :ELIM)))
      nil)))

#|
;;;  NORMALIZATION LEMMA

(defloop normalize-equal-conjuncts (slot-names db)
  (for ((slot in slot-names))
    (collect `(EQUAL ,slot ,(db slot :reader-call)))))

(defloop normalization-rhs (slot-names written-slot db)
  (for ((slot in slot-names))
    (collect
     (db-let (value-variable (slot reader) name)
       (cond
        ((eq slot written-slot) value-variable)
        (t `(,reader ,name)))))))

(defloop normalization-conjuncts (slot-names all-slot-names db)
  (for ((slot in slot-names))
    (unless (db slot :READ-ONLY)
      (collect
       (db-let ((slot writer) value-variable name)
         `(EQUAL (,writer ,value-variable ,name)
                 (,name ,@(normalization-rhs all-slot-names slot db))))))))

(defun normalization-lemma (db)
  (db-let (name constructor-call normalization-lemma slot-names force
                weak-predicate-call)

    ;;  Note: In the first conjunct below (the equality conjunct), if both the
    ;;  LHS and RHS are explicit references of the constructor, then we can
    ;;  rewrite w/o hypotheses.  Rather than introducing 2 lemmas, however, we
    ;;  simply introduce the most general one, assuming that one will be able
    ;;  to relieve the weak predicate hypothesis.

    (if normalization-lemma
        (list
         "
;  This lemma normalizes symbolic writes by transforming the symbolic
;  structure into an explicit reference of the constructor.  The first
;  conjunct is a lemma that will normalize equality tests for this structure
;  when one of the objects is an explicit reference of the constructor.
 "
         `(DEFTHM ,normalization-lemma

            (IMPLIES
             ,(if force
                  `(FORCE ,weak-predicate-call)
                weak-predicate-call)
             (AND
              (EQUAL (EQUAL ,constructor-call ,name)
                     (AND ,@(normalize-equal-conjuncts slot-names db)))
              ,@(normalization-conjuncts slot-names slot-names db)))))
      nil)))

|#

;;;  SLOT-WRITERS-LEMMAS

;  The slot writers always preserve the weak predicate on the structures they
;  write.  A more interesting case concerns the question of whether a write
;  to a slot returns a structure that satisfies the predicate.  In general,
;  the predicate can involve complex relationships between the slots, thus it
;  is necessary to normalize the structure being written to an explicit call
;  of the constructor, and then the `predicate-constructor-lemma' will prove
;  the conjecture.  In the special case [ which is probably the most common ]
;  that there are no complex interrelationships, we can prove the predicate
;  by simply proving the particular assertion(s) about the slot.

(defloop weak-predicate-slot-writers-lemma-fn (weak-predicate writer-calls)
  (for ((call in writer-calls))
    (collect `(,weak-predicate ,call))))

(defloop normalization-rhs (slot-names written-slot db)
  (for ((slot in slot-names))
    (collect
     (db-let (value-variable (slot reader) name)
       (cond
        ((eq slot written-slot) value-variable)
        (t `(,reader ,name)))))))

(defloop map-access-assertion-bound-slots (assertions)
  (for ((assertion in assertions))
    (collect (access ASSERTION assertion :BOUND-SLOTS))))

(defloop map-subst-assertions (assertions slot value-variable)
  (for ((assertion in assertions))
    (collect
     (subst-expr-all assertion (list value-variable) (list slot)))))

(defloop all-bound-slots-fn (slot-names db)
  (for ((slot in slot-names))
    (append (map-access-assertion-bound-slots (db slot :ASSERTIONS)))))

(defun all-bound-slots (slot-names db)
  (append (map-access-assertion-bound-slots (db :ASSERTIONS))
          (all-bound-slots-fn slot-names db)))

(defun simple-slot-p (slot db)
  (db-let ((slot assertions) slot-names)
    (and (equal (remove-duplicates-equal
                 (map-access-assertion-bound-slots assertions))
                (list (list slot)))
         (not
          (member slot
                  (flatten (all-bound-slots (remove slot slot-names) db)))))))

(defloop predicate-slot-writers-lemma-fn
  (predicate slot-names all-slot-names db)
  (for ((slot in slot-names))
    (unless (db slot :READ-ONLY)
      (collect
       (db-let (name assertions predicate-call weak-predicate-call
                     value-variable (slot writer-call))
         (if (not (simple-slot-p slot db))
             `(IMPLIES
               ,weak-predicate-call
               (EQUAL (,predicate ,writer-call)
                      (,predicate
                       (,name
                        ,@(normalization-rhs all-slot-names slot db)))))
           (let* ((slot-assertions-assertions
                   (map-access-assertion-assertion (db slot :ASSERTIONS)))
                  (subst-assertions
                   (map-subst-assertions slot-assertions-assertions
                                         slot value-variable)))
             `(IMPLIES
               ,predicate-call
               (IFF (,predicate ,writer-call)
                    ,(if subst-assertions
                         (cond
                          ((cdr subst-assertions)
                           `(AND ,@subst-assertions))
                          (t (car subst-assertions)))
                       'T))))))))))

(defun slot-writers-lemmas (db)
  (db-let (weak-predicate-slot-writers-lemma
           weak-predicate-call weak-predicate
           predicate-slot-writers-lemma predicate
           slot-names)

    (append
     (if weak-predicate-slot-writers-lemma
         (list
          "
;  This lemma backchains the weak predicate through the slot writers.
  "
          `(DEFTHM ,weak-predicate-slot-writers-lemma
             (IMPLIES
              ,weak-predicate-call
              (AND ,@(weak-predicate-slot-writers-lemma-fn
                      weak-predicate (map-if-slots-db slot-names :WRITER-CALL
                                                   db))))))
       nil)
     (if predicate-slot-writers-lemma
         (list
              "
;  This lemma proves the predicate on a slot writer call.  For simple slots
;  whose assertions (if any) only mention the slot itself one need only prove
;  the assertion about the new slot.  For more complex slot assertions, or if
;  the structure as a whole has an assertion, it is necessary to normalize
;  the slot writer call to an explicit instance of the constructor.
  "
              `(DEFTHM ,predicate-slot-writers-lemma
                 (AND ,@(predicate-slot-writers-lemma-fn
                         predicate slot-names slot-names db))))
       nil))))

;;;  READ-WRITE-LEMMA

(defloop read-write-conjuncts1 (slot-names write-slot db)
  (for ((read-slot in slot-names))
    (collect
     (db-let (value-variable (read-slot reader) (write-slot writer) name)
       (cond
        ((eq read-slot write-slot)
         `(EQUAL (,reader (,writer ,value-variable ,name))
                 ,value-variable))
        (t `(EQUAL (,reader (,writer ,value-variable ,name))
                   (,reader ,name))))))))

(defloop read-write-conjuncts (slot-names all-slot-names db)
    (for ((write-slot in slot-names))
      (unless (db write-slot :READ-ONLY)
        (append (read-write-conjuncts1 all-slot-names write-slot db)))))

(defun read-write-lemma (db)
  (db-let (read-write-lemma slot-names force weak-predicate-call)
    (if read-write-lemma
        (list
         "
;  This lemma normalizes symbolic reads of symbolic writes by `pushing'
;  reads though nested writes until either 1) a symbolic write of the read
;  slot is detected, or 2) something unrecognized is found.
 "
         `(DEFTHM ,read-write-lemma
            (AND ,@(read-write-conjuncts slot-names slot-names db))))
      nil)))

;;;  WRITE-WRITE-LEMMA

(defloop write-write-conjuncts1 (deep-slot template db)
  (for ((shallow-slot in template))
    (unless (db shallow-slot :READ-ONLY)
      (collect
       (db-let (value-variable value-variable1 name)
         (let ((deep-writer (db deep-slot :WRITER))
               (shallow-writer (db shallow-slot :WRITER)))
           (if (eq deep-slot shallow-slot)
               `(EQUAL (,deep-writer ,value-variable
                                     (,deep-writer ,value-variable1 ,name))
                       (,deep-writer ,value-variable ,name))
             `(EQUAL (,deep-writer ,value-variable
                                   (,shallow-writer ,value-variable1 ,name))
                     (,shallow-writer ,value-variable1
                                      (,deep-writer ,value-variable ,name))))))))))

(defloop write-write-conjuncts (template db)
  (for ((slot in template))
    (unless (db slot :READ-ONLY)
      (append (write-write-conjuncts1 slot template db)))))

(defun write-write-lemma (db)
  (db-let (write-write-lemma template tag)
    (if write-write-lemma
        (let ((template (reverse (flatten (if tag (cdr template) template)))))
          (list
           "
;  This lemma normalizes multiple nested writes of a structure by pushing
;  writes for `deep' slots through writes to `shallow' slots, and reducing
;  redundant writes to the same slot to a single write.
  "
           `(DEFTHM ,write-write-lemma
              (AND ,@(write-write-conjuncts  template db)))))
      nil)))

;;;  NAKED-PROOFS

(defloop map-rules-for-rule-classes (rules)
  (for ((rule in rules)) (collect (access RULE rule :RULE-CLASS))))

(defloop map-assertions-for-rule-classes (assertions)
  (for ((assertion in assertions))
    (append (map-rules-for-rule-classes (access ASSERTION assertion :RULES)))))

(defloop map-slot-assertions-for-rule-classes (slot-names db)
  (for ((slot in slot-names))
    (append (db-let ((slot assertions))
              (map-assertions-for-rule-classes assertions)))))

(defun all-rule-classes (db)
  (db-let (assertions slot-names)
    (append (map-slot-assertions-for-rule-classes slot-names db)
            (map-assertions-for-rule-classes assertions))))

(defun naked-proofs (db)
  (db-let (assertion-lemma predicate predicate-call
                           predicate-guard-hints
                           assertion-lemma-hints guards verify-guards)
    (if (or assertion-lemma (and guards verify-guards))
        (append
         (list `(LOCAL (IN-THEORY (ENABLE ,predicate))))
         (and guards verify-guards
              (list
               "
;  The guard verification for the predicate is performed here since it may
;  need the current environment.  If it does not prove then you may need some
;  hints.  Any :PREDICATE-GUARD-HINTS option to DEFSTRUCTURE will be attached
;  to this lemma.
 "
               `(VERIFY-GUARDS ,predicate
                               ,@(and predicate-guard-hints
                                      (list :HINTS predicate-guard-hints)))))
         (and assertion-lemma
              (list
               "
;  This lemma captures all assertions about the structure.  This lemma is not
;  guaranteed to prove.  If it does not prove than you may have to provide
;  some :HINTS.  Any :ASSERTION-LEMMA-HINTS option to DEFSTRUCTURE will be
;  attached to this lemma.  Be sure that you have not specified
;  unsatisfiable assertions.
 "

               `(DEFTHM ,assertion-lemma
                  (IMPLIES
                   ,predicate-call
                   ,(predicate-body db))
                  :RULE-CLASSES
                  ,(all-rule-classes db)
                  ,@(and assertion-lemma-hints
                         (list :HINTS assertion-lemma-hints))))))
      nil)))

;;;  MV-INTRO-MACRO

(defun mv-intro-macro-case-body (readers form n)
  (cond
   ((atom readers) ())
   (t (cons `(,n (,(car readers) ,form))
            (mv-intro-macro-case-body (cdr readers) form (1+ n))))))

(defun mv-intro-macro-fn (name form event-name readers)
  (let*
    ((event-name (if event-name
                     event-name
                   (pack-intern (car form) name "-MV-INTRO-" (car form))))
     (n (car (unique-symbols 1 'MV-INTRO-MACRO-N (flatten form))))
     (mv-nth-form `(MV-NTH ,n ,form)))

    `(DEFTHM ,event-name
       (EQUAL ,mv-nth-form
              (CASE ,n
                ,@(MV-intro-macro-case-body readers form 0)
                (T (HIDE ,mv-nth-form))))
       :HINTS
       (("Goal"
         :IN-THEORY '(ZP OPEN-MV-NTH ,@readers)
         :EXPAND (HIDE ,mv-nth-form))))))

(defun mv-intro-macro (db)
  (db-let (name slot-names mv-intro-macro)
    (if mv-intro-macro
      (list
       "
;  This macro generates a lemma that will rewrite MV-NTH applied to any form
;  as a call of the appropriate reader for this MV structure.
"
       `(DEFMACRO ,mv-intro-macro (FORM &KEY EVENT-NAME)
          (DECLARE (XARGS :GUARD (AND FORM
                                      (SYMBOL-LISTP FORM)
                                      (SYMBOLP EVENT-NAME))))
          (MV-INTRO-MACRO-FN ',name FORM EVENT-NAME
                          ',(map-slots-db slot-names :READER db))))
      nil)))

;;;  DEFINITION-THEORY

; At one time we DISABLEd all :TYPE-PRESCRIPTION runes, just to make the theory
; as abstract as possible.  However a user had an example where it was
; advantageous to use the type information.  They had a spec that returned
; either a structure or a symbol that represeted a `meta-error'.  One can now
; prove that specifications like this don't return non-structure values by type
; reasoning.   I suppose that people might also want to use a structure as a
; template that they may also access by CAR and CDR for example, so they'll
; need the type info.

; At one time we also had DISABLEd the executable counterpart of the
; constructor.  This lead to problems when trying to compare constant
; structures defined with DEFCONST, which always evaluates, to constant
; structures generated during a proof.

#|

(defloop r/w-type-prescriptions-fn (fns)
  (for ((fn in fns))
    (collect `(:TYPE-PRESCRIPTION ,fn))))

(defun r/w-type-prescriptions (db)
  (db-let (slot-names)
    (r/w-type-prescriptions-fn
     (append (map-if-slots-db slot-names :READER db)
             (map-if-slots-db slot-names :WRITER db)))))
|#

(defun definition-theory (db)
  (db-let (name weak-predicate predicate definition-theory slot-names
                representation mix inline)
    (if inline
        nil
      (list
       "
;  This theory consists of all :DEFINITION runes associated with the
;  constructor, predicates, and slot readers/writers.  Only the
;  :TYPE-PRESCRIPTIONS and :EXECUTABLE-COUNTERPARTS remain ENABLEd.
 "
       `(DEFTHEORY ,definition-theory
          '(

            ;;  Note that for :MV structures the constructor is a macro.

            ,@(if (eq representation :MV)
                  nil
                (list name))
            ,weak-predicate
            ,predicate
            ,@(and (not mix) (map-if-slots-db slot-names :READER db))
            ,@(and (not mix) (map-if-slots-db slot-names :WRITER db))))
       `(IN-THEORY (DISABLE ,definition-theory))))))

;;;  LEMMA-THEORY

(defloop lemma-theory-names (lemma-names db)
  (for ((lemma-key in lemma-names))
    (append
     (let ((lemma-name (db-fn lemma-key `(LEMMA-THEORY ,lemma-key) db)))
       (if lemma-name (list lemma-name) nil)))))

(defun lemma-theory (db)
  (db-let (lemma-theory inline)
    (if inline
        nil
      (list
       "
;  This theory lists every lemma generated by this DEFSTRUCTURE.  These are
;  normally to remain ENABLEd.
 "
       `(DEFTHEORY ,lemma-theory
          '(,@(lemma-theory-names *lemma-names* db)))))))


;;;****************************************************************************
;;;
;;;    Parsing
;;;
;;;****************************************************************************
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Constants
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defconst *update-methods* '(:HEURISTIC :SET :COPY))

(defconst *keyword-representations* '(:LIST :MV :DOTTED-LIST :TREE))

(defconst *options*
  '(:ASSERT :ASSERTION-LEMMA-HINTS :CONC-NAME :DO-NOT
            :FORCE :GUARDS :MV-INTRO-MACRO :KEYWORD-CONSTRUCTOR
            :KEYWORD-UPDATER :PREDICATE :PREDICATE-GUARD-HINTS :PREFIX
            :INLINE :MIX :READ-WRITE-LEMMA :REPRESENTATION :SET-CONC-NAME
            :SLOT-WRITERS :WEAK-PREDICATE :UPDATE-METHOD :VERIFY-GUARDS
            :WRITE-WRITE-LEMMA)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "The valid options for DEFSTRUCTURE options."
|#)

(defconst *duplicate-options*
  '(:ASSERT :DO-NOT)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "Only these options may be duplicated."
|#)

(defconst *do-not-options* '(:TAG #|:NORMALIZE|# :READ-WRITE :WRITE-WRITE)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "Things done by default, they can be undone by a :DO-NOT option."
|#)

(defconst *slot-options*
  '(:DEFAULT :READ-ONLY :ASSERT)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "The valid options for DEFSTRUCTURE <slot-and-options>."
|#)

(defconst *duplicate-slot-options*
  '(:ASSERT)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "Options for DEFSTRUCTURE <slot-and-options> that can be duplicated."
|#)

(defconst *rule-tokens*
  '(:BUILT-IN-CLAUSE :COMPOUND-RECOGNIZER :CONGRUENCE :DEFINITION :ELIM
                     :EQUIVALENCE :FORWARD-CHAINING :GENERALIZE :INDUCTION
                     :LINEAR :LINEAR-ALIAS :META NIL :REFINEMENT :REWRITE
                     :TYPE-PRESCRIPTION :TYPE-SET-INVERTER
                     :WELL-FOUNDED-RELATION)
; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "The valid Acl2 rule-tokens. These may need to be updated from time to
   time."
|#)


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Assertion and Rule Checking
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun check-assertion (assertion slot context db)
  "Check the assertion for syntax, and return an ASSERTION record containing
   the assertion, its bound slots, its substitution, and its associated slot."
  (db-let (slot-names)
    (cond

     ;;  If not a LAMBDA, make sure that it is at least a `vanilla' term.

     ((not (assertion-termp assertion))
      (bomb "Assertions are required to satisfy STRUCTURES::ASSERTION-TERMP, ~
             and ~p0 does not because ~@1."
            assertion (reason-for-not-assertion-termp assertion)))

     ;;  This is an assertion term whose free variables are (hopefully!)
     ;;  indicated by FREE-VARS.

     (t (let*
          ((bound-slots (free-vars assertion))
           (err
            (cond
             ((not (subsetp bound-slots slot-names))
              (msg "is not a subset of the slot names ~p0." slot-names))
             ((and slot (not (member slot bound-slots)))
              (msg "does not contain the current slot ~p0." slot)))))
          (if err
              (bomb "The putative assertion ~p0 in the context ~p1 is not ~
                   a valid assertion because the free variable list of the ~
                   assertion (as defined by STRUCTURES::FREE-VARS), ~p2, ~
                   ~@3  If you feel that this message is incorrect, ~
                   then restate your assertion as a LAMBDA function ~
                   and try again." assertion context bound-slots err)

            ;;  Here, the `subst-assertion' is made by substitution of the
            ;;  access forms for the free variables.

            (make ASSERTION
                  :assertion assertion
                  :bound-slots bound-slots
                  :subst-assertion
                  (subst-expr-all assertion
                                  (map-slots-db bound-slots :READER-CALL db)
                                  bound-slots)
                  :slot slot
                  :rules NIL)))))))


(defun parse-rule (rule default-assertion context slot db)
  "Check rule syntax and return a RULE record."

  (let ((rule-token (if (atom rule) rule (car rule))))

    (if (or (not (symbolp rule-token))
            (not (member rule-token *rule-tokens*)))

        (bomb "The putative rule descriptor ~p0 in the context ~
               ~p1 is not valid because ~#2~[it~/its CAR~] ~
               is not one of the allowable rule tokens ~v3."
              rule context (if (equal rule rule-token) 0 1) *rule-tokens*)

      (cond

       ;;  A symbolic rule inherits everything from the default-assertion.

       ((or (atom rule) (null (cdr rule)))
        (make RULE
              :assertion default-assertion
              :rule-class
              `(,rule-token
                :COROLLARY
                ,(make-corollary default-assertion db))))

       ((not (true-listp rule))
        (bomb "The putative atomic rule descriptor ~p0 in the context ~
           ~p1 is not valid because it is not a true list."
              rule context))

       ;;  This is (rule-token assertion . other-rule-stuff).  We parse the
       ;;  assertion and append the other-rule-stuff to make the rule-class.

       (t (let
            ((assertion (check-assertion (second rule) slot rule db)))

            (make RULE
                  :assertion assertion
                  :rule-class
                  (append
                   `(,rule-token
                     :COROLLARY ,(make-corollary assertion db))
                   (rest (rest rule))))))))))

(defloop parse-rule-list (rule-list default-assertion context slot db)
  (for ((rule in rule-list))
    (collect (parse-rule rule default-assertion context slot db))))


(defloop parse-assert-options (assert-options slot db)
  "Traverse the assert-options (which *only* consist of :ASSERT options),
  and check the syntax and collect a list of ASSERTION records."

  (for ((option in assert-options))
    (collect
     (if (or (atom option)
             (atom (rest option))
             (not (true-listp option)))

         (bomb "The :ASSERT option ~p0 needs an assertion and optional ~
           rule-descriptors, or it is not a true list.")

       (let*
         ((assertion (check-assertion (second option) slot option db))
          (rule-list
           (parse-rule-list
            (rest (rest option))        ;The rules.
            assertion                        ;The default assertion.
            option                        ;Context
            slot                        ;Required slot.
            db)))

         (change ASSERTION assertion :RULES rule-list))))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;  PARSE-SLOT-OPTIONS
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defloop parse-slot-options (slots db)
  "We know that the slot is either a valid symbol, or a CONS whose CAR is a
  valid symbol.  Check all of the rest of the syntax and return an extension
  to be APPENDed to the DB."

  (for ((slot-and-options in slots))
    (append
     (let*
       ((slot-name (if (symbolp slot-and-options)
                       slot-and-options
                     (car slot-and-options)))

        (options (if (symbolp slot-and-options) nil (cdr slot-and-options)))

        (option-err
         (get-option-check-syntax 'DEFSTRUCTURE options *slot-options*
                                  *duplicate-slot-options* nil)))

       (acons-up
        ((cons slot-name :READ-ONLY)
         (get-option-as-flag 'DEFSTRUCTURE :READ-ONLY options))

        ((cons slot-name :DEFAULT-SPECIFIED)
         (get-option-entry :DEFAULT options))

        ((cons slot-name :DEFAULT)
         (get-option-argument 'DEFSTRUCTURE :DEFAULT options
                              :FORM nil nil))

        ((cons slot-name :ASSERTIONS)
         (parse-assert-options
          (get-option-entries :ASSERT options) slot-name db)))))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;  PARSE-DEFSTRUCTURE
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun get-string-designator (key options default)
  (designated-string
   (get-option-argument 'DEFSTRUCTURE key options :STRING-DESIGNATOR
                        default default)))

(defun get-symbol (key options default)
  (get-option-argument 'DEFSTRUCTURE key options :SYMBOL default default))

(defloop parse-do-not-options (do-not-options)
  "We allow any number of :DO-NOT options.  We return an alist to append to
   the DB that resets the defaults."
  (for ((options on do-not-options))
    (append
     (let
       ((do-nots (get-option-subset 'DEFSTRUCTURE :DO-NOT options
                                    *do-not-options* nil)))
       (pairlis$ do-nots (make-list (length do-nots) :initial-element
                                    nil))))))

(defun get-representation (options slot-names)
  "The :REPRESENTATION has a special syntax."
  (let ((opt (get-option-entry :REPRESENTATION options))
        (default :LIST))
    (cond
     (opt (cond
           ((consp opt)
            (cond
             ((null (cdr opt)) default)
             (t (if (and (true-listp opt)
                         (null (cddr opt))
                         (or (member (cadr opt) *keyword-representations*)
                             (let ((l (flatten (cadr opt))))
                               (and (subsetp l slot-names)
                                    (subsetp slot-names l)
                                    (equal (length l)
                                           (length slot-names))))))
                    (cadr opt)
                  (bomb "The :REPRESENTATION option descriptor must be either ~
                         :REPRESENTATION, (:REPRESENTATION), ~
                         or (:REPRESENTATION representation), where ~
                         representation is either one of ~v0, or a CONS ~
                         tree which when flattened according to ~
                         STRUCTURES::FLATTEN yields a permutation of the ~
                         slot names ~p1, but ~p2 is not."
                        *keyword-representations* slot-names opt)))))
           (t default)))
     (t default))))

(defun parse-defstructure (name doc-and-slots)
  "Parse the DEFSTRUCTURE arguments, returning the DB"

  (let*
    ((name
      (if (and name (symbolp name))
          name
        (bomb "The <name> argument of DEFSTRUCTURE must be a ~
               non-NIL symbol, but ~p0 is not." name)))

     ;; Since doc-and-slots is an &REST arg, we know it's TRUE-LISTP.

     (doc (if (stringp (car doc-and-slots)) (car doc-and-slots) nil))
     (slots-and-options (if doc (cdr doc-and-slots) doc-and-slots))
     (last-car (car (last slots-and-options)))
     (options? (and (consp last-car) (eq (car last-car) :OPTIONS)))
     (options (if options? (cdr last-car) nil))
     (slots (if options? (butlast slots-and-options 1) slots-and-options))

     (option-err
      (get-option-check-syntax 'DEFSTRUCTURE options *options*
                               *duplicate-options* nil))

     (slot-names (map-x-or-car-x slots))

     (check-slot-names
      (or (null slot-names)
          (let
            ((err
              (cond
               ((not (arglistp slot-names))
                (msg "must be a valid argument list as defined by ~
                      ACL2::ARGLISTP, but ~p0 is not." slot-names))
               ((member name slot-names)
                (msg "may not contain the structure name, ~p0, but ~
                      ~p1 does." name slot-names))
               ((duplicates-equal (map-string slot-names))
                (msg "~p0 apparently contains symbols in different packages ~
                      that have the same print name, which is illegal."
                     slot-names)))))
            (if err
                (bomb "The implied list of slot names ~@0" err)
              T)))))

    ;;  Build and return the DB.  First, the user options.

    (extend-db
     ()                                        ;Initialize
     (acons-db
      (:NAME name)
      (:DOC doc)
      (:SLOT-NAMES slot-names)
      (:GUARDS (get-option-as-flag 'DEFSTRUCTURE :GUARDS options))
      (:VERIFY-GUARDS
       (get-option-member 'DEFSTRUCTURE :VERIFY-GUARDS options
                          '(T NIL) :DEFAULT :DEFAULT))
      (:INLINE (get-option-as-flag 'DEFSTRUCTURE :INLINE options))
      (:MIX    (get-option-as-flag 'DEFSTRUCTURE :MIX options))
      (:CONC-NAME
       (get-string-designator
        :CONC-NAME options (concatenate 'STRING (string name) "-")))
      (:SET-CONC-NAME
       (get-string-designator
        :SET-CONC-NAME options (concatenate 'STRING "SET-" (string name) "-")))
      (:KEYWORD-CONSTRUCTOR
       (get-symbol
        :KEYWORD-CONSTRUCTOR options (pack-intern name "MAKE-" name)))
      (:KEYWORD-UPDATER
       (get-symbol :KEYWORD-UPDATER options (pack-intern name "UPDATE-" name)))
      (:PREDICATE
       (get-symbol :PREDICATE options (pack-intern name name "-P")))
      (:WEAK-PREDICATE
       (get-symbol :WEAK-PREDICATE options
                   (pack-intern name "WEAK-" name "-P")))
      (:FORCE
       (get-option-as-flag 'DEFSTRUCTURE :FORCE options))
      (:REPRESENTATION (get-representation options slot-names))
      ;;  Note: The original default was to always generate :SLOT-WRITERS,
      ;;  but this was changed, so the code is all written in terms of a
      ;;  :READ-ONLY flag.
      (:READ-ONLY
       (let ((slot-writers
              (get-option-as-flag 'DEFSTRUCTURE :SLOT-WRITERS options)))
         (cond
          ((and slot-writers (eq (db :REPRESENTATION) :MV))
           (bomb ":MV structures can't have :SLOT-WRITERS."))
          (t (not slot-writers)))))
      (:MV-INTRO-MACRO
       (if (eq (db :REPRESENTATION) :MV)
           (get-symbol :MV-INTRO-MACRO options
                       (pack-intern name name "-INTRO"))
         (let ((entry (get-option-entry :MV-INTRO-MACRO options)))
           (if (and entry (or (atom entry) (atom (cdr entry)) (cadr entry)))
             (bomb "The :MV-INTRO-MACRO option is illegal unless the ~
                    (:REPRESENTATION :MV) option is chosen.")
             NIL))))
      (:UPDATE-METHOD
       (let* ((default (if (db :READ-ONLY) :COPY (if (db :MIX) :SET :HEURISTIC)))
              (method (get-option-member 'DEFSTRUCTURE :UPDATE-METHOD options
                                   *update-methods* default default)))
         (if (and (db :READ-ONLY) (not (eq method :COPY)))
             (bomb "The only valid :UPDATE-METHOD for structures without ~
                    :SLOT-WRITERS is :COPY.")
           (cond
            ((db :INLINE) :INLINE)
            (t method)))))
      (:ASSERTION-LEMMA-HINTS
       (get-option-argument 'DEFSTRUCTURE :ASSERTION-LEMMA-HINTS options
                            :FORM nil nil))
      (:PREDICATE-GUARD-HINTS
       (get-option-argument 'DEFSTRUCTURE :PREDICATE-GUARD-HINTS options
                            :FORM nil nil))
      (:PREFIX (get-string-designator :PREFIX options "DEFS-"))

      ;;  Set defaults to possibly be overidden.

      (:TAG name)
      #|(:NORMALIZE T)|#
      (:READ-WRITE T)
      (:WRITE-WRITE t))

     ;;  Override defaults.

     (append-db
      (parse-do-not-options (get-option-entries :DO-NOT options)))

     ;; Still extending we add the forms necessary to complete parsing, and
     ;; parsing the :ASSERT options and the slot descriptors, returning the
     ;; DB.

     (acons-db
      (:VALUE-VARIABLE (car (unique-symbols 2 (pack-intern name "VALUE")
                                            (cons name slot-names))))
      (:VALUE-VARIABLE1 (cadr (unique-symbols 2 (pack-intern name "VALUE")
                                              (cons name slot-names))))
      (:PREDICATE-CALL `(,(db :PREDICATE) ,name)))
     (append-db
      (reader-names slot-names db)
      (reader-calls slot-names db))
     (acons-db
      (:ASSERTIONS (parse-assert-options
                    (get-option-entries :ASSERT options) nil db)))
     (append-db (parse-slot-options slots db)))))



;;;****************************************************************************
;;;
;;;    DEFSTRUCTURE
;;;
;;;****************************************************************************

(defloop nullify-lemmas (lemma-names)
  (for ((lemma in lemma-names))
    (collect (cons lemma nil))))

(defun prepare-for-code-gen (db)

  (db-let (slot-names representation name predicate read-only tag
                      #|normalize|# read-write write-write mv-intro-macro
                      weak-predicate inline mix set-conc-name)
    (cond

     ;;  A few error checks.

     ((and (eq representation :MV)
           (< (len slot-names) 2)
           (bomb "An :MV structure must have at least 2 slots in order ~
                  to be valid according to the syntax of Acl2, but ~
                  the current structure has ~#0~[one slot~/no slots~]."
                 slot-names)))

     ((not weak-predicate)
      (bomb "You have apparently tried to suppress the generation of the
             weak predicate on the structure, which is currently illegal."))

     ((not predicate)
      (bomb "You have apparently tried to suppress the generation of the
             predicate on the structure, which is currently illegal."))

     (t

      (extend-db
       (acons-db
        (:KEYWORD-SLOT-NAMES (keywordify-list slot-names))
        (:REQUIRED-SLOT-NAMES (required-slot-names slot-names db))

        ;;  We force :READ-ONLY if all slots were :READ-ONLY, or the
        ;;  representation is :MV

        (:READ-ONLY (or read-only
                        (equal (read-only-keyword-slots slot-names db)
                               (db :KEYWORD-SLOT-NAMES))
                        (eq representation :MV)))

        ;;  We force :MV records to be untagged.  After settling the :TAG
        ;;  question we can build the template.

        (:TAG (if (eq representation :MV) nil tag))
        (:TEMPLATE (make-template db)))

       (db-let (read-only keyword-updater)
         (extend-db
          (acons-db

           ;;  Define function,macro, and lemma names, and code fragments. We
           ;;  use the convention that if a name is NIL, then it is a flag to
           ;;  the appropriate code generator not to generate that thing.

           (:CONSTRUCTOR-CALL `(,name ,@slot-names))
           (:ACL2-COUNT-LEMMA (if (eq representation :mv)
                                  nil
                                (make-prefix-name "ACL2-COUNT-" name)))

           ;;  Weak Predicate.

           (:WEAK-PREDICATE-CALL `(,weak-predicate ,name))
           (:WEAK-PREDICATE-CONSTRUCTOR-LEMMA
            (make-prefix-name weak-predicate "-" name))

           ;;  Predicate.

           (:PREDICATE-WEAK-PREDICATE-LEMMA
            (make-prefix-name predicate "-INCLUDES-" weak-predicate))

           (:PREDICATE-CONSTRUCTOR-LEMMA (make-prefix-name predicate "-" name))

           ;;  We suppress the keyword-updater if it's an :MV or there
           ;;  aren't any slots.

           (:KEYWORD-UPDATER (if (or (eq representation :MV) (not slot-names))
                                 nil
                               keyword-updater))

           (:READ-LEMMA (if slot-names (make-prefix-name "READ-" name) nil))
           (:WRITE-LEMMA (if (or read-only (not slot-names))
                             nil
                           (make-prefix-name "WRITE-" name)))

           (:LIFT-IF-LEMMA (if slot-names
                               (make-prefix-name name "-LIFT-IF")
                             nil))

           (:ELIMINATION-LEMMA (if (or mix
                                       (eq representation :MV)
                                       (not slot-names))
                                   nil
                                 (make-prefix-name "ELIMINATE-" name)))
           #|
           (:NORMALIZATION-LEMMA (if (and normalize slot-names (not read-only))
                                     (make-prefix-name "NORMALIZE-" name)
                                   nil))
           |#
           (:WEAK-PREDICATE-SLOT-WRITERS-LEMMA
            (if (and slot-names (not read-only))
                (make-prefix-name weak-predicate "-" set-conc-name)
              nil))
           (:PREDICATE-SLOT-WRITERS-LEMMA
            (if (and slot-names (not read-only))
                (make-prefix-name predicate "-" set-conc-name)
              nil))
           (:READ-WRITE-LEMMA (if (and (not mix)
                                       read-write
                                       (not read-only)
                                       slot-names)
                                  (make-prefix-name "READ-WRITE-" name)
                                nil))
           (:WRITE-WRITE-LEMMA (if (and (not mix)
                                        write-write
                                        (not read-only)
                                        slot-names)
                                   (make-prefix-name "WRITE-WRITE-" name)
                                nil))
           (:ASSERTION-LEMMA (if (and predicate (all-rule-classes db))
                                 (make-prefix-name name "-ASSERTIONS")
                               nil))

           (:DEFINITION-THEORY (make-prefix-name name "-DEFINITION-THEORY"))
           (:LEMMA-THEORY (make-prefix-name name "-LEMMA-THEORY")))

          ;;  In :INLINE mode we simply NULL out all lemma names to suppress
          ;;  their generation.  This could be done more cleanly perhaps,
          ;;  i.e., there was no reason to even generate them above, but
          ;;  this simple and is guaranteed to work.

          (append-db
           (writer-names slot-names db)
           (writer-calls slot-names db)
           (if inline
               (nullify-lemmas *lemma-names*)
             nil)))))))))


#|
For debugging.

(defmacro capsule (&rest args)
  `(QUOTE ,args))

(defmacro defstructure (name-and-options &rest doc-and-slots)
  (let ((db (prepare-for-code-gen
             (parse-defstructure name-and-options doc-and-slots))))
    `(QUOTE ,db)))


|#

(defmacro capsule (&rest args)
  "Remove documentation strings and recast as an ENCAPSULATE."
  `(ENCAPSULATE () ,@(remove-strings args)))

(encapsulate ()
  (logic)
  (deftheory minimal-theory-for-defstructure
    (append *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*
            (list-all *BUILT-IN-EXECUTABLE-COUNTERPARTS*)
            '(IFF CAR-CONS CDR-CONS CAR-CDR-ELIM EQLABLEP MV-NTH ZP TRUE-LISTP
                  OPEN-MV-NTH O< ACL2-COUNT

                  (cpath::clrp-list)
                  cpath::path-list-record-reduction-2-bool
                  CPATH::CLRP-LIST-EQUAL-CLRP-LIST-REWRITE
                  CPATH::CLRP-LIST-OF-SP-WHEN-DOMINATED-BY-SOME
                  (cpath::dominated-by-some)
                  (cpath::diverges-from-all)
                  acl2::TAG-LOCATION-elimination
                  cpath::acl2-count-gp-decreasing
                  cpath::acl2-count-gp-decreases
                  acl2::wfkey
                  (cpath::diverge)
                  (cpath::dominates)
                  acl2::car-cons
                  acl2::cdr-cons
                  (cpath::wfpath)
                  (acl2::wfr)
                  cpath::WFR-SP
                  cpath::psort-clrp-list
                  (cpath::psort)
                  cpath::gp-of-nil
                  cpath::path-list-record-reduction-1
                  cpath::path-list-record-reduction-2
                  cpath::gp-list
                  cpath::sp==r
                  acl2::not-failed-location
                  acl2::tag-location-elimination

                  acl2::append
                  acl2::len
                  acl2::nthcdr
                  cpath::dominated-by-some
                  cpath::diverges-from-all
                  cpath::dominates
                  cpath::diverge
                  cpath::gp-of-sp
                  CPATH::clrp-list-of-sp-when-dominated-by-some

                  (:TYPE-PRESCRIPTION ACL2-COUNT) INTEGER-ABS))))

(defmacro structures::defstructure (name &rest doc-and-slots)

  (let ((db (prepare-for-code-gen (parse-defstructure name doc-and-slots))))
    (db-let (inline guards)

      `(PROGN

        (CAPSULE
         "
;  We define the structure and all of the events (except the assertion theory)
;  in the absoulte minimum theory possible in order to expedite the proofs
;  and guarantee that they will always work.  If you ever find a case where
;  one of these proof fails (except due to user syntax errors) please
;  report it as a bug in DEFSTRUCTURE.
 "

         (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY-FOR-DEFSTRUCTURE)))

         ,@(constructor db)
         ,@(weak-predicate db)
         ,@(readers db)
         ,@(writers db)
         ,@(predicate db)
         ,@(keyword-constructor db)
         ,@(keyword-updater db)
         #|,@(normalization-lemma db)|#
         ,@(slot-writers-lemmas db)
         ,@(read-write-lemma db)
         ,@(write-write-lemma db)
         ,@(read-lemma db)
         ,@(write-lemma db)
         ,@(lift-if-lemma db)
         ,@(elimination-lemma db)
         ,@(extensionality db)
         ,@(mv-intro-macro db)
         ,@(definition-theory db))
        ,@(if (and inline (not guards))
              nil
            (list
             `(CAPSULE
               ,@(naked-proofs db)
               ,@(lemma-theory db))))))))




;;;
;;;
;;; beginning of defstructure+ stuff
;;;
;;;

#|

(defun harvest-field-names (name base form)
  (if (consp form)
      (let ((line (car form)))
        (if (consp line)
            (if (equal (car line) :options) nil
              (cons (join-symbols name base (car line))
                    (harvest-field-names name base (cdr form))))
          (if (symbolp line)
              (cons (join-symbols name base line)
                    (harvest-field-names name base (cdr form)))
            (harvest-field-names name base (cdr form)))))
    nil))



;bzo
(defthm integerp-+
  (implies
   (and
    (integerp a)
    (integerp b))
   (integerp (+ a b))))

;trying disabled.
(defthmd plus-constant-reduction
  (implies
   (and
    (syntaxp (quotep q))
    (integerp q)
    (integerp n))
   (iff (equal (+ 1 n) q)
        (equal n (1- q)))))

;bzo drop?
(defthmd len-reduction
  (implies
   (and
    (syntaxp (quotep n))
    (integerp n)
    (<= 0 n))
   (iff (equal (len x) n)
        (if (zp n) (not (consp x))
          (and (consp x)
               (equal (len (cdr x)) (1- n)))))))

(defun accessor-predicate (name doc-and-slots)
  (declare (xargs :mode :program))
  (let*
      ((doc (if (stringp (car doc-and-slots)) (car doc-and-slots) nil))
       (slots-and-options (if doc (cdr doc-and-slots) doc-and-slots))
       (last-car (car (last slots-and-options)))
       (options? (and (consp last-car) (eq (car last-car) :OPTIONS)))
       (options (if options? (cdr last-car) nil)))
    (let ((string (structures::get-string-designator
                   :CONC-NAME options (concatenate 'STRING (structures::string name) "-"))))
      (intern-in-package-of-symbol string name))))

(defun add-assertion-types (rst)
  (if (consp rst)
      (let ((entry (car rst)))
        (if (and (consp entry)               ; (field  (:assert (pred field)))
                 (consp (cdr entry))         ;        ((:assert (pred field)))
                 (null  (cddr entry)))
            (let ((assertion (cadr entry)))  ;         (:assert (pred field))
              (let ((assertion
                     (if (and (consp assertion)
                              (equal (car assertion) :assert)
                              (consp (cdr assertion))
                              (null  (cddr assertion)))
                         `(:assert ,(cadr assertion) :rewrite :forward-chaining)
                       assertion)))
                (let ((entry `(,(car entry) ,assertion)))
                  (cons entry (add-assertion-types (cdr rst))))))
          (cons entry (add-assertion-types (cdr rst)))))
    rst))



|#

(defmacro defstructure+ (name &rest rst)
  `(acl2::defstructure ,name ,@rst))

#+joe
(let ((pred (accessor-predicate name rst)))
    (let ((rst (add-assertion-types rst)))
      (let ((fields (harvest-field-names name pred rst)))
        (let ((paths (acl2::psort (enlist (enkey-field-names fields)))))
          (let ((field1 (number-symbol-list name fields 1))
                (field2 (number-symbol-list name fields 2)))
            `(encapsulate
              ()

              (acl2::defstructure ,name ,@rst)

              (defthm ,(join-symbols name name '-extensionality!)
                (implies
                 (and
                  (,(join-symbols name 'weak- name '-p) x)
                  (,(join-symbols name 'weak- name '-p) y)
                  )
                 (iff
                  (equal x y)
                  (equal (gp-list '(,@paths) x)
                         (gp-list '(,@paths) y))))
                :hints (("goal" :in-theory (e/d (acl2::path-list-record-reduction-1
                                                 acl2::path-list-record-reduction-2
                                                 ,(join-symbols name 'weak- name '-p)
                                                 ,name)
                                                (gp-list
                                                 (ACL2::CLRP-LIST)
                                                 ACL2::CLRP-LIST-OF-SP-WHEN-DIVERGES-FROM-ALL
                                                 acl2::GP-OF-CLRP-LIST-WHEN-DIVERGES-FROM-ALL
                                                 ACL2::S==R
                                                 ACL2::EQUAL-S-RECORD-EQUALITY)))))

              (defthm ,(join-symbols name name '-extensionality)
                (iff
                 (equal (,name ,@field1)
                        (,name ,@field2))
                 (and
                  ,@(existential-fields field1 field2)
                  ))
                :hints (("goal" :in-theory (enable ,name))))

              (in-theory (disable ,(join-symbols name name '-extensionality!)))

              ))))))

