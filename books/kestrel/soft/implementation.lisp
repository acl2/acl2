; SOFT ('Second-Order Functions and Theorems') -- Implementation
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file implements SOFT ('Second-Order Functions and Theorems'),
; a tool to mimic second-order functions and theorems
; in the first-order logic of ACL2.

; The code in this file is meant to be simple.
; Its efficiency can be improved if needed.
; The code is experimental and has undergone limited testing.
; Some possible improvements/extensions are discussed at the end of the file.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/alists/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For now SOFT assumes that the default DEFUN mode is :LOGIC.
; The second-order functions introduced using SOFT are in logic mode.

(logic)

; The guards in this file will be verified in the future.

(set-verify-guards-eagerness 0)

; Make the BODY system utility usable in logic mode.

(verify-termination latest-body) ; called by BODY
(verify-termination def-body) ; called by BODY
(verify-termination body)

; The JUSTIFICATION property of a recursive function is a record
; called JUSTIFICATION that has the form
; (SUBSET . ((SUBVERSIVE-P . (MP . REL)) (MEASURE . RULER-EXTENDERS)));
; see (DEFREC JUSTIFICATION ...) in the ACL2 sources.
; In that record,
; REL is the well-founded relation (a symbol)
; and MEASURE is the measure (a term).

(define justification ((fun symbolp) (w plist-worldp))
  (getprop fun 'justification nil 'current-acl2-world w))

(define wfrel ((fun symbolp) (w plist-worldp))
  (cddr (caddr (justification fun w))))

(define fmeasure ((fun symbolp) (w plist-worldp))
  (car (cadddr (justification fun w))))

; Logic-mode simplified version of the GUARD system utility.

(define fguard ((fun symbolp) (w plist-worldp))
  (getprop fun 'guard *T* 'current-acl2-world w))

; Logic-mode simplified version of the FORMULA system utility.

(define tformula ((thm symbolp) (w plist-worldp))
  (getprop thm 'theorem nil 'current-acl2-world w))

; Check that all the symbols in a list are names of functions.

(define function-symbol-listp ((syms symbol-listp) (w plist-worldp))
  (if (endp syms)
      t
    (and (function-symbolp (car syms) w)
         (function-symbol-listp (cdr syms) w))))

; Experiments suggest that
; the body of a DEFCHOOSE can be extracted from the DEFCHOOSE-AXIOM property,
; which has one of the following forms:
; 1. If there is one bound variable and :STRENGTHEN is NIL, the form is
;      (IMPLIES BODY ...).
; 2. If there are two or more bound variables and :STRENGTHEN is NIL,
;    the form is
;      (IF (TRUE-LISTP ...)
;          (IMPLIES BODY ...)
;        ...).
; 3. If there is one bound variable and :STRENGTHEN is T, the form is
;      (IF (IMPLIES BODY ...)
;          ...
;        ...).
; 4. If there are two or more bound variables and :STRENGTHEN is T, the form is
;      (IF (IF (TRUE-LISTP ...)
;              (IMPLIES BODY ...)
;            ...)
;        ...).
; From the form of DEFCHOOSE-AXIOM, the value of :STRENGTHEN can be determined.

(define defchoose-axiom ((fun symbolp) (w plist-worldp))
  (getprop fun 'defchoose-axiom nil 'current-acl2-world w))

(define defchoose-body ((fun symbolp) (w plist-worldp))
  :guard (defchoose-axiom fun w)
  (let ((axiom (defchoose-axiom fun w)))
    (if (eq (fn-symb axiom) 'implies) ; form 1
        (fargn axiom 1)
      (let ((if-test (fargn axiom 1)))
        (case (fn-symb if-test)
          (true-listp ; form 2
           (let ((if-then (fargn axiom 2)))
             (fargn if-then 1)))
          (implies ; form 3
           (fargn if-test 1))
          (otherwise ; form 4
           (let ((nested-if-then (fargn if-test 2)))
             (fargn nested-if-then 1))))))))

(define defchoose-strongp ; value of :STRENGTHEN
  ((fun symbolp) (w plist-worldp))
  :guard (defchoose-axiom fun w)
  (let ((axiom (defchoose-axiom fun w)))
    (and (eq (fn-symb axiom) 'if) ; not form 1
         (let ((if-test (fargn axiom 1)))
           (not (eq (fn-symb if-test) 'true-listp)))))) ; not form 2

; The quantified formula of a DEFUN-SK is in prenex normal form;
; the matrix of this prenex normal form is the term
; after the quantifier and bound variables.
; Experiments suggest that
; the matrix of a DEFUN-SK
; can be extracted from the defining body of the function
; (as returned by the BODY system utility),
; which has the form (RETURN-LAST ... ... CORE) or just CORE,
; where CORE has one of the following forms:
; 1. If there is one bound variable, the form is
;      ((LAMBDA (...) MATRIX) ...).
; 2. If there are two or more bound variables, the form is
;      ((LAMBDA (...) ((LAMBDA (...) MATRIX) ...)) ...).
; These two forms are ambiguous under certain conditions:
;   (DEFUN-SK FUN (FREE-VARS)
;     (FORALL/EXISTS MV (LET ((BV1 (MV-NTH 0 MV))
;                             ...
;                             (BVn (MV-NTH n-1 MV)))
;                         TERM)))
; internally looks the same as
;   (DEFUN-SK FUN (FREE-VARS)
;     (FORALL/EXISTS (BV1 ... BVn) TERM)).
; The two forms are unambiguous if it is known
; whether the DEFUN-SK has either one or more than one bound variables:
; this information is passed to the following code
; in the form of a boolean flag that is true when there was one bound variable.

(define defun-sk-matrix ((fun symbolp) (1bvarp booleanp) (w plist-worldp))
  (let* ((body (body fun nil w))
         (core (if (eq (car body) 'return-last)
                   (fargn body 3)
                 body))
         (lamb (fn-symb core)))
    (if 1bvarp
        (lambda-body lamb) ; form 1
      (let* ((nested-app (lambda-body lamb))
             (nested-lamb (fn-symb nested-app)))
        (lambda-body nested-lamb)))))

; Experiments suggest that
; the name of the witness of a function introduced via DEFUN-SK
; is the CONSTRAINT-LST of the function.

(define defun-sk-witness-name ((fun symbolp) (w plist-worldp))
  (getprop fun 'constraint-lst nil 'current-acl2-world w))

; Experiments suggest that
; to determine whether a DEFUN-SK
; is introduced with :STRENGTHEN set to T or not,
; the CONSTRAINT-LST of the witness can be inspected:
; if it has 3 constraints, :STRENGTHEN was T;
; if it has 2 constraints, :STRENGTHEN was NIL.

(define defun-sk-strongp ((fun symbolp) (w plist-worldp))
  (let* ((witness (defun-sk-witness-name fun w))
         (constraint-lst
          (getprop witness 'constraint-lst nil 'current-acl2-world w)))
    (= (len constraint-lst) 3)))

; The :BOGUS-DEFUN-HINTS-OK setting is in the ACL2-DEFAULTS-TABLE.

(define get-bogus-defun-hints-ok ((w plist-worldp))
  (let ((table (table-alist 'acl2-defaults-table w)))
    (cdr (assoc-eq :bogus-defun-hints-ok table))))

; Second-order functions and theorems depend on function variables.
; Each function variable is typed by the number of its arguments (1 or more).
; Types of function variables are denoted
; by the ACL2-signature-like notation (* ... *) => *.

(define *-listp (stars)
  (if (atom stars)
      (null stars)
    (and (eq (car stars) '*)
         (*-listp (cdr stars)))))

(define funvar-typep (type)
  (and (true-listp type)
       (= (len type) 3)
       (*-listp (first type))
       (first type)
       (eq (second type) '=>)
       (eq (third type) '*)))

; The name and type of each function variable are stored in a table.

(table function-variables nil nil :guard (and (symbolp key) ; name
                                              (funvar-typep val)))

(define funvarp (funvar (w plist-worldp))
  (let ((table (table-alist 'function-variables w)))
    (and (symbolp funvar)
         (not (null (assoc-eq funvar table))))))

(define funvar-type (funvar (w plist-worldp))
  :guard (funvarp funvar w)
  (let ((table (table-alist 'function-variables w)))
    (cdr (assoc-eq funvar table))))

; Function variables are mimicked by uninterpreted functions (i.e. stubs).
; The macro DEFUNVAR defines a function variable with its type.
; DEFUNVAR introduces the stub and updates the table of function variables.

(define defunvar-event (funvar arguments arrow result)
  (b* (((unless (symbolp funvar))
        (raise "~x0 must be a name." funvar))
       ((unless (*-listp arguments))
        (raise "~x0 must be a list (* ... *)." arguments))
       ((unless (eq arrow '=>))
        (raise "~x0 must be the arrow =>." arrow))
       ((unless (eq result '*))
        (raise "~x0 must be *." result)))
      `(progn
         (defstub ,funvar ,arguments => *)
         (table function-variables ',funvar '(,arguments => *)))))

(defmacro defunvar (funvar arguments arrow result)
  `(make-event (defunvar-event ',funvar ',arguments ',arrow ',result)))

(defmacro show-defunvar (funvar arguments arrow result)
  `(defunvar-event ',funvar ',arguments ',arrow ',result))

; A second-order function or theorem depends on
; a set of one or more function variables.
; The set is represented as a non-empty list without duplicates.

(define funvar-listp ; may be empty or have duplicates
  (funvars (w plist-worldp))
  (if (atom funvars)
      (null funvars)
    (and (funvarp (car funvars) w)
         (funvar-listp (cdr funvars) w))))

(define funvar-setp (funvars (w plist-worldp))
  (and (funvar-listp funvars w)
       funvars
       (no-duplicatesp funvars)))

; Three kinds of second-order functions are supported:
; plain functions
; (introduced via DEFUN2, which generates a DEFUN),
; choice functions
; (introduced via DEFCHOOSE2, which generates a DEFCHOOSE),
; and quantifier functions
; (introduced via DEFUN-SK2, which generates a DEFUN-SK).

(define sofun-kindp (kind)
  (or (eq kind 'plain)
      (eq kind 'choice)
      (eq kind 'quant)))

; A second-order function is mimicked by a (first-order) function
; that depends on one or more function variables,
; which are the function parameters of the second-order function
; (the second-order function may also have individual parameters,
; like a first-order function).
; A table associates to each second-order function name
; its kind and the set of its function parameters.
; In addition, the table associates
; to each choice or quantifier second-order function name
; its list of bound variables.
; In addition, the table associates
; to each quantifier second-order function name
; its quantifier (FORALL or EXISTS)
; and the kind of its rewrite rule
; (default, direct, or custom term;
; the custom term itself is not recorded in the table,
; just the fact that it is a custom term is recorded).

(define bound-varsp (bvars)
  (and (symbol-listp bvars)
       bvars
       (no-duplicatesp bvars)))

(define quantifierp (quant)
  (or (eq quant 'forall)
      (eq quant 'exists)))

(define qrewrite-kindp (qrkind)
  (or (eq qrkind 'default)
      (eq qrkind 'direct)
      (eq qrkind 'term)))

(define plain-sofun-infop (info (w plist-worldp))
  (and (true-listp info)
       (= (len info) 2)
       (sofun-kindp (first info))
       (funvar-setp (second info) w)))

(define choice-sofun-infop (info (w plist-worldp))
  (and (true-listp info)
       (= (len info) 3)
       (sofun-kindp (first info))
       (funvar-setp (second info) w)
       (bound-varsp (third info))))

(define quant-sofun-infop (info (w plist-worldp))
  (and (true-listp info)
       (= (len info) 5)
       (sofun-kindp (first info))
       (funvar-setp (second info) w)
       (bound-varsp (third info))
       (quantifierp (fourth info))
       (qrewrite-kindp (fifth info))))

(define sofun-infop (info (w plist-worldp))
  (or (plain-sofun-infop info w)
      (choice-sofun-infop info w)
      (quant-sofun-infop info w)))

(table second-order-functions nil nil :guard (and (symbolp key) ; name
                                                  (sofun-infop val world)))

(define sofunp (sofun (w plist-worldp))
  (let ((table (table-alist 'second-order-functions w)))
    (and (symbolp sofun)
         (not (null (assoc-eq sofun table))))))

(define sofun-kind (sofun (w plist-worldp))
  :guard (sofunp sofun w)
  (let ((table (table-alist 'second-order-functions w)))
    (first (cdr (assoc-eq sofun table)))))

(defabbrev plain-sofunp (sofun w)
  (and (sofunp sofun w)
       (eq (sofun-kind sofun w) 'plain)))

(defabbrev choice-sofunp (sofun w)
  (and (sofunp sofun w)
       (eq (sofun-kind sofun w) 'choice)))

(defabbrev quant-sofunp (sofun w)
  (and (sofunp sofun w)
       (eq (sofun-kind sofun w) 'quant)))

(define sofun-fparams (sofun (w plist-worldp))
  :guard (sofunp sofun w)
  (let ((table (table-alist 'second-order-functions w)))
    (second (cdr (assoc-eq sofun table)))))

(define sofun-bound-vars (sofun (w plist-worldp))
  :guard (or (choice-sofunp sofun w)
             (quant-sofunp sofun w))
  (let ((table (table-alist 'second-order-functions w)))
    (third (cdr (assoc-eq sofun table)))))

(define sofun-quantifier (sofun (w plist-worldp))
  :guard (quant-sofunp sofun w)
  (let ((table (table-alist 'second-order-functions w)))
    (fourth (cdr (assoc-eq sofun table)))))

(define sofun-qrewrite-kind (sofun (w plist-worldp))
  :guard (quant-sofunp sofun w)
  (let ((table (table-alist 'second-order-functions w)))
    (fifth (cdr (assoc-eq sofun table)))))

; A DEFUN-SK introduces a rewrite rule for the function FUN being defined,
; namely the FUN-NECC (for FORALL) or FUN-SUFF (for EXISTS) theorem.
; These are the default names,
; but they may be changed using the :THM-NAME option of DEFUN-SK.
; However, currently SOFT does not support the :THM-NAME option (see below),
; and so the names are always the default ones.

(defun defun-sk-rewrite-rule-name (fun quant)
  (declare (xargs :guard (and (symbolp fun)
                              (quantifierp quant))))
  (let* ((fun-name (symbol-name fun))
         (suffix (case quant (forall "-NECC") (exists "-SUFF")))
         (rule-name (string-append fun-name suffix)))
    (intern-in-package-of-symbol rule-name fun)))

; A term may reference a function variable directly
; (when the function variable occurs in the term)
; or indirectly
; (when the function variable
; is a parameter of a second-order function that occurs in the term).
; The following code returns
; a list of the function variables referenced by a term
; (the list may contain duplicates).

(defines funvars-of-term/terms

  (define funvars-of-term ((term pseudo-termp) (w plist-worldp))
    (if (or (variablep term)
            (quotep term))
        nil ; no function variables in individual variables and constants
      (let* ((fn (fn-symb term))
             (fn-vars ; function variables in FN
              (if (flambdap fn)
                  (funvars-of-term (lambda-body fn) w)
                (if (funvarp fn w)
                    (list fn)
                  (if (sofunp fn w)
                      (sofun-fparams fn w)
                    nil))))) ; is a 1st-order function
        (append fn-vars (funvars-of-terms (fargs term) w)))))

  (define funvars-of-terms ((terms pseudo-term-listp) (w plist-worldp))
    (if (endp terms)
        nil
      (append (funvars-of-term (car terms) w)
              (funvars-of-terms (cdr terms) w)))))

; Plain and quantifier second-order functions and their instances
; may reference function variables
; in their defining bodies,
; in their measures (absent in quantifier functions),
; and in their guards (which are introduced via :WITNESS-DCLS for DEFUN-SK).
; For now recursive second-order functions (which are all plain)
; and their instances
; are only allowed to use O< as their well-founded relation,
; and so plain second-order functions and their instances
; may not reference function variables in their well-founded relations.

(define funvars-of-defun ((fun symbolp) (w plist-worldp))
  (let* ((body (body fun nil w))
         (measure (fmeasure fun w))
         (guard (fguard fun w))
         (body-funvars (funvars-of-term body w))
         (measure-funvars (funvars-of-term measure w)) ; NIL if no measure
         (guard-funvars (funvars-of-term guard w)))
    (append body-funvars
            measure-funvars
            guard-funvars)))

; Choice second-order functions and their instances
; may reference function variables in their defining bodies.

(define funvars-of-defchoose ((fun symbolp) (w plist-worldp))
  (funvars-of-term (defchoose-body fun w) w))

; Second-order theorems and their instances
; may reference function variables in their formulas.

(define funvars-of-defthm ((thm symbolp) (w plist-worldp))
  (funvars-of-term (tformula thm w) w))

; When a second-order function, or an instance thereof, is introduced,
; its function parameters must be
; all and only the function variables that the function depends on.
; A first-order instance of a second-order function,
; which has no function parameters,
; must depend on no function variables.

(define check-fparams-dependency
  ((fun symbolp)
   (kind sofun-kindp) ; kind of 2nd-order function of which FUN is an instance
   fparams
   (w plist-worldp))
  :guard (or (funvar-setp fparams w) ; if FUN is 2nd-order
             (null fparams))         ; if FUN is 1st-order
  (let ((funvars (case kind
                   (plain (funvars-of-defun fun w))
                   (choice (funvars-of-defchoose fun w))
                   (quant (funvars-of-defun fun w)))))
    (cond ((set-equiv funvars fparams) t)
          (fparams ; FUN is 2nd-order
           (raise "~x0 must depend on exactly its function parameters ~x1, ~
                   but depends on ~x2 instead.~%"
                  fun fparams funvars))
          (t ; FUN is 1st-order
           (raise "~x0 must depend on no function parameters, ~
                   but depens on ~x1 instead.~%"
                  fun funvars)))))

; When a recursive second-order function (which is always plain) is introduced,
; its well-founded relation must be O< for now
; (see the possible improvements/extensions at the end of this file).

(define check-wfrel-o< ((fun symbolp) (w plist-worldp))
  (let ((wfrel (wfrel fun w)))
    (cond ((null wfrel) t) ; FUN is not recursive
          ((eq wfrel 'o<) t)
          (t (raise "~x0 must use O< as well-founded relation, not ~x1.~%"
                    fun wfrel)))))

; When a quantifier second-order function, or an instance thereof,
; is introduced with a custom rewrite rule in :REWRITE,
; the custom rewrite rule must have the same function variables
; as the matrix (or body) of the function.

(define check-qrewrite-rule-funvars
  ((fun symbolp) (quant quantifierp) (w plist-worldp))
  (let* ((rule-name (defun-sk-rewrite-rule-name fun quant))
         (rule-body (tformula rule-name w))
         (fun-body (body fun nil w)))
    (set-equiv (funvars-of-term rule-body w)
               (funvars-of-term fun-body w))))

; The macro DEFUN2 introduces a plain second-order function.
; DEFUN2 has the form
;   (DEFUN2 SOFUN (FVAR1 ... FVARn) (VAR1 ... VARm)
;     DOC-STRING
;     DCL ... DCL
;     BODY)
; where SOFUN is the name of the function,
; (FVAR1 ... FVARn) is a non-empty list without duplicates of function variables
; that are the functions parameters (whose order is immaterial),
; (VAR1 ... VARm) are the individual parameters as in DEFUN,
; the optional documentation string DOC-STRING is as in DEFUN,
; the optional DCL ... DCL are declarations as in DEFUN
; such that :MODE :PROGRAM does not appear in any XARGS declaration,
; and BODY is the defining body as in DEFUN.
;
; DEFUN2 generates a DEFUN event via DEFINE,
; updates the table of second-order functions,
; and checks that the supplied function variables are
; all and only the ones that the new function depends on.
; If the new function is recursive,
; it also checks that the well-founded relation is O<.
;
; DEFUN2 sets the :T-PROOF option of DEFINE to T,
; in order to introduce an explicit termination theorem
; (if the function is recursive).
; :BOGUS-DEFUN-HINTS-OK is set to T just before the DEFINE,
; so that if the function is not recursive
; the :T-PROOF option does not cause an error
; (checking whether the function is recursive before submitting it to ACL2
; would involve parsing, expanding macros, etc.,
; to see if the function is called in the body;
; this is avoided by setting :BOGUS-DEFUN-HINTS-OK to T);
; :BOGUS-DEFUN-HINTS-OK is restored to its previous value just after DEFINE.
;
; DEFUN2 sets the :NO-FUNCTION option of DEFINE to T,
; to prevent DEFINE from wrapping the function body
; with a LET binding of __FUNCTION__ to the name of the function.
;
; DEFUN2 sets the :ENABLED option of DEFINE to T
; to leave the new function enabled after the DEFUN2,
; matching the behavior of DEFUN.
;
; DEFUN2 directly checks the name and the function parameters,
; but relies on DEFINE to check the rest of the form
; (individual parameters,
; optional documentation string,
; optional declarations,
; and body).
; Since DEFINE accepts richer forms than DEFUN,
; it may be possible to use, without an immediate error,
; correspondingly richer forms of DEFUN2
; than just adding the function parameters to DEFUN,
; but this is currently not supported by SOFT,
; i.e. the behavior is undefined from the perspective of SOFT.

(define defun2-event (sofun fparams rest (w plist-worldp))
  (b* (((unless (symbolp sofun))
        (raise "~x0 must be a name." sofun))
       ((unless (funvar-setp fparams w))
        (raise "~x0 must be a non-empty list of function variables ~
                 without duplicates."
               fparams))
       (info (list 'plain fparams))
       (bogus-defun-hints-ok (get-bogus-defun-hints-ok w)))
      `(progn
         (set-bogus-defun-hints-ok t)
         (define ,sofun ,@rest :t-proof t :no-function t :enabled t)
         (set-bogus-defun-hints-ok ,bogus-defun-hints-ok)
         (table second-order-functions ',sofun ',info)
         (value-triple (and (check-wfrel-o< ',sofun (w state))
                            (check-fparams-dependency ',sofun
                                                      'plain
                                                      ',fparams
                                                      (w state)))))))

(defmacro defun2 (sofun fparams &rest rest)
  `(make-event (defun2-event ',sofun ',fparams ',rest (w state))))

(defmacro show-defun2 (sofun fparams &rest rest)
  `(defun2-event ',sofun ',fparams ',rest (w state)))

; The name of the termination theorem of a recursive second-order function
; is obtained by adding -T to the name of the function.

(define sofun-termination-theorem-name ((sofun symbolp))
  (let* ((sofun-name (symbol-name sofun))
         (theorem-name (string-append sofun-name "-T")))
    (intern-in-package-of-symbol theorem-name sofun)))

; The macro DEFCHOOSE2 introduces a choice second-order function.
; DEFCHOOSE2 has the form
;   (DEFCHOOSE2 SOFUN (BVAR1 ... BVARm) (FVAR1 ... FVARn) (VAR1 ... VARp)
;     BODY
;     :STRENGTHEN ...
;     :DOC ...)
; where SOFUN is the name of the function
; (BVAR1 ... BVARm) are the bound variables as in DEFCHOOSE,
; (FVAR1 ... FVARn) is a non-empty list without duplicates of function variables
; that are the functions parameters (whose order is immaterial),
; (VAR1 ... VARp) are the individual parameters as in DEFCHOOSE,
; BODY is the body as in DEFCHOOSE,
; and the keyed options are the same as in DEFCHOOSE.
;
; DEFCHOOSE2 generates a DEFCHOOSE event,
; updates the table of second-order functions,
; and checks that the supplied function variables are
; all and only the ones that the new function depends on.
;
; DEFCHOOSE2 directly checks
; the name, bound variables, and function parameters,
; but relies on DEFCHOOSE to check the rest of the form
; (individual parameters, body, and keyed options).

(define defchoose2-event
  (sofun bvars fparams params body options (w plist-worldp))
  (b* (((unless (symbolp sofun))
        (raise "~x0 must be a name." sofun))
       ((unless (or (symbolp bvars)
                    (symbol-listp bvars)))
        (raise "~x0 must be one or more bound variables." bvars))
       ((unless (funvar-setp fparams w))
        (raise "~x0 must be a non-empty list of function variables ~
                without duplicates."
               fparams))
       (info (list 'choice fparams (if (symbolp bvars) (list bvars) bvars))))
      `(progn
         (defchoose ,sofun ,bvars ,params ,body ,@options)
         (table second-order-functions ',sofun ',info)
         (value-triple (check-fparams-dependency ',sofun
                                                 'choice
                                                 ',fparams
                                                 (w state))))))

(defmacro defchoose2 (sofun bvars fparams vars body &rest options)
  `(make-event
    (defchoose2-event
      ',sofun ',bvars ',fparams ',vars ',body ',options (w state))))

(defmacro show-defchoose2 (sofun bvars fparams vars body &rest options)
  `(defchoose2-event
     ',sofun ',bvars ',fparams ',vars ',body ',options (w state)))

; The macro DEFUN-SK2 introduces a quantifier second-order function.
; DEFUN-SK2 has the form
;   (DEFUN-SK2 SOFUN (FVAR1 ... FVARn) (VAR1 ... VARm)
;     BODY
;     :STRENGTHEN ...
;     :DOC ...
;     :QUANT-OK ...
;     :WITNESS-DCLS ...
;     :SKOLEM-NAME ...
;     :REWRITE ...)
; where SOFUN is the name of the function,
; (FVAR1 ... FVARn) is a non-empty list without duplicates of function variables
; that are the functions parameters whose order is immaterial,
; (VAR1 ... VARm) are the individual parameters as in DEFUN-SK,
; BODY is the body as in DEFUN-SK,
; and the keyed options are the same as in DEFUN-SK.
; The keyed option :THM-NAME of DEFUN-SK is currently not supported by SOFT.
;
; DEFUN-SK2 generates a DEFUN-SK event,
; updates the table of second-order functions,
; checks that the supplied function variables are
; all and only the ones that the new function depends on,
; and checks that the rewrite rule has
; the same function variables as the function body.
; The last check is redundant unless a custom rewrite rule
; is supplied via :REWRITE.
;
; DEFUN-SK2 directly checks
; the name, function parameters, individual parameters,
; and top-level structure of the body
; (it checks that the body has the form (FORALL/EXISTS BOUND-VAR(S) ...)),
; but relies on DEFUN-SK to check the keyed options and the matrix of the body.

(define defun-sk2-event (sofun fparams params body options (w plist-worldp))
  (b* (((unless (symbolp sofun))
        (raise "~x0 must be a name." sofun))
       ((unless (funvar-setp fparams w))
        (raise "~x0 must be a non-empty list of function variables ~
                without duplicates."
               fparams))
       ((unless (symbol-listp params))
        (raise "~x0 must be a list of symbols." params))
       ((unless (and (consp body)
                     (= (len body) 3)
                     (quantifierp (first body))
                     (or (symbolp (second body))
                         (symbol-listp (second body)))))
        (raise "~x0 must be a quantified formula." body))
       ((unless (keyword-value-listp options))
        (raise "~x0 must be a list of keyed options." options))
       (quant (first body))
       (bvars (second body))
       (bvars (if (symbolp bvars) (list bvars) bvars))
       (rewrite (cadr (assoc-keyword :rewrite options)))
       (qrkind (if rewrite
                   (case rewrite
                     (:default 'default)
                     (:direct 'direct)
                     (otherwise 'term))
                 'default))
       (info (list 'quant fparams bvars quant qrkind)))
      `(progn
         (defun-sk ,sofun ,params ,body ,@options)
         (table second-order-functions ',sofun ',info)
         (value-triple (check-fparams-dependency ',sofun
                                                 'quant
                                                 ',fparams
                                                 (w state)))
         (value-triple (check-qrewrite-rule-funvars ',sofun
                                                    ',quant
                                                    (w state))))))

(defmacro defun-sk2 (sofun fparams params body &rest options)
  `(make-event
    (defun-sk2-event ',sofun ',fparams ',params ',body ',options (w state))))

(defmacro show-defun-sk2 (sofun fparams params body &rest options)
  `(defun-sk2-event ',sofun ',fparams ',params ',body ',options (w state)))

; A theorem may reference function variables in its formula.

(define funvars-of-theorem ((thm symbolp) (w plist-worldp))
  (funvars-of-term (tformula thm w) w))

; A second-order theorem is mimicked by a (first-order) theorem
; that depends on one or more function variables,
; over which the second-order theorem is universally quantified.
; A theorem is second-order iff it depends on one or more function variables.

(define sothmp ((sothm symbolp) (w plist-worldp))
  (not (null (funvars-of-theorem sothm w))))

; When a second-order function or theorem is instantiated,
; certain function names are replaced with other function names,
; similarly to functional instantiation in ACL2's.
; A function substitution is an alist with unique keys
; that maps function names to function names
; and without trivial pairs (e.g. pairs whose key is the same as the value).

(define no-trivial-pairsp ((alist alistp))
  (if (endp alist)
      t
    (let ((pair (car alist)))
      (and (not (equal (car pair) (cdr pair)))
           (no-trivial-pairsp (cdr alist))))))

(define fun-substp (fsbs)
  (and (symbol-alistp fsbs)
       (symbol-listp (alist-vals fsbs))
       (no-duplicatesp (alist-keys fsbs))
       (no-trivial-pairsp fsbs)))

; A second-order function or theorem is instantiated
; by replacing (some of) its function variables
; with other function variables,
; with first-order functions,
; or with other second-order functions.
; A (function variable) instantiation is
; a non-empty function substitution
; whose keys are all function variables
; and whose values are all function symbols.

(define funvar-instp (inst (w plist-worldp))
  (and (fun-substp inst)
       inst
       (funvar-listp (alist-keys inst) w)
       (function-symbol-listp (alist-vals inst) w)))

(define funvar-inst-listp (insts (w plist-worldp))
  (if (atom insts)
      (null insts)
    (and (funvar-instp (car insts) w)
         (funvar-inst-listp (cdr insts) w))))

; Instantiating a second-order function yields
; another second-order function
; (if the result still depends on function variables)
; or a first-order function
; (if the result no longer depends on any function variable).
; All the known instances of a second-order function
; are represented by a map from instantiations
; to names of the function instances.
; This map is represented as an alist,
; accessed by treating instantiations equivalent according to ALIST-EQUIV.

(define sof-instancesp (instmap (w plist-worldp))
  (and (alistp instmap)
       (funvar-inst-listp (alist-keys instmap) w)
       (symbol-listp (alist-vals instmap))))

(define get-sof-instance ; read from map (NIL if absent)
  (inst instmap (w plist-worldp))
  :guard (and (funvar-instp inst w)
              (sof-instancesp instmap w))
  (if (endp instmap)
      nil
    (let ((pair (car instmap)))
      (if (alist-equiv (car pair) inst)
          (cdr pair)
        (get-sof-instance inst (cdr instmap) w)))))

(define put-sof-instance ; add to map
  (inst (fun symbolp) instmap (w plist-worldp))
  :guard (and (funvar-instp inst w)
              (sof-instancesp instmap w)
              ;; must not be already in map:
              (null (get-sof-instance inst instmap w)))
  (declare (ignore w)) ; only used in guard
  (acons inst fun instmap))

; A table maps second-order functions to their instances.
; Only second-order functions with instances appear in the table.

(table sof-instances nil nil :guard (and (symbolp key) ; name
                                         (sof-instancesp val world)))

(define sof-instances ; instances of SOFUN (NIL if none)
  (sofun (w plist-worldp))
  :guard (sofunp sofun w)
  (let ((table (table-alist 'sof-instances w)))
    (cdr (assoc-eq sofun table))))

; Applying an instantiation to a term involves replacing
; not only the function variables that are keys of the instantiation
; and that occur explicitly in the term,
; but also the ones that occur implicitly in the term
; via occurrences of second-order functions that have
; those function variables as parameters.
; For example, if FF is a second-order function with function parameter F,
; and an instantiation I replaces F with G,
; applying I to the term (CONS (F X) (FF Y))
; should yield the term (CONS (G X) (GG Y)),
; where GG is the instance that results form applying I to FF.
; The table of second-order function instances of FF is used to find GG;
; I is restricted to the function parameters of FF
; before searching the table;
; if the restriction is empty, GG is FF (i.e. no replacement takes place).
; If GG does not exist,
; the application of I to (CONS (F X) (FF Y)) fails;
; the user must create GG
; and try applying I to (CONS (F X) (FF Y)) again.
;
; When an instantiation is applied
; to the body of a recursive second-order function SOFUN
; to obtain an instance SOFUN,
; occurrences of SOFUN in the body must be replaced with FUN,
; but at that time FUN does not exist yet,
; and thus the table of second-order function instances of SOFUN
; has no entries for FUN yet.
; Thus, it is convenient to use function substitutions (not just instantiation)
; to instantiate terms.

(define fun-subst-function
  ((fsbs fun-substp) (fun symbolp) (w plist-worldp))
  (let ((pair (assoc-eq fun fsbs)))
    (if pair ; FUN is a key of FSBS
        (cdr pair)
      (if (sofunp fun w)
          (let* ((fparams (sofun-fparams fun w))
                 (subfsbs (restrict-alist fparams fsbs)))
            (if (null subfsbs) ; FUN does not depend on keys of FSBS
                fun
              (let* ((instmap (sof-instances fun w))
                     (new-fun (get-sof-instance subfsbs instmap w)))
                (if new-fun ; instance of FUN exists
                    new-fun
                  (raise "~x0 has no instance for ~x1."
                              fun fsbs)))))
        fun)))) ; FUN is a function variable or 1st-order function

(defines fun-subst-term/terms

  (define fun-subst-term
    ((fsbs fun-substp) (term pseudo-termp) (w plist-worldp))
    (if (or (variablep term)
            (quotep term))
        term ; no change to individual variables and constants
      (let* ((fn (fn-symb term))
             ;; apply substitution to FN:
             (new-fn (if (symbolp fn)
                         (fun-subst-function fsbs fn w)
                       (make-lambda (lambda-formals fn)
                                    (fun-subst-term fsbs
                                                    (lambda-body fn)
                                                    w))))
             ;; apply substitution to arguments:
             (new-args (fun-subst-terms fsbs (fargs term) w)))
        (cons new-fn new-args))))

  (define fun-subst-terms
    ((fsbs fun-substp) (terms pseudo-term-listp) (w plist-worldp))
    (if (endp terms)
        nil
      (cons (fun-subst-term fsbs (car terms) w)
            (fun-subst-terms fsbs (cdr terms) w)))))

; An instance THM of a second-order theorem SOTHM is also a theorem,
; provable using a :FUNCTIONAL-INSTANCE of SOTHM.
; The pairs of the :FUNCTIONAL-INSTANCE are
; not only the pairs of the instantiation that determines THM from SOTHM,
; but also all the pairs
; whose first components are second-order functions that SOTHM depends on
; and whose second components are the corresponding instances.
;
; For example,
; if SOTHM is (P (SOFUN X)),
; SOFUN is a second-order function,
; P is a first-order predicate,
; and applying I to (P (SOFUN X)) yields (P (FUN X)),
; then THM is proved using (:FUNCTIONAL-INSTANCE SOTHM (... (SOFUN FUN) ...)),
; where the first ... are the pairs of I
; and the second ... are further pairs of second-order functions and instances,
; e.g. if the definition of SOFUN references a second-order function SOFUN',
; the pair (SOFUN' FUN') must be in the second ...,
; where FUN' is the instance of SOFUN' corresponding to I.
; All these pairs are needed to properly instantiate
; the constraints that arise from the :FUNCTIONAL-INSTANCE,
; which involve the second-order functions that SOTHM depends on,
; directly or indirectly.
;
; The following code extends a function substitution
; (initially an instantiation)
; to contains all those extra pairs.
; The starting point is a term;
; the bodies of second-order functions referenced in the term
; are recursively processed.
; The table of instances of second-order functions is searched,
; similarly to the code that applies a function substitution to a term.

(defines ext-fun-subst-term/terms/function
  :mode :program ; termination needs ACL2 world invariants

  (define ext-fun-subst-term
    ((term pseudo-termp) (fsbs fun-substp) (w plist-worldp))
    (if (or (variablep term)
            (quotep term))
        fsbs ; no 2nd-order functions in individual variables and constants
      (let* ((fn (fn-symb term))
             (fsbs (if (symbolp fn)
                       (ext-fun-subst-function fn fsbs w)
                     (ext-fun-subst-term (lambda-body fn) fsbs w))))
        (ext-fun-subst-terms (fargs term) fsbs w))))

  (define ext-fun-subst-terms
    ((terms pseudo-term-listp) (fsbs fun-substp) (w plist-worldp))
    (if (endp terms)
        fsbs
      (let ((fsbs (ext-fun-subst-term (car terms) fsbs w)))
        (ext-fun-subst-terms (cdr terms) fsbs w))))

  (define ext-fun-subst-function
    ((fun symbolp) (fsbs fun-substp) (w plist-worldp))
    (cond
     ((assoc fun fsbs) fsbs) ; pair already present
     ((sofunp fun w)
      (b* ((fparams (sofun-fparams fun w))
           (subfsbs (restrict-alist fparams fsbs))
           ((if (null subfsbs)) fsbs) ; FUN unchanged under FSBS
           (instmap (sof-instances fun w))
           (funinst (get-sof-instance subfsbs instmap w))
           ((unless funinst)
            (raise "~x0 has no instance for ~x1." fun fsbs))
           (fsbs (acons fun funinst fsbs))) ; extend FSBS
          (case (sofun-kind fun w)
            (plain (ext-fun-subst-term (body fun nil w) fsbs w))
            (choice (ext-fun-subst-term (defchoose-body fun w) fsbs w))
            (quant
             (let* ((fsbs (ext-fun-subst-term (body fun nil w) fsbs w))
                    ;; the 2nd-order functions in the matrix of FUN
                    ;; are the same as in the rewrite rule of FUN:
                    (quant (sofun-quantifier fun w))
                    (body (tformula (defun-sk-rewrite-rule-name fun quant) w)))
               (ext-fun-subst-term body fsbs w))))))
     (t fsbs)))) ; FUN is not a 2nd-order function

; From a function substitution obtained by extending an instantiation as above,
; the list of pairs to supply to :FUNCTIONAL-INSTANCE is obtained.
; Each dotted pair is turned into a list of length 2
; (a different representation of the pair).
; In addition, when a dotted pair is encountered
; whose CAR is the name of a quantifier second-order function,
; an extra pair for instantiating the associated witness is inserted.
; The witness of a function introduced with DEFUN-SK is
; the CONSTRAINT-LST property of the function.
;
; The witnesses of quantifier second-order functions
; must also be part of the :FUNCTIONAL-INSTANCE,
; because they are referenced by the quantifier second-order functions.
; However, these witnesses are not recorded as second-order functions
; in the table of second-order functions,
; and thus the code above
; that extends an instantiation to a function substitution
; does not catch these witnesses.

(define sothm-inst-pairs ((fsbs fun-substp) (w plist-worldp))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (if (quant-sofunp 1st w)
          (let ((1st-wit (defun-sk-witness-name 1st w))
                (2nd-wit (defun-sk-witness-name 2nd w)))
            (cons (list 1st 2nd) ; pair from FSBS
                  (cons (list 1st-wit 2nd-wit) ; pair of witnesses
                        (sothm-inst-pairs (cdr fsbs) w))))
        (cons (list 1st 2nd) ; pair from FSBS
              (sothm-inst-pairs (cdr fsbs) w))))))

; When a :FUNCTIONAL-INSTANCE is used in a proof,
; proof subgoals are created to ensure that the replacing functions
; satisfy all the constraints of the replaced functions.
; In the :FUNCTIONAL-INSTANCE with the function substitution S as above,
; each function variable (which comes from the instantiation) has no constraints
; and so no subgoals are generated for them.
; Each second-order function SOFUN in S has the following constraints:
; - If SOFUN is a plain second-order function,
;   the constraint is that
;   the application of S to the definition of SOFUN is a theorem,
;   which follows by the construction of the instance FUN of SOFUN,
;   i.e. it follows from the definition of FUN.
; - If SOFUN is a choice second-order function,
;   the constraint is that
;   the application of S to the choice axiom of SOFUN is a theorem,
;   which follows by the construction of the instance FUN of SOFUN,
;   i.e. it follows from the choice axiom of FUN.
; - If SOFUN is a quantifier second-order function,
;   the constraints are that
;   (1) the application of S
;   to the rewrite rule generated by the DEFUN-SK of SOFUN,
;   and (2) the application of S to the definition of SOFUN,
;   are both theorems,
;   which both follow by the construction of the instance FUN of SOFUN,
;   i.e. they follow from
;   (1) the rewrite rule generated by the DEFUN-SK of FUN
;   and (2) the definition of FUN.
; The list of facts needed to prove these constraints is determined
; by the function substitution S.
; For each pair (FUN1 . FUN2) of the function substitution:
; - If FUN1 is a plain second-order function,
;   the fact used in the the proof is the definition of FUN2
;   (by construction, since FUN2 is an instance of FUN1,
;   FUN2 is introduced by a DEFUN, via a DEFINE),
;   whose name is the name of FUN2.
; - If FUN1 is a choice second-order function,
;   the fact used in the proof is the DEFCHOOSE axiom of FUN2
;   (by construction, since FUN2 is an instance of FUN1,
;   FUN2 is introduced by a DEFCHOOSE),
;   whose name is the name of FUN2.
; - If FUN1 is a quantifier second-order function,
;   the fact used in the proof is the DEFUN-SK rewrite rule of FUN2
;   (by construction, since FUN2 is an instance of FUN1,
;   FUN2 is introduced by a DEFUN-SK).
; - Otherwise, FUN1 is a function variable, which has no constraints,
;   so no fact is used in the proof.

(define sothm-inst-facts ((fsbs fun-substp) (w plist-worldp))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (cond ((or (plain-sofunp 1st w)
                 (choice-sofunp 1st w))
             (cons 2nd (sothm-inst-facts (cdr fsbs) w)))
            ((quant-sofunp 1st w)
             (cons (defun-sk-rewrite-rule-name 2nd (sofun-quantifier 1st w))
                   (sothm-inst-facts (cdr fsbs) w)))
            (t (sothm-inst-facts (cdr fsbs) w))))))

; Instances of second-order theorems are proved using the ACL2 proof checker.
; Each such instance is proved by
; first using the :FUNCTIONAL-INSTANCE described above,
; then using the facts described above on the subgoals.
; Each sugoal only needs a subset of those facts,
; but for simplicity all the facts are used for each subgoal,
; using the proof checker :REPEAT command.
; Since sometimes the facts are not quite identical to the subgoals,
; the proof checker :PROVE command is used to iron out any such differences.

(define sothm-inst-proof
  ((sothm symbolp) (fsbs fun-substp) (w plist-worldp))
  `(:instructions
    ((:use (:functional-instance ,sothm ,@(sothm-inst-pairs fsbs w)))
     (:repeat (:then (:use ,@(sothm-inst-facts fsbs w)) :prove)))))

; The macro DEFTHM-INST introduces an instance of a second-order theorem.
; DEFTHM-INST has the form
;   (DEFTHM-INST THM
;     (SOTHM (F1 . G1) ... (Fm . Gm))
;     :RULE-CLASSES ...)
; where THM is the name of the theorem instance,
; SOTHM is the second-order theorem being instantiated,
; ((F1 . G1) ... (Fn . Gn)) is the instantiation that defines THM,
; and the optional :RULE-CLASSES is as in DEFTHM.
;
; DEFTHM-INST checks that each Fi is
; a function variable on which SOTHM depends.
;
; DEFTHM-INST generates a DEFTHM event
; whose formula is obtained by applying the instantiation to SOTHM;
; the theorem is proved by functional instantiation as explained earlier.
;
; DEFTHM-INST directly checks the form
; except for the :RULE-CLASSES option,
; relying on DEFTHM to check it.
; Supplying :HINTS causes an error because DEFTHM does not allow
; both :HINTS and :INSTRUCTIONS.
; Supplying :OTF-FLG has no effect because the proof is via the proof checker.
; Supplying :DOC just attaches a documentation string to THM,
; but generally documentation should be attached
; to second-order theorems introduced via DEFTHM2,
; and not to their instances.

; check that SOTHM-INST has the form (SOTHM (F1 . G1) ... (Fm . Gm)),
; where SOTHM is a 2nd-order theorem
; and ((F1 . G1) ... (Fm . Gm)) is an instantiation:
(define check-sothm-inst (sothm-inst (w plist-worldp))
  (and (true-listp sothm-inst)
       (>= (len sothm-inst) 2)
       (sothmp (car sothm-inst) w)
       (funvar-instp (cdr sothm-inst) w)))

(define defthm-inst-event (thm sothm-inst rest (w plist-worldp))
  :mode :program ; calls EXT-FUN-SUBST-TERM
  (b* (;; THM is the name of the new theorem:
       ((unless (symbolp thm)) (raise "~x0 must be a name." thm))
       ;; after THM there is (SOTHM (F1 . G1) ... (Fm . Gm)):
       ((unless (check-sothm-inst sothm-inst w))
        (raise "~x0 must be the name of a second-order theorem ~
                followed by the pairs of an instantiation."
               sothm-inst))
       ;; decompose (SOTHM (F1 . G1) ... (Fm . Gm)):
       (sothm (car sothm-inst))
       (inst (cdr sothm-inst))
       ;; every Fi must be a function variable that SOTHM depends on:
       ((unless (subsetp (alist-keys inst) (funvars-of-theorem sothm w)))
        (raise "Each function variable key of ~x0 must be ~
                among function variable that ~x1 depends on."
               inst sothm))
       ;; apply ((F1 . G1) ... (Fm . Gm)) to the formula of SOTHM:
       (sothm-formula (tformula sothm w))
       (thm-formula (fun-subst-term inst sothm-formula w))
       ;; construct the proof from the instantiation:
       (fsbs (ext-fun-subst-term sothm-formula inst w))
       (thm-proof (sothm-inst-proof sothm fsbs w)))
      ;; generate event (REST is RULE-CLASSES, if present):
      `(defthm ,thm ,thm-formula ,@thm-proof ,@rest)))

(defmacro defthm-inst (thm uqfvars-or-sothminst &rest rest)
  `(make-event
    (defthm-inst-event ',thm ',uqfvars-or-sothminst ',rest (w state))))

(defmacro show-defthm-inst (thm uqfvars-or-sothminst &rest rest)
  `(defthm-inst-event ',thm ',uqfvars-or-sothminst ',rest (w state)))

; The macro DEFUN-INST introduces an instance of a second-order function.
; DEFUN-INST has the form
;   (DEFUN-INST FUN (FVAR1 ... FVARn)
;     (SOFUN (F1 . G1) ... (Fm . Gm))
;     :VERIFY-GUARDS ...
;     :SKOLEM-NAME ...
;     :REWRITE ...)
; where FUN is the name of the function instance,
; (FVAR1 ... FVARn) is an optional non-empty list without duplicates
; of function parameters of FUN (whose order is immaterial),
; SOFUN is the second-order function being instantiated,
; ((F1 . G1) ... (Fm . Gm)) is the instantiation that defines FUN,
; and the optional :VERIFY-GUARDS, :DOC, :SKOLEM-NAME, and :REWRITE
; are explained below.
;
; If (FVAR1 ... FVARn) is present, FUN is a second-order function;
; otherwise, FUN is a first-order function.
; In the first case, DEFUN-INST checks that (FVAR1 ... FVARn) are
; all and only the function variables that FUN depends on;
; in the second case, DEFUN-INST checks that
; FUN does not depend on any function variables.
; In the first case, DEFUN-INST adds FUN to the table of second-order functions;
; in the second case, that table is left unchanged.
;
; DEFUN-INST adds FUN to the table of instances of SOFUN.
;
; (SOFUN (F1 . G1) ... (Fm . Gm)) resembles
; an "application" of SOFUN to G1 ... Gm in place of F1 ... Fm.
; This application is by the names F1 ... Fm, not positional,
; consistent with the treatment as a set
; of the list of function parameters in DEFUN2, DEFCHOOSE2, and DEFUN-SK2.
; DEFUN-INST checks that each Fi is a function parameter of SOFUN.
;
; DEFUN-INST generates a DEFUN, DEFCHOOSE, or DEFUN-SK event,
; depending on whether SOFUN is a plain, choice, or quantifier function.
; DEFUN-INST directly checks the form except for the options,
; relying on DEFINE, DEFCHOOSE, or DEFUN-SK to check them.
;
; If SOFUN is a plain second-order function, DEFUN-INST generates a DEFUN
; via a DEFINE.
; The body, measure, and guard of FUN
; are obtained by applying the instantiation
; to the body, measure, and guard of SOFUN.
; If a measure is present, it means that SOFUN and FUN are recursive.
; In this case, the termination of FUN
; follows by functional instantiation from the termination of SOFUN,
; in the same way as the proof of an instance of a second-order theorem
; follows by functional instantiation from the proof of the theorem.
; DEFUN-INST generates a :HINTS for the termination proof of the same form
; as the generated proof of an instance of a second-order theorem above.
;
; If FUN is second-order and recursive, the :T-PROOF option is used,
; so that the termination theorem of FUN can be later used
; to prove the termination of instances of FUN.
; Unlike DEFUN2, :BOGUS-DEFUN-HINTS-OK is not set to T and then restored,
; because DEFUN-INST generates the :T-PROOF option
; only if SOFUN and FUN are recursive.
; Similarly to DEFUN2, DEFUN-INST sets
; the :NO-FUNCTION and :ENABLED options of DEFINE to T.
; DEFUN-INST sets
; the :IGNORE-OK and :IRRELEVANT-FORMALS-OK options of DEFINE to T,
; in case SOFUN has IGNORE or IGNORABLE declarations.
;
; The :VERIFY-GUARDS option in DEFUN-INST can be used only if SOFUN is plain.
; Its meaning is the same as in DEFUN (or DEFINE).
; It is passed through as an option to DEFINE.
;
; Since DEFINE accepts more options than :VERIFY-GUARDS,
; it may be possible to supply, without an immediate error,
; more options than :VERIFY-GUARDS to DEFUN-INST when SOFUN is plain,
; but this is currently not supported by SOFT,
; i.e. the behavior is undefined from the perspective of SOFT.
;
; If SOFUN is a choice second-order function, DEFUN-INST generates a DEFCHOOSE.
; The body of FUN is obtained
; by applying the instantiation to the body of SOFUN.
; In the generated DEFCHOOSE,
; the :STRENGTHEN option is set to the same value as in the DEFCHOOSE of SOFUN.
;
; If SOFUN is a quantifier second-order function,
; DEFUN-INST generates a DEFUN-SK.
; The quantifier and bound variables of FUN are the same as SOFUN,
; and the matrix of FUN is obtained
; by applying the instantiation to the matrix of SOFUN.
; In the generated DEFUN-SK,
; the :STRENGTHEN option is set to the same value as in the DEFUN-SK of SOFUN.
; In the generated DEFUN-SK,
; the :QUANT-OK is set to T, in case it was set to T in the DEFUN-SK of SOFUN.
;
; The :SKOLEM-NAME and :REWRITE options in DEFUN-INST can be used
; only if SOFUN is a quantifier second-order function.
; Their meaning is the same as in DEFUN-SK,
; except that if :REWRITE is absent,
; it is inherited from SOFUN.
;
; Since DEFUN-SK accepts more options than :SKOLEM-NAME and :REWRITE,
; it may be possible to supply, without an immediate error,
; more options than :SKOLEM-NAME and :REWRITE to DEFUN-INST,
; when SOFUN is a quantifier second-order function,
; but this is currently not supported by SOFT,
; i.e. the behavior is undefined from the perspective of SOFT.
;
; If SOFUN is a quantifier second-order function,
; DEFUN-INST checks that the function variables in the rewrite rule
; are the same as the ones in the body,
; similary to DEFUN-SK2.
; This check is redundant unless a custom rewrite rule is supplied via :REWRITE.
;
; If SOFUN is a quantifier second-order function,
; DEFUN-INST applies the instantiation to the guard
; and uses the result as the guard of the generated DEFUN-SK,
; in the :WITNESS-DCLS option.
; As explained in the documentation of DEFUN-SK,
; guard verification typically fails if attempted with DEFUN-SK,
; making it necessary to defer guard verification.
; Thus, DEFUN-INST also generates :VERIFY-GUARDS NIL
; as part of the :WITNESS-DCLS option.
;
; For now, SOFT does not support the transitivity of instantiations,
; i.e. that if F is an instance of G and G is an instance of H,
; then F is also an instance of H.

; check that SOFUN-INST had the form (SOFUN (F1 . G1) ... (Fm . Gm)),
; where SOFUN is a 2nd-order function
; and ((F1 . G1) ... (Fm . Gm)) is an instantiation:
(define check-sofun-inst (sofun-inst (w plist-worldp))
  (and (true-listp sofun-inst)
       (>= (len sofun-inst) 2)
       (sofunp (car sofun-inst) w)
       (funvar-instp (cdr sofun-inst) w)))

; events to introduce FUN
; and to add it to the table of second-order functions if it is second-order,
; when SOFUN is a plain second-order function:
(define defun-inst-plain-events
  ((fun symbolp) fparams sofun inst (options true-listp) (w plist-worldp))
  :mode :program ; calls EXT-FUN-SUBST-TERM
  :guard (and (or (funvar-setp fparams w) ; FUN is 2nd-order
                  (null fparams))         ; FUN is 1st-order
              (plain-sofunp sofun w))
  (b* (;; retrieve body, measure, and guard of SOFUN:
       (sofun-body (body sofun nil w))
       (sofun-measure (fmeasure sofun w))
       (sofun-guard (fguard sofun w))
       ;; extend instantiation with (SOFUN . FUN) if SOFUN is recursive
       ;; (so that recursive calls to SOFUN can be properly replaced with FUN)
       ;; and apply it to the body of SOFUN:
       (fsbs (if sofun-measure (acons sofun fun inst) inst))
       (fun-body (fun-subst-term fsbs sofun-body w))
       ;; apply instantiation to the measure and guard of SOFUN:
       (fun-measure (fun-subst-term inst sofun-measure w))
       (fun-guard (fun-subst-term inst sofun-guard w))
       ;; construct the termination proof from the instantiation, if recursive:
       (sofun-tt-name (sofun-termination-theorem-name sofun))
       (sofun-tt-formula (tformula sofun-tt-name w)) ; could be NIL
       (fsbs (ext-fun-subst-term sofun-tt-formula inst w))
       (fun-tt-proof (sothm-inst-proof sofun-tt-name fsbs w))
       ;; :HINTS of FUN if recursive, otherwise NIL:
       (hints (if fun-measure `(:hints (("Goal" ,@fun-tt-proof))) nil))
       ;; :MEASURE of FUN if recursive, otherwise NIL:
       (measure (if fun-measure `(:measure ,fun-measure) nil))
       ;; :GUARD of FUN if guarded, otherwise NIL:
       (guard (if fun-guard `(:guard ,fun-guard) nil))
       ;; :T-PROOF option if FUN is recursive, otherwise NIL:
       (t-proof (if fun-measure '(:t-proof t) nil))
       ;; info about FUN to add to the table of second-order functions
       ;; (if FUN is second-order):
       (info (list 'plain fparams))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
      ;; generated list of events:
      `((define ,fun ,(formals sofun w)
          ,fun-body
          ,@measure
          ,@hints
          ,@guard
          ,@t-proof
          :no-function t
          :enabled t
          :ignore-ok t
          :irrelevant-formals-ok t
          ,@options)
        ,@table-event)))

; events to introduce FUN
; and to add it to the table of second-order functions if it second-order,
; when SOFUN is a choice second-order function:
(define defun-inst-choice-events
    ((fun symbolp) fparams sofun inst (options true-listp) (w plist-worldp))
  :guard (and (or (funvar-setp fparams w) ; FUN is 2nd-order
                  (null fparams))         ; FUN is 1st-order
              (choice-sofunp sofun w))
  (b* (;; retrieve bound variables of SOFUN:
       (bound-vars (sofun-bound-vars sofun w))
       ;; apply instantiation to body of SOFUN:
       (sofun-body (defchoose-body sofun w))
       (fun-body (fun-subst-term inst sofun-body w))
       ;; info about FUN to add to the table of second-order functions
       ;; (if FUN is second-order):
       (info (list 'choice fparams bound-vars))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
      ;; generated list of events:
      `((defchoose ,fun ,bound-vars ,(formals sofun w)
          ,fun-body
          :strengthen ,(defchoose-strongp sofun w)
          ,@options)
        ,@table-event)))

; events to introduce FUN
; and to add it to the table of second-order functions if it is second-order,
; when SOFUN is a quantifier second-order function:
(define defun-inst-quant-events
  ((fun symbolp) fparams sofun inst (options true-listp) (w plist-worldp))
  :guard (and (or (funvar-setp fparams w) ; FUN is 2nd-order
                  (null fparams))         ; FUN is 1st-order
              (quant-sofunp sofun w))
  (b* (;; retrieve bound variables and quantifier of SOFUN:
       (bound-vars (sofun-bound-vars sofun w))
       (1bvarp (= (len bound-vars) 1))
       (quant (sofun-quantifier sofun w))
       ;; apply instantiation to the matrix of SOFUN:
       (sofun-matrix (defun-sk-matrix sofun 1bvarp w))
       (fun-matrix (fun-subst-term inst sofun-matrix w))
       ;; the value of :REWRITE for FUN
       ;; is determined from the supplied value (if any),
       ;; otherwise it is inherited from SOFUN:
       (rewrite-supplied (cadr (assoc-keyword :rewrite options)))
       (rewrite (or rewrite-supplied
                    (let ((qrkind (sofun-qrewrite-kind sofun w)))
                      (case qrkind
                        (default :default)
                        (direct :direct)
                        (term
                         ;; apply instantiation to that term
                         ;; and use result as :REWRITE for FUN
                         ;; (the instantiation is extended with (SOFUN . FUN)
                         ;; because the term presumably references SOFUN):
                         (let* ((fsbs (acons sofun fun inst))
                                (rule-name (defun-sk-rewrite-rule-name
                                             sofun (sofun-quantifier sofun w)))
                                (term (tformula rule-name w)))
                           (fun-subst-term fsbs term w)))))))
       ;; kind of rewrite rule for FUN:
       (qrkind (case rewrite
                 (:default 'default)
                 (:direct 'direct)
                 (otherwise 'term)))
       ;; apply instantiation to the guard of SOFUN:
       (sofun-guard (fguard sofun w))
       (fun-guard (fun-subst-term inst sofun-guard w))
       ;; :WITNESS-DCLS for FUN:
       (wit-dcl `(declare (xargs :guard ,fun-guard :verify-guards nil)))
       ;; info about FUN to add to the table of second-order functions
       ;; (if FUN is second-order):
       (info (list 'quant fparams bound-vars quant qrkind))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
      ;; generated list of events:
      `((defun-sk ,fun ,(formals sofun w)
          (,quant ,bound-vars ,fun-matrix)
          :strengthen ,(defun-sk-strongp sofun w)
          :quant-ok t
          :rewrite ,rewrite
          :witness-dcls (,wit-dcl)
; Matt K. mod: avoid duplicate keywords.
          ,@(strip-keyword-list
             '(:strengthen :quant-ok :rewrite :witness-dcls)
             options))
        ,@table-event
        (value-triple (check-qrewrite-rule-funvars ',fun ',quant (w state))))))

(define defun-inst-event (fun fparams-or-sofuninst rest (w plist-worldp))
  :mode :program ; calls DEFUN-INST-PLAIN-EVENTS
  (b* (;; FUN is the name of the new function:
       ((unless (symbolp fun)) (raise "~x0 must be a name." fun))
       ;; after FUN there is (FVAR1 ... FVARn) if FUN is 2nd-order,
       ;; otherwise there is (SOFUN (F1 . G1) ... (Fm . Gm)):
       (2nd-order ; T if FUN is 2nd-order
        (funvar-setp fparams-or-sofuninst w))
       ((unless (or 2nd-order
                    (check-sofun-inst fparams-or-sofuninst w)))
        (raise "~x0 must be either a non-empty list of ~
                function variables without duplicates ~
                or the name of a second-order function ~
                followed by the pairs of an instantiation."
               fparams-or-sofuninst))
       ;; the function parameters are
       ;; FPARAMS-OR-SOFUNINST if FUN is 2nd-order,
       ;; otherwise there are no function parameters:
       (fparams (if 2nd-order fparams-or-sofuninst nil))
       ;; if FUN is 2nd-order, REST must be non-empty
       ;; and its first element must be (SOFUN (F1 . G1) ... (Fm . Gm)):
       ((unless (or (not 2nd-order)
                    (and (consp rest)
                         (check-sofun-inst (car rest) w))))
        (raise "~x0 must start with the name of a second-order function ~
                followed by an instantiation."
               rest))
       (sofun-inst (if 2nd-order (car rest) fparams-or-sofuninst))
       ;; decompose (SOFUN (F1 . G1) ... (Fm . Gm)):
       (sofun (car sofun-inst))
       (inst (cdr sofun-inst))
       ;; every Fi must be a function parameter of SOFUN:
       ((unless (subsetp (alist-keys inst) (sofun-fparams sofun w)))
        (raise "Each function variable key of ~x0 must be ~
                among the function parameters ~x1 of ~x2."
               inst (sofun-fparams sofun w) sofun))
       ;; the options are REST if FUN is 1st-order,
       ;; otherwise they come after (SOFUN (F1 . G1) ... (Fm . Gm)) in REST:
       (options (if 2nd-order (cdr rest) rest))
       ;; events specific to the kind of SOFUN:
       (spec-events
        (case (sofun-kind sofun w)
          (plain
           (defun-inst-plain-events fun fparams sofun inst options w))
          (choice
           (defun-inst-choice-events fun fparams sofun inst options w))
          (quant
           (defun-inst-quant-events fun fparams sofun inst options w))))
       ;; updated entry for SOFUN
       ;; in table of instances of second-order functions:
       (instmap (sof-instances sofun w))
       (new-instmap (put-sof-instance inst fun instmap w)))
      ;; generated event:
      `(progn
         ,@spec-events
         (table sof-instances ',sofun ',new-instmap)
         (value-triple (check-fparams-dependency ',fun
                                                 ',(sofun-kind sofun w)
                                                 ',fparams
                                                 (w state))))))

(defmacro defun-inst (fun fparams-or-sofuninst &rest rest)
  `(make-event
    (defun-inst-event ',fun ',fparams-or-sofuninst ',rest (w state))))

(defmacro show-defun-inst (fun fparams-or-sofuninst &rest rest)
  `(defun-inst-event ',fun ',fparams-or-sofuninst ',rest (w state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some possible improvements/extensions:
; - Generate instances of second-order functions and theorems
;   with untranslated terms, which are more user-readable.
; - Check that only the allowed options are used in each macro.
; - Support the transitivity of instantiation,
;   i.e. if F is an instance of G and G is an instance of H,
;   then F is also an instance of H.
; - Support more general types for function variables,
;   e.g. including multiple-value results and stobjs.
; - Support constrained function variables,
;   i.e. function variables that satisfy certain conditions.
; - Allow recursive second-order functions to use well-founded relations
;   other than O<, and possibly second-order well-founded relations.
; - Support the introduction of second-order functions
;   via macros that correspond to
;   DEFUND, DEFN, DEFND, DEFUN-NX, DEFUND-NX, DEFINE, DEFPUN, DEFP,
;   and MUTUAL-RECURSION.
; - Support the introduction of second-order theorems
;   via a macro that corresponds to DEFTHMD.
; - Support the :THM-NAME option in DEFUN-SK2,
;   and in DEFUN-INST when applied to a quantifier function.
; - Allow instantiations to map function variable names to LAMBDA terms,
;   similarly to :FUNCTIONAL-INSTANCE.
; - Provide facilities to use (by functional instantiation)
;   proved guards of second-order functions
;   to prove guards of instances of those second-order functions.
;   The instances may have more proof obligations
;   because function variables that have no obligations
;   may be replaced with functions that have obligations.
; - Provide facilities to trim guards of instances of second-order functions
;   by using proved theorems.
;   For instance, if the guard of a second-order function
;   includes a conjunct that uses a non-executable quantifier function
;   (e.g. expressing a condition on some function parameter),
;   but the instance of this conjunct is a theorem
;   (e.g. the first-order function that replaces that function parameter
;   satisfies the condition expressed by conjunct),
;   then that conjunct does not need to appear in the guard
;   of the instance of the second-order function,
;   making the guard executable and allowing the instance to run.
; - Currently the default :RULE-CLASSES
;   of an instance of a second-order theorem is (:REWRITE),
;   but perhaps the default should be the :RULE-CLASSES
;   of the second-order theorem that is being instantiated.
; - Support program-mode second-order functions.
