(in-package "ACL2")

; SOFT - Second-Order Functions and Theorems
;
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License (an MIT license):
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Alessandro Coglio (coglio@kestrel.edu)

; Overview:
;
;   This file contains SOFT ('Second-Order Functions and Theorems'),
;   a tool to mimic second-order functions and theorems
;   in the first-order logic of ACL2.
;
;   The code in this file is meant to be simple.
;   Its efficiency can be improved if needed.
;   The code is experimental and has undergone limited testing.
;   Some possible improvements/extensions are discussed at the end of the file.

(include-book "std/alists/top" :dir :system)
(include-book "tools/bstar" :dir :system)

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

(defun justification (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (getprop fun 'justification nil 'current-acl2-world world))

(defun wfrel (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (cddr (caddr (justification fun world))))

(defun measure (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (car (cadddr (justification fun world))))

; Logic-mode simplified version of the GUARD system utility.

(defun fguard (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (getprop fun 'guard *T* 'current-acl2-world world))

; Logic-mode simplified version of the FORMULA system utility.

(defun tformula (thm world)
  (declare (xargs :guard (and (symbolp thm)
                              (plist-worldp world))))
  (getprop thm 'theorem nil 'current-acl2-world world))

; Check that all the symbols in a list are names of functions.

(defun function-symbol-listp (syms world)
  (declare (xargs :guard (and (symbol-listp syms)
                              (plist-worldp world))))
  (if (endp syms)
      t
    (and (function-symbolp (car syms) world)
         (function-symbol-listp (cdr syms) world))))

; The body of a DEFCHOOSE can be extracted
; from the DEFCHOOSE-AXIOM property, which has one of the following forms:
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
; From the form of DEFCHOOSE-AXIOM the value of :STRENGTHEN can be determined.

(defun defchoose-axiom (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (getprop fun 'defchoose-axiom nil 'current-acl2-world world))

(defun defchoose-body (fun world)
  (declare (xargs :guard (and (plist-worldp world)
                              (defchoose-axiom fun world))))
  (let ((axiom (defchoose-axiom fun world)))
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

(defun defchoose-strongp (fun world) ; value of :STRENGTHEN
  (declare (xargs :guard (and (plist-worldp world)
                              (defchoose-axiom fun world))))
  (let ((axiom (defchoose-axiom fun world)))
    (and (eq (fn-symb axiom) 'if) ; not form 1
         (let ((if-test (fargn axiom 1)))
           (not (eq (fn-symb if-test) 'true-listp)))))) ; not form 2

; The quantified formula of a DEFUN-SK is in prenex normal form;
; the matrix of this prenex normal form is the term
; after the quantifier and bound variables.
; The matrix of a DEFUN-SK
; can be extracted from the defining body of the function
; (as returned by the BODY system utility),
; which has the form (RETURN-LAST ... ... CORE),
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
; whether the DEFUN-SK had either one or more than one bound variables:
; this information is passed to the following code
; in the form of a boolean flag that is true when there was one bound variable.

(defun defun-sk-matrix (fun 1bvarp world)
  (declare (xargs :guard (and (symbolp fun)
                              (booleanp 1bvarp)
                              (plist-worldp world))))
  (let* ((body (body fun nil world))
         (core (fargn body 3))
         (lamb (fn-symb core)))
    (if 1bvarp
        (lambda-body lamb) ; form 1
      (let* ((nested-app (lambda-body lamb))
             (nested-lamb (fn-symb nested-app)))
        (lambda-body nested-lamb)))))

; The name of the witness of a function introduced via DEFUN-SK
; is the CONSTRAINT-LST of the function.

(defun defun-sk-witness-name (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (getprop fun 'constraint-lst nil 'current-acl2-world world))

; To determine whethe a DEFUN-SK is introduced with :STRENGTHEN set to T or not,
; the CONSTRAINT-LST of the witness can be inspected:
; if it has 3 constraints, :STRENGTHEN was T;
; if it has 2 constraints, :STRENGTHEN was NIL.

(defun defun-sk-strongp (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (let* ((witness (defun-sk-witness-name fun world))
         (constraint-lst
          (getprop witness 'constraint-lst nil 'current-acl2-world world)))
    (= (len constraint-lst) 3)))

; The :BOGUS-DEFUN-HINTS-OK setting is in the ACL2-DEFAULTS-TABLE.

(defun get-bogus-defun-hints-ok (world)
  (declare (xargs :guard (plist-worldp world)))
  (let ((table (table-alist 'acl2-defaults-table world)))
    (cdr (assoc-eq :bogus-defun-hints-ok table))))

; Erroneous conditions stop processing.

(defun stop-error-0 (message) ; 0 arguments in message
  (declare (xargs :guard (stringp message)))
  (hard-error 'soft message nil))

(defun stop-error-1 (message arg1) ; 1 argument in message
  (declare (xargs :guard (stringp message)))
  (hard-error 'soft message (acons #\0 arg1 nil)))

(defun stop-error-2 (message arg1 arg2) ; 2 arguments in message
  (declare (xargs :guard (stringp message)))
  (hard-error 'soft message (acons #\0 arg1 (acons #\1 arg2 nil))))

(defun stop-error-3 (message arg1 arg2 arg3) ; 3 arguments in message
  (declare (xargs :guard (stringp message)))
  (hard-error 'soft
              message
              (acons #\0 arg1 (acons #\1 arg2 (acons #\2 arg3 nil)))))

(defmacro stop-error (message &rest args)
  (declare (xargs :guard (and (stringp message)
                              (<= (len args) 3)))) ; increase as needed
  (case (len args)
    (0 `(stop-error-0 ,message))
    (1 `(stop-error-1 ,message ,(first args)))
    (2 `(stop-error-2 ,message ,(first args) ,(second args)))
    (3 `(stop-error-3 ,message ,(first args) ,(second args) ,(third args)))))

; Second-order functions and theorems depend on function variables.
; Each function variable is typed by the number of its arguments (1 or more).
; Types of function variables are denoted
; by the ACL2-signature-like notation (* ... *) => *.

(defn *-listp (stars)
  (if (atom stars)
      (null stars)
    (and (eq (car stars) '*)
         (*-listp (cdr stars)))))

(defn funvar-typep (type)
  (and (true-listp type)
       (= (len type) 3)
       (*-listp (first type))
       (first type)
       (eq (second type) '=>)
       (eq (third type) '*)))

; The name and type of each function variable are stored in a table.

(table function-variables nil nil :guard (and (symbolp key) ; name
                                              (funvar-typep val)))

(defun funvarp (funvar world)
  (declare (xargs :guard (plist-worldp world)))
  (let ((table (table-alist 'function-variables world)))
    (and (symbolp funvar)
         (not (null (assoc-eq funvar table))))))

(defun funvar-type (funvar world)
  (declare (xargs :guard (and (plist-worldp world)
                              (funvarp funvar world))))
  (let ((table (table-alist 'function-variables world)))
    (cdr (assoc-eq funvar table))))

; Function variables are mimicked by uninterpreted functions (i.e. stubs).
; The macro DEFUNVAR defines a function variable with its type.
; DEFUNVAR introduces the stub and updates the table of function variables.

(defn defunvar-event (funvar arguments arrow result)
  (b* (((unless (symbolp funvar))
        (stop-error "~x0 must be a name." funvar))
       ((unless (*-listp arguments))
        (stop-error "~x0 must be a list (* ... *)." arguments))
       ((unless (eq arrow '=>))
        (stop-error "~x0 must be the arrow =>." arrow))
       ((unless (eq result '*))
        (stop-error "~x0 must be *." result)))
      `(progn
         (defstub ,funvar ,arguments => *)
         (table function-variables ',funvar '(,arguments => *)))))

(defmacro defunvar (funvar arguments arrow result)
  (declare (xargs :guard t))
  `(make-event (defunvar-event ',funvar ',arguments ',arrow ',result)))

(defmacro show-defunvar (funvar arguments arrow result)
  (declare (xargs :guard t))
  `(defunvar-event ',funvar ',arguments ',arrow ',result))

; A second-order function or theorem depends on
; a set of one or more function variables.
; The set is represented as a non-empty list without duplicates.

(defun funvar-listp (funvars world) ; may be empty or have duplicates
  (declare (xargs :guard (plist-worldp world)))
  (if (atom funvars)
      (null funvars)
    (and (funvarp (car funvars) world)
         (funvar-listp (cdr funvars) world))))

(defun funvar-setp (funvars world)
  (declare (xargs :guard (plist-worldp world)))
  (and (funvar-listp funvars world)
       funvars
       (no-duplicatesp funvars)))

; Three kinds of second-order functions are supported:
; plain functions
; (introduced via DEFUN2, which generates a DEFUN event),
; choice functions
; (introduced via DEFCHOOSE2, which generates a DEFCHOOSE event),
; and quantifier functions
; (introduced via DEFUN-SK2, which generates a DEFUN-SK event).

(defn sofun-kindp (kind)
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
; to each choice second-order function name its list of bound variables,
; and to each quantifier second-order function name
; its list of bound variables and its quantifier (FORALL or EXISTS).

(defn bound-varsp (bvars)
  (and (symbol-listp bvars)
       bvars
       (no-duplicatesp bvars)))

(defn quantifierp (quant)
  (or (eq quant 'forall)
      (eq quant 'exists)))

(defun plain-sofun-infop (info world) ; (KIND FUNVARS)
  (declare (xargs :guard (plist-worldp world)))
  (and (true-listp info)
       (= (len info) 2)
       (sofun-kindp (first info))
       (funvar-setp (second info) world)))

(defun choice-sofun-infop (info world) ; (KIND FUNVARS BVARS)
  (declare (xargs :guard (plist-worldp world)))
  (and (true-listp info)
       (= (len info) 3)
       (sofun-kindp (first info))
       (funvar-setp (second info) world)
       (bound-varsp (third info))))

(defun quant-sofun-infop (info world) ; (KIND FUNVARS BVARS QUANT)
  (declare (xargs :guard (plist-worldp world)))
  (and (true-listp info)
       (= (len info) 4)
       (sofun-kindp (first info))
       (funvar-setp (second info) world)
       (bound-varsp (third info))
       (quantifierp (fourth info))))

(defun sofun-infop (info world)
  (declare (xargs :guard (plist-worldp world)))
  (or (plain-sofun-infop info world)
      (choice-sofun-infop info world)
      (quant-sofun-infop info world)))
  
(table second-order-functions nil nil :guard (and (symbolp key) ; name
                                                  (sofun-infop val world)))

(defun sofunp (sofun world)
  (declare (xargs :guard (plist-worldp world)))
  (let ((table (table-alist 'second-order-functions world)))
    (and (symbolp sofun)
         (not (null (assoc-eq sofun table))))))

(defun sofun-kind (sofun world)
  (declare (xargs :guard (and (plist-worldp world)
                              (sofunp sofun world))))
  (let ((table (table-alist 'second-order-functions world)))
    (first (cdr (assoc-eq sofun table)))))

(defabbrev plain-sofunp (sofun world)
  (and (sofunp sofun world)
       (eq (sofun-kind sofun world) 'plain)))

(defabbrev choice-sofunp (sofun world)
  (and (sofunp sofun world)
       (eq (sofun-kind sofun world) 'choice)))

(defabbrev quant-sofunp (sofun world)
  (and (sofunp sofun world)
       (eq (sofun-kind sofun world) 'quant)))

(defun sofun-fparams (sofun world)
  (declare (xargs :guard (and (plist-worldp world)
                              (sofunp sofun world))))
  (let ((table (table-alist 'second-order-functions world)))
    (second (cdr (assoc-eq sofun table)))))

(defun sofun-bound-vars (sofun world)
  (declare (xargs :guard (and (plist-worldp world)
                              (or (choice-sofunp sofun world)
                                  (quant-sofunp sofun world)))))
  (let ((table (table-alist 'second-order-functions world)))
    (third (cdr (assoc-eq sofun table)))))

(defun sofun-quantifier (sofun world)
  (declare (xargs :guard (and (plist-worldp world)
                              (quant-sofunp sofun world))))
  (let ((table (table-alist 'second-order-functions world)))
    (fourth (cdr (assoc-eq sofun table)))))

; A term may reference a function variable directly
; (when the function variable occurs in the term)
; or indirectly
; (when the function variable
; is a parameter of a second-order function that occurs in the term).
; The following code returns
; a list of the function variables referenced by a term
; (the list may contain duplicates).

(mutual-recursion
 
 (defun funvars-of-term (term world)
   (declare (xargs :guard (and (pseudo-termp term)
                               (plist-worldp world))))
   (if (or (variablep term)
           (quotep term))
       nil ; no function variables in individual variables and constants
     (let* ((fn (fn-symb term))
            (fn-vars ; function variables in FN
             (if (flambdap fn)
                 (funvars-of-term (lambda-body fn) world)
               (if (funvarp fn world)
                     (list fn)
                   (if (sofunp fn world)
                       (sofun-fparams fn world)
                     nil))))) ; is a 1st-order function
       (append fn-vars (funvars-of-terms (fargs term) world)))))

 (defun funvars-of-terms (terms world)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (plist-worldp world))))
   (if (endp terms)
       nil
     (append (funvars-of-term (car terms) world)
             (funvars-of-terms (cdr terms) world)))))

; Plain second-order functions and their instances
; may reference function variables
; in their defining bodies,
; in their measures,
; and in their guards.
; For now recursive second-order functions (which are all plain)
; and their instances
; are only allowed to use O< as their well-founded relation,
; and so plain second-order functions and their instances
; may not reference function variables in their well-founded relations.

(defun funvars-of-defun (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (let* ((body (body fun nil world))
         (measure (measure fun world))
         (guard (fguard fun world))
         (body-funvars (funvars-of-term body world)) ; NIL if no body
         (measure-funvars (funvars-of-term measure world)) ; NIL if no measure
         (guard-funvars (funvars-of-term guard world))) ; NIL if no guard
    (append body-funvars
            measure-funvars
            guard-funvars)))

; Choice second-order functions and their instances
; may reference function variables in their defining bodies.

(defun funvars-of-defchoose (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (funvars-of-terms (defchoose-body fun world) world))

; Quantifier second-order functions and their instances
; may reference function variables in their matrices.
; The function variables in the matrix are the same as
; the function variables in the body of the function.
; For now the :REWRITE option of DEFUN-SK is not supported
; for second-order functions,
; so the rewrite rule cannot contain function variables
; that are not already in the matrix.

(defun funvars-of-defun-sk (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (funvars-of-term (body fun nil world) world))

; Second-order theorems and their instances
; may reference function variables in their formulas.

(defun funvars-of-defthm (thm world)
  (declare (xargs :guard (and (symbolp thm)
                              (plist-worldp world))))
  (funvars-of-term (tformula thm world) world))

; When a second-order function, or an instance thereof, is introduced,
; its function parameters must be
; all and only the function variables that the function depends on.
; A first-order instance of a second-order function,
; which has no function parameters,
; must depend on no function variables.

(defun check-fparams-dependency (fun kind fparams world)
  (declare
   (xargs :guard (and (symbolp fun)
                      (sofun-kindp kind) ; kind of FUN (if 2nd-order)
                                         ; or of the 2nd-order function
                                         ; of which FUN is an instance
                      (or (funvar-setp fparams world) ; if FUN is 2nd-order
                          (null fparams))             ; if FUN is 1st-order
                      (plist-worldp world))))
  (let ((funvars (case kind
                   (plain (funvars-of-defun fun world))
                   (choice (funvars-of-defchoose fun world))
                   (quant (funvars-of-defun-sk fun world)))))
    (cond ((set-equiv funvars fparams) t)
          (fparams ; FUN is 2nd-order
           (stop-error "~x0 must depend on exactly ~
                        its function parameters ~x1, ~
                        but depends on ~x2 instead.~%"
                       fun fparams funvars))
          (t ; FUN is 1st-order
           (stop-error "~x0 must depend on no function parameters, ~
                        but depens on ~x1 instead.~%"
                       fun funvars)))))

; When a recursive second-order function (which is always plain) is introduced,
; its well-founded relation must be O< for now
; (see the possible improvements/extensions at the end of this file).

(defun check-wfrel-o< (fun world)
  (declare (xargs :guard (and (symbolp fun)
                              (plist-worldp world))))
  (let ((wfrel (wfrel fun world)))
    (cond ((null wfrel) t) ; FUN is not recursive
          ((eq wfrel 'o<) t)
          (t (stop-error "~x0 must use O< as well-founded relation, not ~x1.~%"
                         fun wfrel)))))

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
; to leave the new function enabled after the DEFUN2.
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

(defun defun2-event (sofun fparams rest world)
  (declare (xargs :guard (plist-worldp world)))
  (b* (((unless (symbolp sofun))
        (stop-error "~x0 must be a name." sofun))
       ((unless (funvar-setp fparams world))
        (stop-error "~x0 must be a non-empty list of function variables ~
                     without duplicates."
                     fparams))
       (info (list 'plain fparams))
       (bogus-defun-hints-ok (get-bogus-defun-hints-ok world)))
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
  (declare (xargs :guard t))
  `(make-event (defun2-event ',sofun ',fparams ',rest (w state))))

(defmacro show-defun2 (sofun fparams &rest rest)
  (declare (xargs :guard t))
  `(defun2-event ',sofun ',fparams ',rest (w state)))

; The name of the termination theorem of a recursive second-order function
; is obtained by adding -T to the name of the function.

(defun sofun-termination-theorem-name (sofun)
  (declare (xargs :guard (symbolp sofun)))
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
; and the options :STRENGTHEN and :DOC are as in DEFCHOOSE.
;
; DEFCHOOSE2 generates a DEFCHOOSE event,
; updates the table of second-order functions,
; and checks that the supplied function variables are
; all and only the ones that the new function depends on.
;
; DEFCHOOSE2 directly checks
; the name, bound variables, and function parameters,
; but relies on DEFCHOOSE to check the rest of the form
; (individual parameters, body, and :STRENGTHEN and :DOC options).

(defun defchoose2-event (sofun bvars fparams rest world)
  (declare (xargs :guard (plist-worldp world)))
  (b* (((unless (symbolp sofun))
        (stop-error "~x0 must be a name." sofun))
       ((unless (or (symbolp bvars)
                    (symbol-listp bvars)))
        (stop-error "~x0 must be one or more bound variables." bvars))
       ((unless (funvar-setp fparams world))
        (stop-error "~x0 must be a non-empty list of function variables ~
                     without duplicates."
                     fparams))
       (info (list 'choice
                   fparams
                   (if (symbolp bvars) (list bvars) bvars))))
      `(progn
         (defchoose ,sofun ,bvars ,@rest)
         (table second-order-functions ',sofun ',info)
         (value-triple (check-fparams-dependency ',sofun
                                                 'choice
                                                 ',fparams
                                                 (w state))))))

(defmacro defchoose2 (sofun bvars fparams &rest rest)
  (declare (xargs :guard t))
  `(make-event (defchoose2-event ',sofun ',bvars ',fparams ',rest (w state))))

(defmacro show-defchoose2 (sofun bvars fparams &rest rest)
  (declare (xargs :guard t))
  `(defchoose2-event ',sofun ',bvars ',fparams ',rest (w state)))

; The macro DEFUN-SK2 introduces a quantifier second-order function.
; DEFUN-SK2 has the form
;   (DEFUN-SK2 SOFUN (FVAR1 ... FVARn) (VAR1 ... VARm)
;     BODY
;     :REWRITE ...
;     :STRENGTHEN ...
;     :SKOLEM-NAME ...
;     :QUANT-OK ...
;     :DOC ...)
; where SOFUN is the name of the function,
; (FVAR1 ... FVARn) is a non-empty list without duplicates of function variables
; that are the functions parameters whose order is immaterial,
; (VAR1 ... VARm) are the individual parameters as in DEFUN-SK,
; BODY is the body as in DEFUN-SK,
; and the options :STRENGTHEN through :DOC are as in DEFUN-SK
; except that only :DEFAULT and :DIRECT are allowed for :REWRITE (no terms).
;
; DEFUN-SK2 generates a DEFUN-SK event,
; updates the table of second-order functions,
; and checks that the supplied function variables are
; all and only the ones that the new function depends on.
;
; DEFUN-SK2 directly checks
; the name, function parameters, individual parameters,
; and top-level structure of the body
; (it checks that the body has the form (FORALL/EXISTS BOUND-VAR(S) ...)),
; but relies on DEFUN-SK to check
; the rest of the form (:REWRITE and the other options)
; and the matrix of the body.
;
; DEFUN-SK2 does not support
; the :THM-NAME, :WITNESS-DCLS, and :REWRITE with term options for now.
; Since DEFUN-SK2 delegates to DEFUN-SK the processing of the options,
; it is possible to use, without an immediate error,
; the :REWRITE TERM and :THM-NAME and :WITNESS-DCLS options,
; but then the behavior is undefined from the perspective of SOFT.

(defun defun-sk2-event (sofun fparams params body rest world)
  (declare (xargs :guard (plist-worldp world)))
  (b* (((unless (symbolp sofun))
        (stop-error "~x0 must be a name." sofun))
       ((unless (funvar-setp fparams world))
        (stop-error "~x0 must be a non-empty list of function variables ~
                     without duplicates."
                     fparams))
       ((unless (symbol-listp params))
        (stop-error "~x0 must be a list of symbols." params))
       ((unless (and (consp body)
                     (= (len body) 3)
                     (or (eq (first body) 'forall)
                         (eq (first body) 'exists))
                     (or (symbolp (second body))
                         (symbol-listp (second body)))))
        (stop-error "~x0 must be a quantified formula." body))
       (quantifier (first body))
       (bvars (second body))
       (bvars (if (symbolp bvars) (list bvars) bvars))
       (info (list 'quant fparams bvars quantifier)))
      `(progn
         (defun-sk ,sofun ,params ,body ,@rest)
         (table second-order-functions ',sofun ',info)
         (value-triple (check-fparams-dependency ',sofun
                                                 'quant
                                                 ',fparams
                                                 (w state))))))

(defmacro defun-sk2 (sofun fparams params body &rest rest)
  (declare (xargs :guard t))
  `(make-event
    (defun-sk2-event ',sofun ',fparams ',params ',body ',rest (w state))))

(defmacro show-defun-sk2 (sofun fparams params body &rest rest)
  (declare (xargs :guard t))
  `(defun-sk2-event ',sofun ',fparams ',params ',body ',rest (w state)))

; A theorem may reference function variables in its formula.

(defun funvars-of-theorem (thm world)
  (declare (xargs :guard (and (symbolp thm)
                              (plist-worldp world))))
  (funvars-of-term (tformula thm world) world))
  
; A second-order theorem is mimicked by a (first-order) theorem
; that depends on one or more function variables,
; over which the second-order theorem is universally quantified.
; A theorem is second-order iff it depends on one or more function variables.

(defun sothmp (sothm world)
  (declare (xargs :guard (plist-worldp world)))
  (not (null (funvars-of-theorem sothm world))))

; When a second-order function or theorem is instantiated,
; certain function names are replaced with other function names,
; similarly to functional instantiation in ACL2's.
; A function substitution is an alist with unique keys
; that maps function names to function names
; and without trivial pairs (e.g. pairs whose key is the same as the value).

(defun no-trivial-pairsp (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      t
    (let ((pair (car alist)))
      (and (not (equal (car pair) (cdr pair)))
           (no-trivial-pairsp (cdr alist))))))

(defn fun-substp (fsbs)
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

(defun funvar-instp (inst world)
  (declare (xargs :guard (plist-worldp world)))
  (and (fun-substp inst)
       inst
       (funvar-listp (alist-keys inst) world)
       (function-symbol-listp (alist-vals inst) world)))

(defun funvar-inst-listp (insts world)
  (declare (xargs :guard (plist-worldp world)))
  (if (atom insts)
      (null insts)
    (and (funvar-instp (car insts) world)
         (funvar-inst-listp (cdr insts) world))))

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

(defun sof-instancesp (instmap world)
  (declare (xargs :guard (plist-worldp world)))
  (and (alistp instmap)
       (funvar-inst-listp (alist-keys instmap) world)
       (symbol-listp (alist-vals instmap))))

(defun get-sof-instance (inst instmap world) ; read from map (NIL if absent)
  (declare (xargs :guard (and (plist-worldp world)
                              (funvar-instp inst world)
                              (sof-instancesp instmap world))))
  (if (endp instmap)
      nil
    (let ((pair (car instmap)))
      (if (alist-equiv (car pair) inst)
          (cdr pair)
        (get-sof-instance inst (cdr instmap) world)))))

(defun put-sof-instance (inst fun instmap world) ; add to map
  (declare (xargs :guard (and (plist-worldp world)
                              (funvar-instp inst world)
                              (symbolp fun)
                              (sof-instancesp instmap world)
                              ;; must not be already in map:
                              (null (get-sof-instance inst instmap world)))))
  (declare (ignore world)) ; only used in guard
  (acons inst fun instmap))

; A table maps second-order functions to their instances.
; Only second-order functions with instances appear in the table.

(table sof-instances nil nil :guard (and (symbolp key) ; name
                                         (sof-instancesp val world)))

(defun sof-instances (sofun world) ; instances of SOFUN (NIL if none)
  (declare (xargs :guard (and (plist-worldp world)
                              (sofunp sofun world))))
  (let ((table (table-alist 'sof-instances world)))
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

(defun fun-subst-function (fsbs fun world)
  (declare (xargs :guard (and (fun-substp fsbs)
                              (symbolp fun)
                              (plist-worldp world))))
  (let ((pair (assoc-eq fun fsbs)))
    (if pair ; FUN is a key of FSBS
        (cdr pair)
      (if (sofunp fun world)
          (let* ((fparams (sofun-fparams fun world))
                 (subfsbs (restrict-alist fparams fsbs)))
            (if (null subfsbs) ; FUN does not depend on keys of FSBS
                fun
              (let* ((instmap (sof-instances fun world))
                     (new-fun (get-sof-instance subfsbs instmap world)))
                (if new-fun ; instance of FUN exists
                    new-fun
                  (stop-error "~x0 has no instance for ~x1."
                              fun fsbs)))))
        fun)))) ; FUN is a function variable or 1st-order function

(mutual-recursion

 (defun fun-subst-term (fsbs term world)
   (declare (xargs :guard (and (fun-substp fsbs)
                               (pseudo-termp term)
                               (plist-worldp world))))
   (if (or (variablep term)
           (quotep term))
       term ; no change to individual variables and constants
     (let* ((fn (fn-symb term))
            ;; apply substitution to FN:
            (new-fn (if (symbolp fn)
                        (fun-subst-function fsbs fn world)
                      (make-lambda (lambda-formals fn)
                                   (fun-subst-term fsbs
                                                   (lambda-body fn)
                                                   world))))
            ;; apply substitution to arguments:
            (new-args (fun-subst-terms fsbs (fargs term) world)))
       (cons new-fn new-args))))

 (defun fun-subst-terms (fsbs terms world)
   (declare (xargs :guard (and (fun-substp fsbs)
                               (pseudo-term-listp terms)
                               (plist-worldp world))))
   (if (endp terms)
       nil
     (cons (fun-subst-term fsbs (car terms) world)
           (fun-subst-terms fsbs (cdr terms) world)))))

; A DEFUN-SK introduces a rewrite rule for the function FUN being defined,
; namely the FUN-NECC (for FORALL) or FUN-SUFF (for EXISTS) theorem.

(defun defun-sk-rewrite-rule-name (fun quant)
  (declare (xargs :guard (and (symbolp fun)
                              (quantifierp quant))))
  (let* ((fun-name (symbol-name fun))
         (suffix (case quant (forall "-NECC") (exists "-SUFF")))
         (rule-name (string-append fun-name suffix)))
    (intern-in-package-of-symbol rule-name fun)))

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

(mutual-recursion

 (defun ext-fun-subst-term (term fsbs world)
   (declare (xargs :mode :program ; termination needs ACL2 world invariants
                   :guard (and (pseudo-termp term)
                               (fun-substp fsbs)
                               (plist-worldp world))))
   (if (or (variablep term)
           (quotep term))
       fsbs ; no 2nd-order functions in individual variables and constants
     (let* ((fn (fn-symb term))
            (fsbs (if (symbolp fn)
                      (ext-fun-subst-function fn fsbs world)
                    (ext-fun-subst-term (lambda-body fn) fsbs world))))
       (ext-fun-subst-terms (fargs term) fsbs world))))

 (defun ext-fun-subst-terms (terms fsbs world)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (fun-substp fsbs)
                               (plist-worldp world))))
   (if (endp terms)
       fsbs
     (let ((fsbs (ext-fun-subst-term (car terms) fsbs world)))
       (ext-fun-subst-terms (cdr terms) fsbs world))))

 (defun ext-fun-subst-function (fun fsbs world)
   (declare (xargs :guard (and (symbolp fun)
                               (fun-substp fsbs)
                               (plist-worldp world))))
   (cond
    ((assoc fun fsbs) fsbs) ; pair already present
    ((sofunp fun world)
     (b* ((fparams (sofun-fparams fun world))
          (subfsbs (restrict-alist fparams fsbs))
          ((if (null subfsbs)) fsbs) ; FUN unchanged under FSBS
          (instmap (sof-instances fun world))
          (funinst (get-sof-instance subfsbs instmap world))
          ((unless funinst)
           (stop-error "~x0 has no instance for ~x1." fun fsbs))
          (fsbs (acons fun funinst fsbs))) ; extend FSBS
         (case (sofun-kind fun world)
           (plain (ext-fun-subst-term (body fun nil world) fsbs world))
           (choice (ext-fun-subst-term (defchoose-body fun world) fsbs world))
           (quant
            (let* ((fsbs (ext-fun-subst-term (body fun nil world) fsbs world))
                   (quant (sofun-quantifier fun world))
                   ;; the 2nd-order functions in the matrix of FUN
                   ;; are the same as in the rewrite rule of FUN:
                   (body
                    (tformula (defun-sk-rewrite-rule-name fun quant) world)))
              (ext-fun-subst-term body fsbs world))))))
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

(defun sothm-inst-pairs (fsbs world)
  (declare (xargs :guard (and (fun-substp fsbs)
                              (plist-worldp world))))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (if (quant-sofunp 1st world)
          (let ((1st-wit
                 (getprop 1st 'constraint-lst nil 'current-acl2-world world))
                (2nd-wit
                 (getprop 2nd 'constraint-lst nil 'current-acl2-world world)))
            (cons (list 1st 2nd) ; pair from FSBS
                  (cons (list 1st-wit 2nd-wit) ; pair of witnesses
                        (sothm-inst-pairs (cdr fsbs) world))))
        (cons (list 1st 2nd) ; pair from FSBS
              (sothm-inst-pairs (cdr fsbs) world))))))

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

(defun sothm-inst-facts (fsbs world)
  (declare (xargs :guard (and (fun-substp fsbs)
                              (plist-worldp world))))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (cond ((or (plain-sofunp 1st world)
                 (choice-sofunp 1st world))
             (cons 2nd (sothm-inst-facts (cdr fsbs) world)))
            ((quant-sofunp 1st world)
             (cons (defun-sk-rewrite-rule-name 2nd (sofun-quantifier 1st world))
                   (sothm-inst-facts (cdr fsbs) world)))
            (t (sothm-inst-facts (cdr fsbs) world))))))

; Instances of second-order theorems are proved using the ACL2 proof checker.
; Each such instance is proved by
; first using the :FUNCTIONAL-INSTANCE described above,
; then using the facts described above on the subgoals.
; Each sugoal only needs a subset of those facts,
; but for simplicity all the facts are used for each subgoal,
; using the proof checker :REPEAT command.
; Since sometimes the facts are not quite identical to the subgoals,
; the proof checker :PROVE command is used to iron out any such differences.

(defun sothm-inst-proof (sothm fsbs world)
  (declare (xargs :guard (and (symbolp sothm)
                              (fun-substp fsbs)
                              (plist-worldp world))))
  `(:instructions
    ((:use (:functional-instance ,sothm ,@(sothm-inst-pairs fsbs world)))
     (:repeat (:then (:use ,@(sothm-inst-facts fsbs world)) :prove)))))

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
(defun check-sothm-inst (sothm-inst world)
  (declare (xargs :guard (plist-worldp world)))
  (and (true-listp sothm-inst)
       (>= (len sothm-inst) 2)
       (sothmp (car sothm-inst) world)
       (funvar-instp (cdr sothm-inst) world)))

(defun defthm-inst-event (thm sothm-inst rest world)
  (declare (xargs :mode :program ; calls EXT-FUN-SUBST-TERM
                  :guard (plist-worldp world)))
  (b* (;; THM is the name of the new theorem:
       ((unless (symbolp thm)) (stop-error "~x0 must be a name." thm))
       ;; after THM there is (SOTHM (F1 . G1) ... (Fm . Gm)):
       ((unless (check-sothm-inst sothm-inst world))
        (stop-error "~x0 must be the name of a second-order theorem ~
                     followed by the pairs of an instantiation."
                    sothm-inst))
       ;; decompose (SOTHM (F1 . G1) ... (Fm . Gm)):
       (sothm (car sothm-inst))
       (inst (cdr sothm-inst))
       ;; every Fi must be a function variable that SOTHM depends on:
       ((unless (subsetp (alist-keys inst) (funvars-of-theorem sothm world)))
        (stop-error "Each function variable key of ~x0 must be ~
                     among function variable that ~x1 depends on."
                    inst sothm))
       ;; apply ((F1 . G1) ... (Fm . Gm)) to the formula of SOTHM:
       (sothm-formula (tformula sothm world))
       (thm-formula (fun-subst-term inst sothm-formula world))
       ;; construct the proof from the instantiation:
       (fsbs (ext-fun-subst-term sothm-formula inst world))
       (thm-proof (sothm-inst-proof sothm fsbs world)))
      ;; generate event (REST is RULE-CLASSES, if present):
      `(defthm ,thm ,thm-formula ,@thm-proof ,@rest)))

(defmacro defthm-inst (thm uqfvars-or-sothminst &rest rest)
  (declare (xargs :guard t))
  `(make-event
    (defthm-inst-event ',thm ',uqfvars-or-sothminst ',rest (w state))))

(defmacro show-defthm-inst (thm uqfvars-or-sothminst &rest rest)
  (declare (xargs :guard t))
  `(defthm-inst-event ',thm ',uqfvars-or-sothminst ',rest (w state)))

; The macro DEFUN-INST introduces an instance of a second-order function.
; DEFUN-INST has the form
;   (DEFUN-INST FUN (FVAR1 ... FVARn)
;     (SOFUN (F1 . G1) ... (Fm . Gm))
;     :VERIFY-GUARDS ...
;     :DOC ...
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
; The :DOC option in DEFUN-INST can be used
; only if SOFUN is a choice second-order function.
; Its meaning is the same as in DEFCHOOSE,
; but generally documentation should be attached
; to the second-order functions introduced via DEFUN2, DEFCHOOSE2, or DEFUN-SK2,
; and not to their instances.
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
; only if SOFUN is a quantifier second-order function;
; only the :DEFAULT and :DIRECT values are allowed for :REWRITE (no terms).
; Their meaning is the same as in DEFUN-SK.
;
; Since DEFUN-SK accepts more options than :SKOLEM-NAME and :THM-NAME,
; it may be possible to supply, without an immediate error,
; more options than :SKOLEM-NAME and :REWRITE to DEFUN-INST
; (or :REWRITE with a term)
; when SOFUN is a quantifier second-order function,
; but this is currently not supported by SOFT,
; i.e. the behavior is undefined from the perspective of SOFT.
;
; For now, SOFT does not support the transitivity of instantiations,
; i.e. that if F is an instance of G and G is an instance of H,
; then F is also an instance of H.

; check that SOFUN-INST had the form (SOFUN (F1 . G1) ... (Fm . Gm)),
; where SOFUN is a 2nd-order function
; and ((F1 . G1) ... (Fm . Gm)) is an instantiation:
(defun check-sofun-inst (sofun-inst world)
  (declare (xargs :guard (plist-worldp world)))
  (and (true-listp sofun-inst)
       (>= (len sofun-inst) 2)
       (sofunp (car sofun-inst) world)
       (funvar-instp (cdr sofun-inst) world)))

; events to introduce FUN
; and to add it to the table of second-order functions if it is second-order,
; when SOFUN is a plain second-order function:
(defun defun-inst-plain-events (fun fparams sofun inst options world)
  (declare (xargs :mode :program ; calls EXT-FUN-SUBST-TERM
                  :guard (and (symbolp fun)
                              (true-listp options)
                              (plist-worldp world)
                              (or (funvar-setp fparams world) ; FUN is 2nd-order
                                  (null fparams))             ; FUN is 1st-order
                              (plain-sofunp sofun world))))
  (b* (;; retrieve body, measure, and guard of SOFUN:
       (sofun-body (body sofun nil world))
       (sofun-measure (measure sofun world))
       (sofun-guard (fguard sofun world))
       ;; extend instantiation with (SOFUN . FUN) if SOFUN is recursive
       ;; (so that recursive calls to SOFUN can be properly replaced with FUN)
       ;; and apply it to the body of SOFUN:
       (fsbs (if sofun-measure (acons sofun fun inst) inst))
       (fun-body (fun-subst-term fsbs sofun-body world))
       ;; apply instantiation to the measure and guard of SOFUN:
       (fun-measure (fun-subst-term inst sofun-measure world))
       (fun-guard (fun-subst-term inst sofun-guard world))
       ;; construct the termination proof from the instantiation, if recursive:
       (sofun-tt-name (sofun-termination-theorem-name sofun))
       (sofun-tt-formula (tformula sofun-tt-name world)) ; could be NIL
       (fsbs (ext-fun-subst-term sofun-tt-formula inst world))
       (fun-tt-proof (sothm-inst-proof sofun-tt-name fsbs world))
       ;; :HINTS of FUN if recursive, otherwise NIL:
       (hints (if fun-measure `(:hints (("Goal" ,@fun-tt-proof))) nil))
       ;; :MEASURE of FUN if recursive, otherwise NIL:
       (measure (if fun-measure `(:measure ,fun-measure) nil))
       ;; :GUARD of FUN if guarded, otherwise NIL:
       (guard (if fun-guard `(:guard ,fun-guard) nil))
       ;; :T-PROOF option if FUN is recursive, otherwise NIL:
       (t-proof (if fun-measure '(:t-proof t) nil))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (info (list 'plain fparams))
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
      ;; generated list of events:
      `((define ,fun ,(formals sofun world)
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
(defun defun-inst-choice-events (fun fparams sofun inst options world)
  (declare (xargs :guard (and (symbolp fun)
                              (true-listp options)
                              (plist-worldp world)
                              (or (funvar-setp fparams world) ; FUN is 2nd-order
                                  (null fparams))             ; FUN is 1st-order
                              (choice-sofunp sofun world))))
  (b* (;; retrieve bound variables of SOFUN:
       (bound-vars (sofun-bound-vars sofun world))
       ;; apply instantiation to body of SOFUN:
       (sofun-body (defchoose-body sofun world))
       (fun-body (fun-subst-term inst sofun-body world))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (info (list 'choice fparams bound-vars))
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
      ;; generated list of events:
      `((defchoose ,fun ,bound-vars ,(formals sofun world)
          ,fun-body
          :strengthen ,(defchoose-strongp sofun world)
          ,@options)
        ,@table-event)))

; events to introduce FUN
; and to add it to the table of second-order functions if it is second-order,
; when SOFUN is a quantifier second-order function:
(defun defun-inst-quant-events (fun fparams sofun inst options world)
  (declare (xargs :guard (and (symbolp fun)
                              (true-listp options)
                              (plist-worldp world)
                              (or (funvar-setp fparams world) ; FUN is 2nd-order
                                  (null fparams))             ; FUN is 1st-order
                              (quant-sofunp sofun world))))
  (b* (;; retrieve bound variables and quantifier of SOFUN:
       (bound-vars (sofun-bound-vars sofun world))
       (1bvarp (= (len bound-vars) 1))
       (quant (sofun-quantifier sofun world))
       ;; apply instantiation to the matrix of SOFUN:
       (sofun-matrix (defun-sk-matrix sofun 1bvarp world))
       (fun-matrix (fun-subst-term inst sofun-matrix world))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (info (list 'quant fparams bound-vars quant))
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
      ;; generated list of events:
      `((defun-sk ,fun ,(formals sofun world)
          (,quant ,bound-vars ,fun-matrix)
          :strengthen ,(defun-sk-strongp sofun world)
          :quant-ok T
          ,@options)
        ,@table-event)))

(defun defun-inst-event (fun fparams-or-sofuninst rest world)
  (declare (xargs :mode :program ; calls DEFUN-INST-PLAIN-EVENTS
                  :guard (plist-worldp world)))
  (b* (;; FUN is the name of the new function:
       ((unless (symbolp fun)) (stop-error "~x0 must be a name." fun))
       ;; after FUN there is (FVAR1 ... FVARn) if FUN is 2nd-order,
       ;; otherwise there is (SOFUN (F1 . G1) ... (Fm . Gm)):
       (2nd-order ; T if FUN is 2nd-order
        (funvar-setp fparams-or-sofuninst world))
       ((unless (or 2nd-order
                    (check-sofun-inst fparams-or-sofuninst world)))
        (stop-error "~x0 must be either a non-empty list of ~
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
                         (check-sofun-inst (car rest) world))))
        (stop-error "~x0 must start with the name of a second-order function ~
                      followed by an instantiation."
                     rest))
       (sofun-inst (if 2nd-order (car rest) fparams-or-sofuninst))
       ;; decompose (SOFUN (F1 . G1) ... (Fm . Gm)):
       (sofun (car sofun-inst))
       (inst (cdr sofun-inst))
       ;; every Fi must be a function parameter of SOFUN:
       ((unless (subsetp (alist-keys inst) (sofun-fparams sofun world)))
        (stop-error "Each function variable key of ~x0 must be ~
                     among the function parameters ~x1 of ~x2."
                    inst (sofun-fparams sofun world) sofun))
       ;; the options are REST if FUN is 1st-order,
       ;; otherwise they come after (SOFUN (F1 . G1) ... (Fm . Gm)) in REST:
       (options (if 2nd-order (cdr rest) rest))
       ;; events specific to the kind of SOFUN:
       (spec-events
        (case (sofun-kind sofun world)
          (plain
           (defun-inst-plain-events fun fparams sofun inst options world))
          (choice
           (defun-inst-choice-events fun fparams sofun inst options world))
          (quant
           (defun-inst-quant-events fun fparams sofun inst options world))))
       ;; updated entry for SOFUN
       ;; in table of instances of second-order functions:
       (instmap (sof-instances sofun world))
       (new-instmap (put-sof-instance inst fun instmap world)))
      ;; generated event:
      `(progn
         ,@spec-events
         (table sof-instances ',sofun ',new-instmap)
         (value-triple (check-fparams-dependency ',fun
                                                 ',(sofun-kind sofun world)
                                                 ',fparams
                                                 (w state))))))

(defmacro defun-inst (fun fparams-or-sofuninst &rest rest)
  (declare (xargs :guard t))
  `(make-event
    (defun-inst-event ',fun ',fparams-or-sofuninst ',rest (w state))))

(defmacro show-defun-inst (fun fparams-or-sofuninst &rest rest)
  (declare (xargs :guard t))
  `(defun-inst-event ',fun ',fparams-or-sofuninst ',rest (w state)))

; Some possible Improvements/Extensions:
;
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
; - Extend DEFUN-SK2 to support options
;   :THM-NAME, :WITNESS-DCLS, and :REWRITE with term,
;   that are analogous to the ones in DEFUN-SK.
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
