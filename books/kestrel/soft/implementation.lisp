; SOFT (Second-Order Functions and Theorems) -- Implementation
;
; Copyright (C) 2015-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "kestrel/utilities/defchoose-queries" :dir :system)
(include-book "kestrel/utilities/defun-sk-queries" :dir :system)
(include-book "kestrel/utilities/symbol-symbol-alists" :dir :system)
(include-book "std/alists/alist-equiv" :dir :system)
(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some possible improvements/extensions are discussed at the end of the file.

; Second-order functions and theorems depend on function variables.
; Each function variable is typed by the number of its arguments (0 or more).
; Types of function variables are denoted
; by the ACL2-signature-like notation (* ... *) => *.

(define *-listp (stars)
  (if (atom stars)
      (null stars)
    (and (eq (car stars) 'acl2::*)
         (*-listp (cdr stars)))))

; The name of each function variable is stored in a table.

(table function-variables nil nil :guard (and (symbolp acl2::key) ; name
                                              (null acl2::val))) ; no extra info

(define funvarp (funvar (wrld plist-worldp))
  :verify-guards nil
  (let ((table (table-alist 'function-variables wrld)))
    (and (symbolp funvar)
         (not (null (assoc-eq funvar table))))))

; Function variables are mimicked by uninterpreted functions (i.e. stubs).
; The macro DEFUNVAR defines a function variable with its type.
; DEFUNVAR introduces the stub and updates the table of function variables.

(define defunvar-event (funvar arguments arrow result)
  (b* (((unless (symbolp funvar))
        (raise "~x0 must be a name." funvar))
       ((unless (*-listp arguments))
        (raise "~x0 must be a list (* ... *)." arguments))
       ((unless (and (symbolp arrow)
                     (equal (symbol-name arrow) "=>")))
        (raise "~x0 must be the arrow =>." arrow))
       ((unless (eq result 'acl2::*))
        (raise "~x0 must be *." result)))
      `(progn
         (defstub ,funvar ,arguments => *)
         (table function-variables ',funvar nil))))

(defmacro defunvar (funvar arguments arrow result)
  `(make-event (defunvar-event ',funvar ',arguments ',arrow ',result)))

(defmacro show-defunvar (funvar arguments arrow result)
  `(defunvar-event ',funvar ',arguments ',arrow ',result))

(defmacro acl2::defunvar (&rest args)
  `(defunvar ,@args))

(defmacro acl2::show-defunvar (&rest args)
  `(show-defunvar ,@args))

; A second-order function or theorem depends on
; a set of one or more function variables.
; The set is represented as a non-empty list without duplicates.

(define funvar-listp ; may be empty or have duplicates
  (funvars (wrld plist-worldp))
  :verify-guards nil
  (if (atom funvars)
      (null funvars)
    (and (funvarp (car funvars) wrld)
         (funvar-listp (cdr funvars) wrld))))

(define funvar-setp (funvars (wrld plist-worldp))
  :verify-guards nil
  (and (funvar-listp funvars wrld)
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

(define sofun-infop (info (wrld plist-worldp))
  :verify-guards nil
  (and (true-listp info)
       (= (len info) 2)
       (sofun-kindp (first info))
       (funvar-setp (second info) wrld)))

(table second-order-functions nil nil
  :guard (and (symbolp acl2::key) ; name
              (sofun-infop acl2::val world)))

(define sofunp (sofun (wrld plist-worldp))
  :verify-guards nil
  (let ((table (table-alist 'second-order-functions wrld)))
    (and (symbolp sofun)
         (not (null (assoc-eq sofun table))))))

(define sofun-kind ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :verify-guards nil
  (let ((table (table-alist 'second-order-functions wrld)))
    (first (cdr (assoc-eq sofun table)))))

(defabbrev plain-sofunp (sofun wrld)
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'plain)))

(defabbrev choice-sofunp (sofun wrld)
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'choice)))

(defabbrev quant-sofunp (sofun wrld)
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'quant)))

(define sofun-fparams ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :verify-guards nil
  (let ((table (table-alist 'second-order-functions wrld)))
    (second (cdr (assoc-eq sofun table)))))

; A term may reference a function variable directly
; (when the function variable occurs in the term)
; or indirectly
; (when the function variable
; is a parameter of a second-order function that occurs in the term).
; The following code returns
; a list of the function variables referenced by a term
; (the list may contain duplicates).

(defines funvars-of-term/terms
  :verify-guards nil

  (define funvars-of-term ((term pseudo-termp) (wrld plist-worldp))
    (if (or (variablep term)
            (quotep term))
        nil ; no function variables in individual variables and constants
      (let* ((fn (fn-symb term))
             (fn-vars ; function variables in FN
              (if (flambdap fn)
                  (funvars-of-term (lambda-body fn) wrld)
                (if (funvarp fn wrld)
                    (list fn)
                  (if (sofunp fn wrld)
                      (sofun-fparams fn wrld)
                    nil))))) ; is a 1st-order function
        (append fn-vars (funvars-of-terms (fargs term) wrld)))))

  (define funvars-of-terms ((terms pseudo-term-listp) (wrld plist-worldp))
    (if (endp terms)
        nil
      (append (funvars-of-term (car terms) wrld)
              (funvars-of-terms (cdr terms) wrld)))))

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

(define funvars-of-defun ((fun symbolp) (wrld plist-worldp))
  :mode :program
  (let* ((body (ubody fun wrld))
         (measure (if (recursivep fun nil wrld)
                      (measure fun wrld)
                    nil))
         (guard (guard fun nil wrld))
         (body-funvars (funvars-of-term body wrld))
         (measure-funvars (funvars-of-term measure wrld)) ; NIL if no measure
         (guard-funvars (funvars-of-term guard wrld)))
    (append body-funvars
            measure-funvars
            guard-funvars)))

; Choice second-order functions and their instances
; may reference function variables in their defining bodies.

(define funvars-of-defchoose ((fun symbolp) (wrld plist-worldp))
  :mode :program
  (funvars-of-term (defchoose-body fun wrld) wrld))

; Second-order theorems and their instances
; may reference function variables in their formulas.

(define funvars-of-defthm ((thm symbolp) (wrld plist-worldp))
  :mode :program
  (funvars-of-term (formula thm nil wrld) wrld))

; When a second-order function, or an instance thereof, is introduced,
; its function parameters must be
; all and only the function variables that the function depends on.
; A first-order instance of a second-order function,
; which has no function parameters,
; must depend on no function variables.

(define check-fparams-dependency
  ((fun symbolp)
   (kind sofun-kindp) ; kind of 2nd-order function of which FUN is an instance
   (fparams (or (funvar-setp fparams wrld) ; if FUN is 2nd-order
                (null fparams)))           ; if FUN is 1st-order
   (wrld plist-worldp))
  :mode :program
  (let ((funvars (case kind
                   (plain (funvars-of-defun fun wrld))
                   (choice (funvars-of-defchoose fun wrld))
                   (quant (funvars-of-defun fun wrld)))))
    (cond ((set-equiv funvars fparams) t)
          (fparams ; FUN is 2nd-order
           (raise "~x0 must depend on exactly its function parameters ~x1, ~
                   but depends on ~x2 instead.~%"
                  fun fparams funvars))
          (t ; FUN is 1st-order
           (raise "~x0 must depend on no function parameters, ~
                   but depends on ~x1 instead.~%"
                  fun funvars)))))

; When a recursive second-order function (which is always plain) is introduced,
; its well-founded relation must be O< for now
; (see the possible improvements/extensions at the end of this file).

(define check-wfrel-o< ((fun symbolp) (wrld plist-worldp))
  :verify-guards nil
  (if (recursivep fun nil wrld)
      (let ((wfrel (well-founded-relation fun wrld)))
        (or (eq wfrel 'o<)
            (raise "~x0 must use O< as well-founded relation, not ~x1.~%"
                   fun wfrel)))
    t))

; When a quantifier second-order function, or an instance thereof,
; is introduced with a custom rewrite rule in :REWRITE,
; the custom rewrite rule must have the same function variables
; as the matrix (or body) of the function.

(define check-qrewrite-rule-funvars ((fun symbolp) (wrld plist-worldp))
  :mode :program
  (let* ((rule-name (defun-sk-info->rewrite-name (defun-sk-check fun wrld)))
         (rule-body (formula rule-name nil wrld))
         (fun-body (ubody fun wrld)))
    (or (set-equiv (funvars-of-term rule-body wrld)
                   (funvars-of-term fun-body wrld))
        (raise "The custome rewrite rule ~x0 must have ~
                the same function variables as the function body ~x1.~%"
               rule-body fun-body))))

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
; DEFUN2 generates a DEFUN event,
; updates the table of second-order functions,
; and checks that the supplied function variables are
; all and only the ones that the new function depends on.
; If the new function is recursive,
; it also checks that the well-founded relation is O<.
;
; DEFUN2 directly checks the name and the function parameters,
; but relies on DEFUN to check the rest of the form
; (individual parameters,
; optional documentation string,
; optional declarations,
; and body).

(define defun2-event (sofun fparams rest (wrld plist-worldp))
  :verify-guards nil
  (b* (((unless (symbolp sofun))
        (raise "~x0 must be a name." sofun))
       ((unless (funvar-setp fparams wrld))
        (raise "~x0 must be a non-empty list of function variables ~
                 without duplicates."
               fparams))
       (info (list 'plain fparams)))
    `(progn
       (defun ,sofun ,@rest)
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

(defmacro acl2::defun2 (&rest args)
  `(defun2 ,@args))

(defmacro acl2::show-defun2 (&rest args)
  `(show-defun2 ,@args))

; The macro DEFCHOOSE2 introduces a choice second-order function.
; DEFCHOOSE2 has the form
;   (DEFCHOOSE2 SOFUN (BVAR1 ... BVARm) (FVAR1 ... FVARn) (VAR1 ... VARp)
;     BODY
;     :STRENGTHEN ...)
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
  (sofun bvars fparams params body options (wrld plist-worldp))
  :verify-guards nil
  (b* (((unless (symbolp sofun))
        (raise "~x0 must be a name." sofun))
       ((unless (or (symbolp bvars)
                    (symbol-listp bvars)))
        (raise "~x0 must be one or more bound variables." bvars))
       ((unless (funvar-setp fparams wrld))
        (raise "~x0 must be a non-empty list of function variables ~
                without duplicates."
               fparams))
       (info (list 'choice fparams)))
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

(defmacro acl2::defchoose2 (&rest args)
  `(defchoose2 ,@args))

(defmacro acl2::show-defchoose2 (&rest args)
  `(show-defchoose2 ,@args))

; The macro DEFUN-SK2 introduces a quantifier second-order function.
; DEFUN-SK2 has the form
;   (DEFUN-SK2 SOFUN (FVAR1 ... FVARn) (VAR1 ... VARm)
;     BODY
;     :STRENGTHEN ...
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
; As in DEFUN-SK, the keyed option :REWRITE may be present only if
; the quantifier is universal.
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

(define defun-sk2-event (sofun fparams params body options (wrld plist-worldp))
  :verify-guards nil
  (b* (((unless (symbolp sofun))
        (raise "~x0 must be a name." sofun))
       ((unless (funvar-setp fparams wrld))
        (raise "~x0 must be a non-empty list of function variables ~
                without duplicates."
               fparams))
       ((unless (symbol-listp params))
        (raise "~x0 must be a list of symbols." params))
       ((unless (and (consp body)
                     (= (len body) 3)
                     (defun-sk-quantifier-p (first body))
                     (or (symbolp (second body))
                         (symbol-listp (second body)))))
        (raise "~x0 must be a quantified formula." body))
       ((unless (keyword-value-listp options))
        (raise "~x0 must be a list of keyed options." options))
       (info (list 'quant fparams)))
      `(progn
         (defun-sk ,sofun ,params ,body ,@options)
         (table second-order-functions ',sofun ',info)
         (value-triple (check-fparams-dependency ',sofun
                                                 'quant
                                                 ',fparams
                                                 (w state)))
         (value-triple (check-qrewrite-rule-funvars ',sofun
                                                    (w state))))))

(defmacro defun-sk2 (sofun fparams params body &rest options)
  `(make-event
    (defun-sk2-event ',sofun ',fparams ',params ',body ',options (w state))))

(defmacro show-defun-sk2 (sofun fparams params body &rest options)
  `(defun-sk2-event ',sofun ',fparams ',params ',body ',options (w state)))

(defmacro acl2::defun-sk2 (&rest args)
  `(defun-sk2 ,@args))

(defmacro acl2::show-defun-sk2 (&rest args)
  `(show-defun-sk2 ,@args))

; A theorem may reference function variables in its formula.

(define funvars-of-theorem ((thm symbolp) (wrld plist-worldp))
  :mode :program
  (funvars-of-term (formula thm nil wrld) wrld))

; A second-order theorem is mimicked by a (first-order) theorem
; that depends on one or more function variables,
; over which the second-order theorem is universally quantified.
; A theorem is second-order iff it depends on one or more function variables.

(define sothmp ((sothm symbolp) (wrld plist-worldp))
  :mode :program
  (not (null (funvars-of-theorem sothm wrld))))

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
  (and (symbol-symbol-alistp fsbs)
       (no-duplicatesp (alist-keys fsbs))
       (no-trivial-pairsp fsbs))
  :guard-hints (("Goal" :in-theory (enable symbol-symbol-alistp))))

; A second-order function or theorem is instantiated
; by replacing (some of) its function variables
; with other function variables,
; with first-order functions,
; or with other second-order functions.
; A (function variable) instantiation is
; a non-empty function substitution
; whose keys are all function variables
; and whose values are all function symbols.

(define funvar-instp (inst (wrld plist-worldp))
  :verify-guards nil
  (and (fun-substp inst)
       (consp inst)
       (funvar-listp (alist-keys inst) wrld)
       (function-symbol-listp (alist-vals inst) wrld)))

(define funvar-inst-listp (insts (wrld plist-worldp))
  :verify-guards nil
  (if (atom insts)
      (null insts)
    (and (funvar-instp (car insts) wrld)
         (funvar-inst-listp (cdr insts) wrld))))

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

(define sof-instancesp (instmap (wrld plist-worldp))
  :verify-guards nil
  (and (alistp instmap)
       (funvar-inst-listp (alist-keys instmap) wrld)
       (symbol-listp (alist-vals instmap))))

(define get-sof-instance ; read from map (NIL if absent)
  ((inst (funvar-instp inst wrld))
   (instmap (sof-instancesp instmap wrld))
   (wrld plist-worldp))
  :verify-guards nil
  (if (endp instmap)
      nil
    (let ((pair (car instmap)))
      (if (alist-equiv (car pair) inst)
          (cdr pair)
        (get-sof-instance inst (cdr instmap) wrld)))))

(define put-sof-instance ; add to map
  ((inst (funvar-instp inst wrld))
   (fun symbolp)
   (instmap (and (sof-instancesp instmap wrld)
                 ;; must not be already in map:
                 (null (get-sof-instance inst instmap wrld))))
   (wrld plist-worldp))
  :verify-guards nil
  (declare (ignore wrld)) ; only used in guard
  (acons inst fun instmap))

; A table maps second-order functions to their instances.
; Only second-order functions with instances appear in the table.

(table sof-instances nil nil :guard (and (symbolp acl2::key) ; name
                                         (sof-instancesp acl2::val world)))

(define sof-instances ; instances of SOFUN (NIL if none)
  ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :verify-guards nil
  (let ((table (table-alist 'sof-instances wrld)))
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
  ((fsbs fun-substp) (fun symbolp) (wrld plist-worldp))
  :verify-guards nil
  (let ((pair (assoc-eq fun fsbs)))
    (if pair ; FUN is a key of FSBS
        (cdr pair)
      (if (sofunp fun wrld)
          (let* ((fparams (sofun-fparams fun wrld))
                 (subfsbs (restrict-alist fparams fsbs)))
            (if (null subfsbs) ; FUN does not depend on keys of FSBS
                fun
              (let* ((instmap (sof-instances fun wrld))
                     (new-fun (get-sof-instance subfsbs instmap wrld)))
                (if new-fun ; instance of FUN exists
                    new-fun
                  (raise "~x0 has no instance for ~x1."
                              fun fsbs)))))
        fun)))) ; FUN is a function variable or 1st-order function

(defines fun-subst-term/terms
  :verify-guards nil

  (define fun-subst-term
    ((fsbs fun-substp) (term pseudo-termp) (wrld plist-worldp))
    (if (or (variablep term)
            (quotep term))
        term ; no change to individual variables and constants
      (let* ((fn (fn-symb term))
             ;; apply substitution to FN:
             (new-fn (if (symbolp fn)
                         (fun-subst-function fsbs fn wrld)
                       (make-lambda (lambda-formals fn)
                                    (fun-subst-term fsbs
                                                    (lambda-body fn)
                                                    wrld))))
             ;; apply substitution to arguments:
             (new-args (fun-subst-terms fsbs (fargs term) wrld)))
        (cons new-fn new-args))))

  (define fun-subst-terms
    ((fsbs fun-substp) (terms pseudo-term-listp) (wrld plist-worldp))
    (if (endp terms)
        nil
      (cons (fun-subst-term fsbs (car terms) wrld)
            (fun-subst-terms fsbs (cdr terms) wrld)))))

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
  :mode :program

  (define ext-fun-subst-term
    ((term pseudo-termp) (fsbs fun-substp) (wrld plist-worldp))
    (if (or (variablep term)
            (quotep term))
        fsbs ; no 2nd-order functions in individual variables and constants
      (let* ((fn (fn-symb term))
             (fsbs (if (symbolp fn)
                       (ext-fun-subst-function fn fsbs wrld)
                     (ext-fun-subst-term (lambda-body fn) fsbs wrld))))
        (ext-fun-subst-terms (fargs term) fsbs wrld))))

  (define ext-fun-subst-terms
    ((terms pseudo-term-listp) (fsbs fun-substp) (wrld plist-worldp))
    (if (endp terms)
        fsbs
      (let ((fsbs (ext-fun-subst-term (car terms) fsbs wrld)))
        (ext-fun-subst-terms (cdr terms) fsbs wrld))))

  (define ext-fun-subst-function
    ((fun symbolp) (fsbs fun-substp) (wrld plist-worldp))
    (cond
     ((assoc fun fsbs) fsbs) ; pair already present
     ((sofunp fun wrld)
      (b* ((fparams (sofun-fparams fun wrld))
           (subfsbs (restrict-alist fparams fsbs))
           ((if (null subfsbs)) fsbs) ; FUN unchanged under FSBS
           (instmap (sof-instances fun wrld))
           (funinst (get-sof-instance subfsbs instmap wrld))
           ((unless funinst)
            (raise "~x0 has no instance for ~x1." fun fsbs))
           (fsbs (acons fun funinst fsbs))) ; extend FSBS
          (case (sofun-kind fun wrld)
            ((plain quant) (ext-fun-subst-term (ubody fun wrld) fsbs wrld))
            (choice (ext-fun-subst-term (defchoose-body fun wrld) fsbs wrld)))))
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

(define sothm-inst-pairs ((fsbs fun-substp) (wrld plist-worldp))
  :mode :program
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (if (quant-sofunp 1st wrld)
          (let ((1st-wit (defun-sk-info->witness (defun-sk-check 1st wrld)))
                (2nd-wit (defun-sk-info->witness (defun-sk-check 2nd wrld))))
            (cons (list 1st 2nd) ; pair from FSBS
                  (cons (list 1st-wit 2nd-wit) ; pair of witnesses
                        (sothm-inst-pairs (cdr fsbs) wrld))))
        (cons (list 1st 2nd) ; pair from FSBS
              (sothm-inst-pairs (cdr fsbs) wrld))))))

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
;   FUN2 is introduced by a DEFUN),
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

(define sothm-inst-facts ((fsbs fun-substp) (wrld plist-worldp))
  :mode :program
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (cond ((or (plain-sofunp 1st wrld)
                 (choice-sofunp 1st wrld))
             (cons 2nd (sothm-inst-facts (cdr fsbs) wrld)))
            ((quant-sofunp 1st wrld)
             (cons (defun-sk-info->rewrite-name (defun-sk-check 2nd wrld))
                   (sothm-inst-facts (cdr fsbs) wrld)))
            (t (sothm-inst-facts (cdr fsbs) wrld))))))

; Instances of second-order theorems are proved using the ACL2 proof builder.
; Each such instance is proved by
; first using the :FUNCTIONAL-INSTANCE described above,
; then using the facts described above on the subgoals.
; Each sugoal only needs a subset of those facts,
; but for simplicity all the facts are used for each subgoal,
; using the proof builder :REPEAT command.
; Since sometimes the facts are not quite identical to the subgoals,
; the proof builder :PROVE command is used to iron out any such differences.

(define sothm-inst-proof
  ((sothm symbolp) (fsbs fun-substp) (wrld plist-worldp))
  :mode :program
  `(:instructions
    ((:use (:functional-instance ,sothm ,@(sothm-inst-pairs fsbs wrld)))
     (:repeat (:then (:use ,@(sothm-inst-facts fsbs wrld)) :prove)))))

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
; Supplying :OTF-FLG has no effect because the proof is via the proof builder.

; check that SOTHM-INST has the form (SOTHM (F1 . G1) ... (Fm . Gm)),
; where SOTHM is a 2nd-order theorem
; and ((F1 . G1) ... (Fm . Gm)) is an instantiation:
(define check-sothm-inst (sothm-inst (wrld plist-worldp))
  :mode :program
  (and (true-listp sothm-inst)
       (>= (len sothm-inst) 2)
       (sothmp (car sothm-inst) wrld)
       (funvar-instp (cdr sothm-inst) wrld)))

(define defthm-inst-event (thm sothm-inst rest (wrld plist-worldp))
  :mode :program
  (b* (;; THM is the name of the new theorem:
       ((unless (symbolp thm)) (raise "~x0 must be a name." thm))
       ;; after THM there is (SOTHM (F1 . G1) ... (Fm . Gm)):
       ((unless (check-sothm-inst sothm-inst wrld))
        (raise "~x0 must be the name of a second-order theorem ~
                followed by the pairs of an instantiation."
               sothm-inst))
       ;; decompose (SOTHM (F1 . G1) ... (Fm . Gm)):
       (sothm (car sothm-inst))
       (inst (cdr sothm-inst))
       ;; every Fi must be a function variable that SOTHM depends on:
       ((unless (subsetp (alist-keys inst) (funvars-of-theorem sothm wrld)))
        (raise "Each function variable key of ~x0 must be ~
                among function variable that ~x1 depends on."
               inst sothm))
       ;; apply ((F1 . G1) ... (Fm . Gm)) to the formula of SOTHM:
       (sothm-formula (formula sothm nil wrld))
       (thm-formula (fun-subst-term inst sothm-formula wrld))
       ;; construct the proof from the instantiation:
       (fsbs (ext-fun-subst-term sothm-formula inst wrld))
       (thm-proof (sothm-inst-proof sothm fsbs wrld)))
      ;; generate event (REST is RULE-CLASSES, if present):
      `(defthm ,thm ,thm-formula ,@thm-proof ,@rest)))

(defmacro defthm-inst (thm uqfvars-or-sothminst &rest rest)
  `(make-event
    (defthm-inst-event ',thm ',uqfvars-or-sothminst ',rest (w state))))

(defmacro show-defthm-inst (thm uqfvars-or-sothminst &rest rest)
  `(defthm-inst-event ',thm ',uqfvars-or-sothminst ',rest (w state)))

(defmacro acl2::defthm-inst (&rest args)
  `(defthm-inst ,@args))

(defmacro acl2::show-defthm-inst (&rest args)
  `(show-defthm-inst ,@args))

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
; and the optional :VERIFY-GUARDS, :SKOLEM-NAME, and :REWRITE
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
; DEFUN-INST directly checks the form except the values of the options,
; relying on DEFUN, DEFCHOOSE, or DEFUN-SK to check them.
;
; If SOFUN is a plain second-order function, DEFUN-INST generates a DEFUN.
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
; The :VERIFY-GUARDS option in DEFUN-INST can be used only if SOFUN is plain.
; Its meaning is the same as in DEFUN.
; If present, it is passed through to DEFUN;
; if absent, it is determined by whether SOFUN is guard-verified or not.
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
; The :SKOLEM-NAME option in DEFUN-INST can be used
; only if SOFUN is a quantifier second-order function.
; Its meaning is the same as in DEFUN-SK.
;
; The :REWRITE option in DEFUN-INST can be used
; only if SOFUN is a quantifier second-order function with FORALL.
; Its meaning is the same as in DEFUN-SK,
; except that if :REWRITE is absent and the quantifier is FORALL,
; then :REWRITE is inherited from SOFUN.
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
; Prior to the event that introduces the new function,
; DEFUN-INST generates local events
; to avoid errors due to ignored or irrelevant formals in the new function
; (which may happen if SOFUN had ignored or irrelevant formals).
;
; For now, SOFT does not support the transitivity of instantiations,
; i.e. that if F is an instance of G and G is an instance of H,
; then F is also an instance of H.

; check that SOFUN-INST had the form (SOFUN (F1 . G1) ... (Fm . Gm)),
; where SOFUN is a 2nd-order function
; and ((F1 . G1) ... (Fm . Gm)) is an instantiation:
(define check-sofun-inst (sofun-inst (wrld plist-worldp))
  :verify-guards nil
  (and (true-listp sofun-inst)
       (>= (len sofun-inst) 2)
       (sofunp (car sofun-inst) wrld)
       (funvar-instp (cdr sofun-inst) wrld)))

; extract keywords from the even positions of a list:
(define keywords-of-keyword-value-list ((kvlist keyword-value-listp))
  (if (endp kvlist)
      nil
    (cons (car kvlist) (keywords-of-keyword-value-list (cddr kvlist)))))

; events to introduce FUN
; and to add it to the table of second-order functions if it is second-order,
; when SOFUN is a plain second-order function:
(define defun-inst-plain-events
  ((fun symbolp)
   (fparams (or (funvar-setp fparams wrld) ; FUN is 2nd-order
                (null fparams)))           ; FUN is 1st-order
   (sofun (plain-sofunp sofun wrld))
   inst
   (options keyword-value-listp)
   (wrld plist-worldp))
  :mode :program
  (b* (;; the keyed options can only include :VERIFY-GUARDS:
       ((unless (subsetp (keywords-of-keyword-value-list options)
                         '(:verify-guards)))
        (raise "~x0 must include only :VERIFY-GUARDS, ~
                because ~x1 is a plain second-order function."
               options sofun))
       ;; if present, use the :VERIFY-GUARDS option for FUN,
       ;; otherwise FUN is guard-verified iff SOFUN is:
       (verify-guards (let ((verify-guards-option
                             (assoc-keyword :verify-guards options)))
                        (if verify-guards-option
                            (cadr verify-guards-option)
                          (guard-verified-p sofun wrld))))
       ;; retrieve body, measure, and guard of SOFUN:
       (sofun-body (ubody sofun wrld))
       (sofun-measure (if (recursivep sofun nil wrld)
                          (measure sofun wrld)
                        nil))
       (sofun-guard (guard sofun nil wrld))
       ;; extend instantiation with (SOFUN . FUN) if SOFUN is recursive
       ;; (so that recursive calls to SOFUN can be properly replaced with FUN)
       ;; and apply it to the body of SOFUN:
       (fsbs (if sofun-measure (acons sofun fun inst) inst))
       (fun-body (fun-subst-term fsbs sofun-body wrld))
       ;; apply instantiation to the measure and guard of SOFUN:
       (fun-measure (fun-subst-term inst sofun-measure wrld))
       (fun-guard (fun-subst-term inst sofun-guard wrld))
       ;; construct the termination proof from the instantiation, if recursive:
       (sofun-tt-name `(:termination-theorem ,sofun))
       (sofun-tt-formula (and (recursivep sofun nil wrld)
                              (termination-theorem sofun wrld)))
       (fsbs (ext-fun-subst-term sofun-tt-formula inst wrld))
       (fun-tt-proof (sothm-inst-proof sofun-tt-name fsbs wrld))
       ;; :HINTS of FUN if recursive, otherwise NIL:
       (hints (if fun-measure `(:hints (("Goal" ,@fun-tt-proof))) nil))
       ;; :MEASURE of FUN if recursive, otherwise NIL:
       (measure (if fun-measure `(:measure ,fun-measure) nil))
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
    `((defun ,fun ,(formals sofun wrld)
        (declare (xargs :guard ,fun-guard
                        :verify-guards ,verify-guards
                        ,@measure
                        ,@hints))
        ,fun-body)
      ,@table-event)))

; events to introduce FUN
; and to add it to the table of second-order functions if it second-order,
; when SOFUN is a choice second-order function:
(define defun-inst-choice-events
  ((fun symbolp)
   (fparams (or (funvar-setp fparams wrld) ; FUN is 2nd-order
                (null fparams)))           ; FUN is 1st-order
   (sofun (choice-sofunp sofun wrld))
   inst
   (options keyword-value-listp)
   (wrld plist-worldp))
  :mode :program
  (b* (;; the options must be absent:
       ((unless (null options))
        (raise "~x0 must include no options, ~
                because ~x1 is a choice second-order function."
               options sofun))
       ;; retrieve bound variables of SOFUN:
       (bound-vars (defchoose-bound-vars sofun wrld))
       ;; apply instantiation to body of SOFUN:
       (sofun-body (defchoose-body sofun wrld))
       (fun-body (fun-subst-term inst sofun-body wrld))
       ;; info about FUN to add to the table of second-order functions
       ;; (if FUN is second-order):
       (info (list 'choice fparams))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
    ;; generated list of events:
    `((defchoose ,fun ,bound-vars ,(formals sofun wrld)
        ,fun-body
        :strengthen ,(defchoose-strengthen sofun wrld))
      ,@table-event)))

; events to introduce FUN
; and to add it to the table of second-order functions if it is second-order,
; when SOFUN is a quantifier second-order function:
(define defun-inst-quant-events
  ((fun symbolp)
   (fparams (or (funvar-setp fparams wrld) ; FUN is 2nd-order
                (null fparams)))           ; FUN is 1st-order
   (sofun (quant-sofunp sofun wrld))
   inst
   (options keyword-value-listp)
   (wrld plist-worldp))
  :mode :program
  (b* (;; the options must include only :SKOLEM-NAME and :REWRITE:
       ((unless (subsetp (keywords-of-keyword-value-list options)
                         '(:skolem-name :rewrite)))
        (raise "~x0 must include only :SKOLEM-NAME and :REWRITE, ~
                because ~x1 is a quantifier second-order function."
               options sofun))
       ;; retrieve DEFUN-SK-specific constituents of SOFUN:
       (sofun-info (defun-sk-check sofun wrld))
       ;; retrieve bound variables and quantifier of SOFUN:
       (bound-vars (defun-sk-info->bound-vars sofun-info))
       (quant (defun-sk-info->quantifier sofun-info))
       ;; apply instantiation to the matrix of SOFUN:
       (sofun-matrix (defun-sk-info->matrix sofun-info))
       (fun-matrix (fun-subst-term inst sofun-matrix wrld))
       ;; the value of :REWRITE for FUN
       ;; is determined from the supplied value (if any),
       ;; otherwise it is inherited from SOFUN:
       (rewrite-option (assoc-keyword :rewrite options))
       (rewrite
        (if rewrite-option
            (cadr rewrite-option)
          (let ((qrkind (defun-sk-info->rewrite-kind sofun-info)))
            (case qrkind
              (:default :default)
              (:direct :direct)
              (:custom
               ;; apply instantiation to that term
               ;; and use result as :REWRITE for FUN
               ;; (the instantiation is extended with (SOFUN . FUN)
               ;; because the term presumably references SOFUN):
               (let* ((fsbs (acons sofun fun inst))
                      (rule-name (defun-sk-info->rewrite-name sofun-info))
                      (term (formula rule-name nil wrld)))
                 (fun-subst-term fsbs term wrld)))))))
       ;; :SKOLEM-NAME of FUN if supplied, otherwise NIL:
       (skolem-name (let ((skolem-name-option
                           (assoc-keyword :skolem-name options)))
                      (if skolem-name-option
                          `(:skolem-name ,(cadr skolem-name-option))
                        nil)))
       ;; apply instantiation to the guard of SOFUN:
       (sofun-guard (guard sofun nil wrld))
       (fun-guard (fun-subst-term inst sofun-guard wrld))
       ;; :WITNESS-DCLS for FUN:
       (wit-dcl `(declare (xargs :guard ,fun-guard :verify-guards nil)))
       ;; info about FUN to add to the table of second-order functions
       ;; (if FUN is second-order):
       (info (list 'quant fparams))
       ;; singleton list of event to add FUN
       ;; to the table of second-order functions,
       ;; or NIL if FUN is first-order:
       (table-event (if fparams ; 2nd-order
                        (list `(table second-order-functions ',fun ',info))
                      nil)))
    ;; generated list of events:
    `((defun-sk ,fun ,(formals sofun wrld)
        (,quant ,bound-vars ,fun-matrix)
        :strengthen ,(defun-sk-info->strengthen sofun-info)
        :quant-ok t
        ,@(and (eq quant 'forall)
               (list :rewrite rewrite))
        ,@skolem-name
        :witness-dcls (,wit-dcl))
      ,@table-event
      (value-triple (check-qrewrite-rule-funvars ',fun (w state))))))

(define defun-inst-event (fun fparams-or-sofuninst rest (wrld plist-worldp))
  :mode :program
  (b* (;; FUN is the name of the new function:
       ((unless (symbolp fun)) (raise "~x0 must be a name." fun))
       ;; after FUN there is (FVAR1 ... FVARn) if FUN is 2nd-order,
       ;; otherwise there is (SOFUN (F1 . G1) ... (Fm . Gm)):
       (2nd-order ; T if FUN is 2nd-order
        (funvar-setp fparams-or-sofuninst wrld))
       ((unless (or 2nd-order
                    (check-sofun-inst fparams-or-sofuninst wrld)))
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
                         (check-sofun-inst (car rest) wrld))))
        (raise "~x0 must start with the name of a second-order function ~
                followed by an instantiation."
               rest))
       (sofun-inst (if 2nd-order (car rest) fparams-or-sofuninst))
       ;; decompose (SOFUN (F1 . G1) ... (Fm . Gm)):
       (sofun (car sofun-inst))
       (inst (cdr sofun-inst))
       ;; every Fi must be a function parameter of SOFUN:
       ((unless (subsetp (alist-keys inst) (sofun-fparams sofun wrld)))
        (raise "Each function variable key of ~x0 must be ~
                among the function parameters ~x1 of ~x2."
               inst (sofun-fparams sofun wrld) sofun))
       ;; the options are REST if FUN is 1st-order,
       ;; otherwise they come after (SOFUN (F1 . G1) ... (Fm . Gm)) in REST:
       (options (if 2nd-order (cdr rest) rest))
       ;; the options must be a list
       ;; whose even-position elements are unique keyword:
       ((unless (keyword-value-listp options))
        (raise "~x0 must be a list of keyed options." options))
       ((unless (no-duplicatesp (keywords-of-keyword-value-list options)))
        (raise "~x0 must have unique keywords." options))
       ;; events specific to the kind of SOFUN:
       (spec-events
        (case (sofun-kind sofun wrld)
          (plain
           (defun-inst-plain-events fun fparams sofun inst options wrld))
          (choice
           (defun-inst-choice-events fun fparams sofun inst options wrld))
          (quant
           (defun-inst-quant-events fun fparams sofun inst options wrld))))
       ;; updated entry for SOFUN
       ;; in table of instances of second-order functions:
       (instmap (sof-instances sofun wrld))
       (new-instmap (put-sof-instance inst fun instmap wrld)))
    ;; generated event:
    `(encapsulate
       ()
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       ,@spec-events
       (table sof-instances ',sofun ',new-instmap)
       (value-triple (check-fparams-dependency ',fun
                                               ',(sofun-kind sofun wrld)
                                               ',fparams
                                               (w state))))))

(defmacro defun-inst (fun fparams-or-sofuninst &rest rest)
  `(make-event
    (defun-inst-event ',fun ',fparams-or-sofuninst ',rest (w state))))

(defmacro show-defun-inst (fun fparams-or-sofuninst &rest rest)
  `(defun-inst-event ',fun ',fparams-or-sofuninst ',rest (w state)))

(defmacro acl2::defun-inst (&rest args)
  `(defun-inst ,@args))

(defmacro acl2::show-defun-inst (&rest args)
  `(show-defun-inst ,@args))

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
