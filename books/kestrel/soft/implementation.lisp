; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/std/system/defchoose-queries" :dir :system)
(include-book "kestrel/std/system/definedp" :dir :system)
(include-book "kestrel/std/system/defun-sk-queries" :dir :system)
(include-book "kestrel/std/system/function-symbol-listp" :dir :system)
(include-book "kestrel/std/system/guard-verified-p" :dir :system)
(include-book "kestrel/std/system/irecursivep" :dir :system)
(include-book "kestrel/std/system/measure" :dir :system)
(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/std/system/well-founded-relation" :dir :system)
(include-book "kestrel/std/system/well-founded-relation-plus" :dir :system)
(include-book "kestrel/std/system/uguard" :dir :system)
(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/alists/alist-equiv" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft-implementation
  :parents (soft)
  :short "Implementation of SOFT."
  :order-subtopics t
  :default-parent t)

(define *-listp (stars)
  :returns (yes/no booleanp)
  :short "Recognize true lists of @('*')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "These lists are used to indicate
     the number of arguments of function variables
     in @(tsee defunvar).")
   (xdoc::p
    "Any @('*') symbol (i.e. in any package) is allowed.
     Normally, the @('*') in the current package should be used
     (without package qualifier),
     which is often the one from the main Lisp package,
     which other packages generally import."))
  (if (atom stars)
      (null stars)
    (and (symbolp (car stars))
         (equal (symbol-name (car stars)) "*")
         (*-listp (cdr stars)))))

(defsection function-variables-table
  :short "Table of function variables."
  :long
  (xdoc::topstring-p
   "The names of declared function variables
    are stored as keys in a @(tsee table).
    No values are associated to these keys, so the table is essentially a set.
    Note that the arity of a function variable
    can be retrieved from the @(see world).")

  (table function-variables nil nil :guard (and (symbolp acl2::key)
                                                (null acl2::val))))

(define funvarp (funvar (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize names of function variables."
  :long
  (xdoc::topstring-p
   "These are symbols that name declared function variables,
    i.e. that are in the table of function variables.")
  (let ((table (table-alist 'function-variables wrld)))
    (and (symbolp funvar)
         (not (null (assoc-eq funvar table))))))

(define defunvar-fn ((inputs true-listp)
                     (call pseudo-event-formp "Call to @(tsee defunvar).")
                     (ctx "Context for errors.")
                     state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event maybe-pseudo-event-formp)
               state)
  :verify-guards nil
  :short "Validate the inputs to @(tsee defunvar)
          and generate the event form to submit."
  :long
  (xdoc::topstring-p
   "Similary to @(tsee *-listp),
    any @('*') and @('=>') symbol (i.e. in any package) is allowed.")
  (b* ((wrld (w state))
       ((unless (>= (len inputs) 4))
        (er-soft+ ctx t nil
                  "At least four inputs must be supplied, not ~n0."
                  (len inputs)))
       (funvar (first inputs))
       (arguments (second inputs))
       (arrow (third inputs))
       (result (fourth inputs))
       (options (nthcdr 4 inputs))
       ((unless (symbolp funvar))
        (er-soft+ ctx t nil
                  "The first input must be a symbol, but ~x0 is not."
                  funvar))
       ((unless (*-listp arguments))
        (er-soft+ ctx t nil
                  "The second input must be a list (* ... *), but ~x0 is not."
                  arguments))
       ((unless (and (symbolp arrow)
                     (equal (symbol-name arrow) "=>")))
        (er-soft+ ctx t nil
                  "The third input must be =>, but ~x0 is not."
                  arrow))
       ((unless (and (symbolp result)
                     (equal (symbol-name result) "*")))
        (er-soft+ ctx t nil
                  "The fourth input must be *, but ~x0 is not."
                  result))
       ((unless (or (null options)
                    (and (= (len options) 2)
                         (eq (car options) :print))))
        (er-soft+ ctx t nil
                  "After the * input there may be at most one :PRINT option, ~
                   but instead ~x0 was supplied."
                  options))
       (print (if options
                  (cadr options)
                nil))
       ((unless (member-eq print '(nil :all)))
        (er-soft+ ctx t nil
                  "The :PRINT input must be NIL or :ALL, but ~x0 is not."
                  print))
       ((when (funvarp funvar wrld))
        (b* ((arity (arity funvar wrld)))
          (if (= arity (len arguments))
              (prog2$ (cw "~%The call ~x0 is redundant.~%" call)
                      (value `(value-triple :invisible)))
            (er-soft+ ctx t nil "A function variable ~x0 with arity ~x1 ~
                                 already exists.~%" funvar arity))))
       (event `(progn
                 (defstub ,funvar ,arguments ,arrow ,result)
                 (table function-variables ',funvar nil)
                 (value-triple ',funvar)))
       (event (restore-output? (eq print :all) event)))
    (value event)))

(defsection defunvar-implementation
  :short "Implementation of @(tsee defunvar)."
  :long
  "@(def defunvar)
   @(def acl2::defunvar)"

  (defmacro defunvar (&whole call &rest inputs)
    `(make-event-terse (defunvar-fn
                         ',inputs
                         ',call
                         (cons 'defunvar ',(if (consp inputs) (car inputs) nil))
                         state)))

  (defmacro acl2::defunvar (&rest inputs)
    `(defunvar ,@inputs)))

(defsection show-defunvar
  :short "Show the event form generated by @(tsee defunvar),
          without submitting them."
  :long
  "@(def show-defunvar)
   @(def acl2::show-defunvar)"

  (defmacro show-defunvar (&whole call
                                  funvar arguments arrow result &key print)
    `(defunvar-fn
       ',funvar
       ',arguments
       ',arrow
       ',result
       ',print
       ',call
       (cons 'defunvar ',funvar)
       state))

  (defmacro acl2::show-defunvar (&rest args)
    `(show-defunvar ,@args)))

(define funvar-listp (funvars (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recoegnize true lists of function variables."
  (if (atom funvars)
      (null funvars)
    (and (funvarp (car funvars) wrld)
         (funvar-listp (cdr funvars) wrld))))

(defsection second-order-functions-table
  :short "Table of second-order functions."
  :long
  (xdoc::topstring-p
   "The names of declared second-order functions
    are stored as keys in a @(see table),
    associated with the function variables they depend on.")

  (table second-order-functions nil nil
    :guard (and (symbolp acl2::key)
                (funvar-listp acl2::val world))))

(define sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize names of second-order functions."
  (let ((table (table-alist 'second-order-functions wrld)))
    (and (symbolp sofun)
         (not (null (assoc-eq sofun table))))))

(define sofun-kindp (kind)
  :returns (yes/no booleanp)
  :short "Recognize symbols that denote
          the kinds of second-order functions supported by SOFT."
  :long
  (xdoc::topstring
   (xdoc::p
    "Following the terminology used in the Workshop paper,
     in the implementation we use:")
   (xdoc::ul
    (xdoc::li
     "@('plain') for second-order functions introduced
      via @(tsee defun2).")
    (xdoc::li
     "@('choice') for second-order functions introduced
      via @(tsee defchoose2).")
    (xdoc::li
     "@('quant') for second-order functions introduced
      via @(tsee defun-sk2).")))
  (or (eq kind 'plain)
      (eq kind 'choice)
      (eq kind 'quant)))

(define sofun-kind ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :returns (kind "A @(tsee sofun-kindp).")
  :verify-guards nil
  :short "Kind of a second-order function."
  (cond ((defchoosep sofun wrld) 'choice)
        ((defun-sk-p sofun wrld) 'quant)
        (t 'plain)))

(define plain-sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize plain second-order functions."
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'plain)))

(define choice-sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize choice second-order functions."
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'choice)))

(define quant-sofunp (sofun (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize quantifier second-order functions."
  (and (sofunp sofun wrld)
       (eq (sofun-kind sofun wrld) 'quant)))

(define sofun-funvars ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :verify-guards nil
  :short "Function variables that a second-order function depends on."
  (let ((table (table-alist 'second-order-functions wrld)))
    (cdr (assoc-eq sofun table))))

(defines funvars-of-term/terms
  :verify-guards nil
  :short "Function variables that terms depend on."
  :long
  (xdoc::topstring
   (xdoc::p
    "A term may depend on a function variable directly
     (when the function variable occurs in the term)
     or indirectly
     (when a the second-order function that occurs in the term
     depends on the function variable).")
   (xdoc::p
    "Note that, in the following code,
     if @('(sofunp fn wrld)') is @('nil'),
     then @('fn') is a first-order function,
     which depends on no function variables.")
   (xdoc::p
    "The returned list may contain duplicates.")
   (xdoc::@def "funvars-of-term")
   (xdoc::@def "funvars-of-terms"))

  (define funvars-of-term ((term pseudo-termp) (wrld plist-worldp))
    :returns (funvars "A @(tsee funvar-listp).")
    (if (or (variablep term)
            (quotep term))
        nil
      (let* ((fn (fn-symb term))
             (fn-vars
              (if (flambdap fn)
                  (funvars-of-term (lambda-body fn) wrld)
                (if (funvarp fn wrld)
                    (list fn)
                  (if (sofunp fn wrld)
                      (sofun-funvars fn wrld)
                    nil)))))
        (append fn-vars (funvars-of-terms (fargs term) wrld)))))

  (define funvars-of-terms ((terms pseudo-term-listp) (wrld plist-worldp))
    :returns (funvars "A @(tsee funvar-listp).")
    (if (endp terms)
        nil
      (append (funvars-of-term (car terms) wrld)
              (funvars-of-terms (cdr terms) wrld)))))

(define funvars-of-plain-fn ((fun symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a plain second-order function or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Plain second-order functions and their instances
     may depend on function variables
     via their defining bodies,
     via their measures (absent in non-recursive functions),
     and via their guards.
     For now recursive second-order functions (which are all plain)
     and their instances
     are only allowed to use @(tsee o<) as their well-founded relation,
     and so plain second-order functions and their instances
     may not depend on function variables via their well-founded relations.")
   (xdoc::p
    "Note that if the function is recursive,
     the variable @('measure') in the following code is @('nil'),
     and @(tsee funvars-of-term) applied to that yields @('nil').")
   (xdoc::p
    "The returned list may contain duplicates."))
  (let* ((body (ubody fun wrld))
         (measure (if (recursivep fun nil wrld)
                      (measure fun wrld)
                    nil))
         (guard (uguard fun wrld))
         (body-funvars (funvars-of-term body wrld))
         (measure-funvars (funvars-of-term measure wrld))
         (guard-funvars (funvars-of-term guard wrld)))
    (append body-funvars
            measure-funvars
            guard-funvars)))

(define funvars-of-choice-fn ((fun symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a choice second-order function or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Choice second-order functions and their instances
     may depend on function variables via their defining bodies.")
   (xdoc::p
    "The returned list may contain duplicates."))
  (funvars-of-term (defchoose-body fun wrld) wrld))

(define funvars-of-quantifier-fn ((fun symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a quantifier second-order function or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Quantifier second-order functions and their instances
     may depend on function variables
     via their matrices
     and via their guards (which are introduced via @(':witness-dcls')).")
   (xdoc::p
    "The returned list may contain duplicates."))
  (let* ((matrix (defun-sk-matrix fun wrld))
         (guard (uguard fun wrld))
         (matrix-funvars (funvars-of-term matrix wrld))
         (guard-funvars (funvars-of-term guard wrld)))
    (append matrix-funvars
            guard-funvars)))

(define funvars-of-thm ((thm symbolp) (wrld plist-worldp))
  :returns (funvars "A @(tsee funvar-listp).")
  :mode :program
  :short "Function variables depended on
          by a second-order theorem or by an instance of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "Second-order theorems and their instances
     may depend on function variables via their formulas.")
   (xdoc::p
    "The returned list may contain duplicates."))
  (funvars-of-term (formula thm nil wrld) wrld))

(define ensure-wfrel-o< ((fn symbolp) ctx state)
  :returns (mv erp (nothing null) state)
  :short "Ensure that a function, if logic-mode and recursive,
          has @(tsee o<) as well-founded relation."
  :long
  (xdoc::topstring-p
   "For now, we only support logic-mode recursive second-order functions
    with the default well-founded relation (i.e. @(tsee o<)).
    This might be relaxed in the future.")
  (b* ((wrld (w state))
       ((unless (logicp fn wrld)) (value nil))
       ((unless (irecursivep fn wrld)) (value nil))
       (wfrel (well-founded-relation+ fn wrld))
       ((when (eq wfrel 'o<)) (value nil)))
    (er-soft+ ctx t nil
              "The well-founded relation of the recursive function ~x0 ~
               must be O<, but it is ~x1 instead."
              fn wfrel)))

(define ensure-defun-sk-rule-same-funvars ((fn symbolp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :mode :program
  :short "Ensure that a function, if introduced by @(tsee defun-sk),
          has an associated rewrite rule (the one generated by @(tsee defun-sk)
          that depends on exactly the same function variables
          that the function's matrix depends on."
  :long
  (xdoc::topstring-p
   "We collect
    the function variables that the @(tsee defun-sk) matrix depends on
    and the ones that the @(tsee defun-sk) rewrite rule depends on;
    we ensure that they are the same function variables.
    It seems unlikely that this check will ever fail in practice,
    but @(tsee defun-sk) allows custom rules (for universal quantifiers)
    that might somehow change the dependencies on function variables;
    for now we do not support this situation,
    but we might recosider this if some compelling example comes up.
    Unless the rewrite rule is a custom one,
    this check is always expected to pass.")
  (b* ((wrld (w state))
       ((unless (defun-sk-p fn wrld)) (value nil))
       (rule-name (defun-sk-rewrite-name fn wrld))
       (rule-body (formula rule-name nil wrld))
       (fn-matrix (defun-sk-matrix fn wrld))
       (rule-funvars (funvars-of-term rule-body wrld))
       (matrix-funvars (funvars-of-term fn-matrix wrld))
       ((when (set-equiv rule-funvars matrix-funvars)) (value nil))
       ((unless (eq (defun-sk-rewrite-kind fn wrld) :custom))
        (value (raise "Internal error: ~
                       the DEFUN-SK function ~x0 has a matrix ~x1
                       that depends on the function variables ~&2 ~
                       but a non-custom rewrite rule ~x3
                       that depends on the function variables ~&4.
                       This was not expected to happen."
                      fn fn-matrix matrix-funvars rule-body rule-funvars))))
    (er-soft+ ctx t nil
              "The DEFUN-SK function ~x0 has a matrix ~x1
               that depends on the function variables ~&2 ~
               but a custom rewrite rule ~x3
               that depends on the function variables ~&4."
              fn fn-matrix matrix-funvars rule-body rule-funvars)))

(define defsoft-fn (fn ctx state)
  :returns (mv erp event state)
  :mode :program
  :short "Generate the event submitted by @(tsee defsoft)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(tsee defsoft) macro records an ACL2 function
     as a (SOFT) second-order function.
     This macro will become the primary one
     to introduce second-order functions,
     and @(tsee defun2), @(tsee defchoose2), and @(tsee defun-sk2)
     will be redefined as @(tsee defun), @(tsee defchoose), and @(tsee defun-sk)
     followed by @(tsee defsoft).")
   (xdoc::p
    "The input @('fn') must be a symbol that denotes an existing function
     that is introduced by @(tsee defchoose),
     or otherwise is introduced by @(tsee defun-sk),
     or otherwise has an unnormalized body
     (which implies that is is introduced by @(tsee defun)).
     Note that @(tsee defun-sk) functions
     are internally introduced by @(tsee defun),
     so it is important to check for @(tsee defun-sk) first.
     Functions introduced by @(tsee defun) but without an unnormalized body
     (such as the built-in program-mode functions)
     are disallowed because we cannot calculate
     the function variables that such functions depend on.
     For the same reason,
     constrained functions introduced by @(tsee encapsulate) are disallowed.")
   (xdoc::p
    "We collect the function variables that the function depends on,
     directly or indirecty; there must be at least one.
     If the function is introduced by @(tsee defun-sk),
     we also ensure that the associated rewrite rule
     does not depend on additional function variables.
     If the function is recursive,
     we also ensure that the well-founded relation is @(tsee o<)."))
  (b* ((wrld (w state))
       ((unless (symbolp fn))
        (er-soft+ ctx t nil
                  "The input must be a symbol, but it is ~x0 instead."
                  fn))
       ((unless (function-symbolp fn wrld))
        (er-soft+ ctx t nil
                  "The symbol ~x0 must be a function symbol, ~
                   but it is not."
                  fn))
       ((unless (or (defchoosep fn wrld)
                    (defun-sk-p fn wrld)
                    (ubody fn wrld)))
        (er-soft+ ctx t nil
                  "The function ~x0 must ~
                   be introduced by DEFCHOOSE, ~
                   be introduced by DEFUN-SK, ~
                   or have a non-NIL unnormalized body."
                  fn))
       (funvars (cond ((defchoosep fn wrld) (funvars-of-choice-fn fn wrld))
                      ((defun-sk-p fn wrld) (funvars-of-quantifier-fn fn wrld))
                      (t (funvars-of-plain-fn fn wrld))))
       (funvars (remove-duplicates-eq funvars))
       ((unless (consp funvars))
        (er-soft+ ctx t nil
                  "The function ~x0 is not second-order:
                   it depends on no function variables, directly or indirectly."
                  fn))
       (table-event `(table second-order-functions ',fn ',funvars))
       (print-event `(cw-event "The second-order function ~x0 ~
                                depends on the function variables ~x1.~%"
                               ',fn ',funvars))
       ((er &) (ensure-wfrel-o< fn ctx state))
       ((er &) (ensure-defun-sk-rule-same-funvars fn ctx state)))
    (value
     `(progn
        ,table-event
        ,print-event
        (value-triple :invisible)))))

(defmacro+ defsoft (fn)
  :short "Record a function as a second-order function."
  `(make-event-terse (defsoft-fn ',fn (cons 'defsoft ',fn) state)))

(defmacro acl2::defsoft (&rest args)
  `(defsoft ,@args))

(define check-wfrel-o< ((fun symbolp) (wrld plist-worldp))
  :returns (err-msg? maybe-msgp)
  :verify-guards nil
  :short "Check if a recursive second-order function, or an instance of it,
          uses @(tsee o<) as well-founded relation."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a recursive second-order function, or an instance thereof,
     is introduced,
     the submitted event form first introduces the function,
     and then checks whether its well-founded relation is @(tsee o<).
     The following code performs this check.")
   (xdoc::p
    "If the check is satisfied, @('nil') is returned.
     Otherwise, an error message is returned."))
  (if (recursivep fun nil wrld)
      (let ((wfrel (well-founded-relation fun wrld)))
        (if (eq wfrel 'o<)
            nil
          (msg "~x0 must use O< as well-founded relation, not ~x1.~%"
               fun wfrel)))
    nil))

(define check-qrewrite-rule-funvars ((fun symbolp) (wrld plist-worldp))
  :returns (err-msg? "A @(tsee maybe-msgp).")
  :mode :program
  :short "Check if the rewrite rule of a quantifier second-order function,
          or of an instance of it,
          depends exactly on the same function variables
          that the matrix of the function depends on."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a quantifier second-order function, or an instance thereof,
     is introduced,
     the submitted event form first introduces the function,
     and then checks whether its rewrite rule depends
     exactly on the same function variables
     that the matrix of the function depends on.
     The following code performs this check.")
   (xdoc::p
    "If the check is satisfied, @('nil') is returned.
     Otherwise, an error message is returned.")
   (xdoc::p
    "This check is relevant when the rewrite rule is a custom one.
     Otherwise, it is a redundant check."))
  (let* ((rule-name (defun-sk-rewrite-name fun wrld))
         (rule-body (formula rule-name nil wrld))
         (fun-matrix (defun-sk-matrix fun wrld)))
    (if (set-equiv (funvars-of-term rule-body wrld)
                   (funvars-of-term fun-matrix wrld))
        nil
      (msg "The custom rewrite rule ~x0 must have ~
            the same function variables as the function's matrix ~x1.~%"
           rule-body fun-matrix))))

(define print-funvar-dependency ((fun symbolp)
                                 (kind sofun-kindp)
                                 (wrld plist-worldp))
  :returns (nothing "Always @(tsee null).")
  :mode :program
  :short "Print the function variables that a funcion depends on."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a second-order function, or an instance thereof, is introduced,
     the submitted event form first introduces the function,
     and then prints the function variables that the function depends on.
     The following code performs that printing.")
   (xdoc::p
    "This function returns nothing.
     It is only used for side effects, namely printing.")
   (xdoc::p
    "The @('kind') argument is the kind of @('fun') if second-order,
     otherwise it is the kind of the second-order function
     of which @('fun') is an instance."))
  (let ((funvars (case kind
                   (plain (funvars-of-plain-fn fun wrld))
                   (choice (funvars-of-choice-fn fun wrld))
                   (quant (funvars-of-quantifier-fn fun wrld)))))
    (if funvars
        (cw "The function ~x0 depends on the function variables ~x1.~%"
            fun (remove-duplicates-eq funvars))
      (cw "The function ~x0 depends on no function variables.~%" fun))))

(defsection defun2-implementation
  :short "Implementation of @(tsee defun2)."
  :long
  "@(def defun2)
   @(def acl2::defun2)"

  (defmacro defun2 (sofun &rest rest)
    `(progn
       (defun ,sofun ,@rest)
       (defsoft ,sofun)))

  (defmacro acl2::defun2 (&rest args)
    `(defun2 ,@args)))

(defsection defchoose2-implementation
  :short "Implementation of @(tsee defchoose2)."
  :long
  "@(def defchoose2)
   @(def acl2::defchoose2)"

  (defmacro defchoose2 (sofun &rest rest)
    `(progn
       (defchoose ,sofun ,@rest)
       (defsoft ,sofun)))

  (defmacro acl2::defchoose2 (&rest args)
    `(defchoose2 ,@args)))

(define defun-sk2-fn (sofun
                      params
                      body
                      options
                      (ctx "Context for errors.")
                      state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event "A @(tsee maybe-pseudo-event-formp).")
               state)
  :mode :program
  :short "Validate some of the inputs to @(tsee defun-sk2)
          and generate the event form to submit."
  :long
  (xdoc::topstring-p
   "We directly check the name
    and @(':print') option (if present),
    but rely on @(tsee defun-sk) to check the rest of the form.
    After submitting the @(tsee defun-sk) form,
    we check that the body and the rewrite rule
    depend on the same function variables.")
  (b* (((unless (symbolp sofun))
        (er-soft+ ctx t nil
                  "The first input must be a symbol, but ~x0 is not."
                  sofun))
       ((unless (keyword-value-listp options))
        (er-soft+ ctx t nil
                  "The inputs after the third input ~
                   must be a keyword-value list, ~
                   but ~x0 is not."
                  options))
       (print-pair (assoc-keyword :print options))
       (print (if print-pair
                  (cadr print-pair)
                :fn-output))
       ((unless (member-eq print '(nil :all :fn-output)))
        (er-soft+ ctx t nil
                  "The :PRINT input must be NIL, :ALL, or :FN-OUTPUT, ~
                   but ~x0 is not."
                  print))
       (options (remove-keyword :print options))
       (defun-sk-event `(defun-sk ,sofun ,params ,body ,@options))
       (table-event `(table second-order-functions
                       ',sofun (funvars-of-quantifier-fn ',sofun world)))
       (check-event `(make-event-terse
                      (b* ((err-msg? (check-qrewrite-rule-funvars ',sofun
                                                                  (w state))))
                        (if err-msg?
                            (er-soft+ ',ctx t nil "~@0" err-msg?)
                          (value '(value-triple :invisible))))))
       (print-funvar-event `(value-triple
                             (print-funvar-dependency
                              ',sofun 'plain (w state))))
       (return-value-event `(value-triple ',sofun))
       (event (cond ((eq print nil)
                     `(progn
                        ,defun-sk-event
                        ,table-event
                        ,check-event
                        ,print-funvar-event
                        ,return-value-event))
                    ((eq print :all)
                     (restore-output
                      `(progn
                         ,defun-sk-event
                         ,table-event
                         ,check-event
                         ,print-funvar-event
                         ,return-value-event)))
                    ((eq print :fn-output)
                     `(progn
                        ,(restore-output defun-sk-event)
                        ,table-event
                        ,check-event
                        ,print-funvar-event
                        ,return-value-event))
                    (t (impossible)))))
    (value event)))

(defsection defun-sk2-implementation
  :short "Implementation of @(tsee defun-sk2)."
  :long
  "@(def defun-sk2)
   @(def acl2::defun-sk2)"

  (defmacro defun-sk2 (sofun params body &rest options)
    `(make-event-terse (defun-sk2-fn
                         ',sofun
                         ',params
                         ',body
                         ',options
                         (cons 'defun-sk2 ',sofun)
                         state)))

  (defmacro acl2::defun-sk2 (&rest args)
    `(defun-sk2 ,@args)))

(defsection show-defun-sk2
  :short "Show the event form generated by @(tsee defun-sk2),
          without submitting them."
  :long
  "@(def show-defun-sk2)
   @(def acl2::show-defun-sk2)"

  (defmacro show-defun-sk2 (sofun params body &rest options)
    `(defun-sk2-fn
       ',sofun
       ',params
       ',body
       ',options
       (cons 'defun-sk2 ',sofun)
       state))

  (defmacro acl2::show-defun-sk2 (&rest args)
    `(show-defun-sk2 ,@args)))

(define sothmp ((sothm symbolp) (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "Recognize second-order theorems."
  :long
  (xdoc::topstring-p
   "A theorem is second-order iff
    it depends on one or more function variables.")
  (not (null (funvars-of-thm sothm wrld))))

(define no-trivial-pairsp ((alist alistp))
  :returns (yes/no booleanp)
  :short "Check if an alist has no pairs with equal key and value."
  :long
  (xdoc::topstring-p
   "This is a constraint satisfied by function substitutions;
    see @(tsee fun-substp).
    A pair that substitutes a function with itself would have no effect,
    so such pairs are useless.")
  (if (endp alist)
      t
    (let ((pair (car alist)))
      (and (not (equal (car pair) (cdr pair)))
           (no-trivial-pairsp (cdr alist))))))

(define fun-substp (fsbs)
  :returns (yes/no booleanp)
  :short "Recognize function substitutions."
  :long
  (xdoc::topstring-p
   "A function substitution is an alist from function names to function names,
    with unique keys and with no trivial pairs.")
  (and (symbol-symbol-alistp fsbs)
       (no-duplicatesp (alist-keys fsbs))
       (no-trivial-pairsp fsbs))
  :guard-hints (("Goal" :in-theory (enable symbol-symbol-alistp))))

(define funvar-instp (inst (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize instantiations."
  :long
  (xdoc::topstring-p
   "These are non-empty function substitutions
    whose keys are function variables and whose values are function names.")
  (and (fun-substp inst)
       (consp inst)
       (funvar-listp (alist-keys inst) wrld)
       (function-symbol-listp (alist-vals inst) wrld)))

(define funvar-inst-listp (insts (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize true lists of instantiations."
  (if (atom insts)
      (null insts)
    (and (funvar-instp (car insts) wrld)
         (funvar-inst-listp (cdr insts) wrld))))

(define sof-instancesp (instmap (wrld plist-worldp))
  :returns (yes/no booleanp)
  :verify-guards nil
  :short "Recognize the information about the instances
          that is associated to second-order function names
          in the @(tsee sof-instances) table."
  :long
  (xdoc::topstring-p
   "This is an alist from instantiations to function names.
    Each pair in the alist maps an instantiation
    to the corresponding instance.")
  (and (alistp instmap)
       (funvar-inst-listp (alist-keys instmap) wrld)
       (symbol-listp (alist-vals instmap))))

(define get-sof-instance ((inst (funvar-instp inst wrld))
                          (instmap (sof-instancesp instmap wrld))
                          (wrld plist-worldp))
  :returns (instance symbolp
                     :hyp (sof-instancesp instmap wrld)
                     :hints (("Goal" :in-theory (enable sof-instancesp))))
  :verify-guards nil
  :short "Retrieve the instance associated to a given instantiation,
          in the map of known instances of a second-order function."
  :long
  (xdoc::topstring-p
   "Instantiations are treated as equivalent according to @(tsee alist-equiv).
    If no instance for the instantiation is found, @('nil') is returned.")
  (if (endp instmap)
      nil
    (let ((pair (car instmap)))
      (if (alist-equiv (car pair) inst)
          (cdr pair)
        (get-sof-instance inst (cdr instmap) wrld)))))

(define put-sof-instance ((inst (funvar-instp inst wrld))
                          (fun symbolp)
                          (instmap (and (sof-instancesp instmap wrld)
                                        (null
                                         (get-sof-instance inst instmap wrld))))
                          (wrld plist-worldp))
  :returns (new-instmap "A @(tsee sof-instancesp).")
  :verify-guards nil
  :short "Associates an instantiation with an instance
          in an existing map of know instances of a second-order function."
  :long
  (xdoc::topstring-p
   "The guard requires the absence of an instance for the same instantiation
    (equivalent up to @(tsee alist-equiv)).")
  (declare (ignore wrld)) ; only used in guard
  (acons inst fun instmap))

(defsection sof-instances-table
  :short "Table of instances of second-order functions."
  :long
  (xdoc::topstring-p
   "The known instances of second-order functions are stored in a @(see table).
    The keys are the names of second-order functions that have instances,
    and the values are alists from instantiations to instances.")

  (table sof-instances nil nil :guard (and (symbolp acl2::key)
                                           (sof-instancesp acl2::val world))))

(define sof-instances ((sofun (sofunp sofun wrld)) (wrld plist-worldp))
  :returns (instmap "A @(tsee sof-instancesp).")
  :verify-guards nil
  :short "Known instances of a second-order function."
  (let ((table (table-alist 'sof-instances wrld)))
    (cdr (assoc-eq sofun table))))

(define fun-subst-function ((fsbs fun-substp) (fun symbolp) (wrld plist-worldp))
  :returns (new-fun "A @(tsee symbolp).")
  :verify-guards nil
  :short "Apply a function substitution to an individual function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Applying an instantiation to a term involves replacing
     not only the function variables that are keys of the instantiation
     and that occur explicitly in the term,
     but also the ones that occur implicitly in the term
     via occurrences of second-order functions that depend on
     those function variables.
     For example, if @('ff') is a second-order function
     with function parameter @('f'),
     and an instantiation @('I') replaces @('f') with @('g'),
     applying @('I') to the term @('(cons (f x) (ff y))')
     should yield the term @('(cons (g x) (gg y))'),
     where @('gg') is the instance that results form applying @('I') to @('ff').
     The @(tsee sof-instances) table is used to find @('gg'):
     @('I') is restricted to the function parameters of @('ff')
     before searching the map of instances of @('ff');
     if the restriction is empty, @('gg') is @('ff'),
     i.e. no replacement takes place.
     If @('gg') does not exist,
     the application of @('I') to @('(cons (f x) (ff y))') fails;
     the user must create @('gg')
     and try applying @('I') to @('(cons (f x) (ff y))') again.")
   (xdoc::p
    "When an instantiation is applied
     to the body of a recursive second-order function @('sofun')
     to obtain an instance @('fun'),
     occurrences of @('sofun') in the body must be replaced with @('fun'),
     but at that time @('fun') does not exist yet,
     and thus the table of second-order function instances of @('sofun')
     has no entries for @('fun') yet.
     Thus, it is convenient to use function substitutions
     (not just instantiations)
     to instantiate terms.")
   (xdoc::p
    "The following code applies a function substitution to an individual function,
     in the manner explained above.
     It is used by @(tsee fun-subst-term),
     which applies a function substitution to a term.
     If a needed second-order function instance does not exist,
     an error occurs."))
  (let ((pair (assoc-eq fun fsbs)))
    (if pair
        (cdr pair)
      (if (sofunp fun wrld)
          (let* ((funvars (sofun-funvars fun wrld))
                 (subfsbs (restrict-alist funvars fsbs)))
            (if (null subfsbs)
                fun
              (let* ((instmap (sof-instances fun wrld))
                     (new-fun (get-sof-instance subfsbs instmap wrld)))
                (if new-fun
                    new-fun
                  (raise "~x0 has no instance for ~x1." fun fsbs)))))
        fun))))

(defines fun-subst-term/terms
  :verify-guards nil
  :short "Apply function substitutions to terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the discussion in @(tsee fun-subst-function).")
   (xdoc::@def "fun-subst-term")
   (xdoc::@def "fun-subst-terms"))

  (define fun-subst-term
    ((fsbs fun-substp) (term pseudo-termp) (wrld plist-worldp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (if (or (variablep term)
            (quotep term))
        term
      (let* ((fn (fn-symb term))
             (new-fn (if (symbolp fn)
                         (fun-subst-function fsbs fn wrld)
                       (make-lambda (lambda-formals fn)
                                    (fun-subst-term fsbs
                                                    (lambda-body fn)
                                                    wrld))))
             (new-args (fun-subst-terms fsbs (fargs term) wrld)))
        (cons new-fn new-args))))

  (define fun-subst-terms
    ((fsbs fun-substp) (terms pseudo-term-listp) (wrld plist-worldp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (if (endp terms)
        nil
      (cons (fun-subst-term fsbs (car terms) wrld)
            (fun-subst-terms fsbs (cdr terms) wrld)))))

(defines ext-fun-subst-term/terms/function
  :mode :program
  :short "Extend function substitutions for functional instantiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "An instance @('thm') of a second-order theorem @('sothm')
     is also a theorem,
     provable using a @(':functional-instance') of @('sothm').
     The pairs of the @(':functional-instance') are
     not only the pairs of the instantiation
     that creates @('thm') from @('sothm'),
     but also all the pairs
     whose first components are
     second-order functions that @('sothm') depends on
     and whose second components are the corresponding instances.")
   (xdoc::p
    "For example,
     if @('sothm') is @('(p (sofun x))'),
     @('sofun') is a second-order function,
     @('p') is a first-order predicate,
     and applying an instantiation @('I') to @('(p (sofun x))')
     yields @('(p (fun x))'),
     then @('thm') is proved using
     @('(:functional-instance sothm (... (sofun fun) ...))'),
     where the first @('...') are the pairs of @('I')
     and the second @('...') are further pairs
     of second-order functions and their instances,
     e.g. if @('sofun') calls a second-order function @('sofun1'),
     the pair @('(sofun1 fun1)') must be in the second @('...'),
     where @('fun1') is the instance of @('sofun1') corresponding to @('I').
     All these pairs are needed to properly instantiate
     the constraints that arise from the @(':functional-instance'),
     which involve the second-order functions that @('sothm') depends on,
     directly or indirectly.")
   (xdoc::p
    "The following code extends a function substitution
     (initially an instantiation)
     to contain all those extra pairs.
     The starting point is a term;
     the bodies of second-order functions referenced in the term
     are recursively processed.
     The table of instances of second-order functions is searched,
     similarly to @(tsee fun-subst-function).")
   (xdoc::@def "ext-fun-subst-term")
   (xdoc::@def "ext-fun-subst-terms")
   (xdoc::@def "ext-fun-subst-function"))

  (define ext-fun-subst-term
    ((term pseudo-termp) (fsbs fun-substp) (wrld plist-worldp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (if (or (variablep term)
            (quotep term))
        fsbs
      (let* ((fn (fn-symb term))
             (fsbs (if (symbolp fn)
                       (ext-fun-subst-function fn fsbs wrld)
                     (ext-fun-subst-term (lambda-body fn) fsbs wrld))))
        (ext-fun-subst-terms (fargs term) fsbs wrld))))

  (define ext-fun-subst-terms
    ((terms pseudo-term-listp) (fsbs fun-substp) (wrld plist-worldp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (if (endp terms)
        fsbs
      (let ((fsbs (ext-fun-subst-term (car terms) fsbs wrld)))
        (ext-fun-subst-terms (cdr terms) fsbs wrld))))

  (define ext-fun-subst-function
    ((fun symbolp) (fsbs fun-substp) (wrld plist-worldp))
    :returns (new-fun "A @(tsee symbolp).")
    (cond
     ((assoc fun fsbs) fsbs)
     ((sofunp fun wrld)
      (b* ((funvars (sofun-funvars fun wrld))
           (subfsbs (restrict-alist funvars fsbs))
           ((if (null subfsbs)) fsbs)
           (instmap (sof-instances fun wrld))
           (funinst (get-sof-instance subfsbs instmap wrld))
           ((unless funinst)
            (raise "~x0 has no instance for ~x1." fun fsbs))
           (fsbs (acons fun funinst fsbs)))
        (case (sofun-kind fun wrld)
          ((plain quant) (ext-fun-subst-term (ubody fun wrld) fsbs wrld))
          (choice (ext-fun-subst-term (defchoose-body fun wrld) fsbs wrld)))))
     (t fsbs))))

(define sothm-inst-pairs ((fsbs fun-substp) (wrld plist-worldp))
  :returns (pairs "A @('doublet-listp').")
  :mode :program
  :short "Create a list of doublets for functional instantiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "From a function substitution obtained by extending an instantiation
     via @(tsee ext-fun-subst-term/terms/function),
     the list of pairs to supply to @(':functional-instance') is obtained.
     Each dotted pair is turned into a doublet
     (a different representation of the pair).")
   (xdoc::p
    "In addition, when a dotted pair is encountered
     whose @(tsee car) is the name of a quantifier second-order function,
     an extra pair for instantiating the associated witness is inserted.
     The witnesses of quantifier second-order functions
     must also be part of the @(':functional-instance'),
     because they are referenced by the quantifier second-order functions.
     However, these witnesses are not recorded as second-order functions
     in the table of second-order functions,
     and thus the code of @(tsee ext-fun-subst-term/terms/function)
     does not catch these witnesses."))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (if (quant-sofunp 1st wrld)
          (let ((1st-wit (defun-sk-witness 1st wrld))
                (2nd-wit (defun-sk-witness 2nd wrld)))
            (cons (list 1st 2nd)
                  (cons (list 1st-wit 2nd-wit)
                        (sothm-inst-pairs (cdr fsbs) wrld))))
        (cons (list 1st 2nd)
              (sothm-inst-pairs (cdr fsbs) wrld))))))

(define sothm-inst-facts ((fsbs fun-substp) (wrld plist-worldp))
  :returns (fact-names "A @(tsee symbol-listp).")
  :mode :program
  :short "Create list of facts for functional instantiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a @(':functional-instance') is used in a proof,
     proof subgoals are created to ensure that the replacing functions
     satisfy all the constraints of the replaced functions.
     In a @(':functional-instance') with a function substitution @('S')
     as calculated by @(tsee ext-fun-subst-term/terms/function),
     each function variable (which comes from the instantiation)
     has no constraints and so no subgoals are generated for them.
     Each second-order function @('sofun') in @('S')
     has the following constraints:")
   (xdoc::ul
    (xdoc::li
     "If @('sofun') is a plain second-order function,
      the constraint is that
      the application of @('S') to the definition of @('sofun') is a theorem,
      which follows by the construction of the instance @('fun') of @('sofun'),
      i.e. it follows from the definition of @('fun').")
    (xdoc::li
     "If @('sofun') is a choice second-order function,
      the constraint is that
      the application of @('S') to the choice axiom of @('sofun') is a theorem,
      which follows by the construction of the instance @('fun') of @('sofun'),
      i.e. it follows from the choice axiom of @('fun').")
    (xdoc::li
     "If @('sofun') is a quantifier second-order function,
      the constraints are that
      (1) the application of @('S')
      to the rewrite rule generated by the @(tsee defun-sk) of @('sofun'),
      and (2) the application of @('S') to the definition of @('sofun')
      (or to the defining theorem of @('sofun')
      if @('sofun') was introduced with @(':constrain t')),
      are both theorems,
      which both follow by the construction
      of the instance @('fun') of @('sofun'),
      i.e. they follow from
      (1) the rewrite rule generated by the @(tsee defun-sk) of @('fun')
      and (2) the definition of @('fun')
      (or the defining theorem of @('fun')
      if @('fun') was introduced with @(':constrain nil'))."))
   (xdoc::p
    "The list of facts needed to prove these constraints is determined
     by the function substitution @('S').
     For each pair @('(fun1 . fun2)') of the function substitution:")
   (xdoc::ul
    (xdoc::li
     "If @('fun1') is a plain second-order function,
      the fact used in the proof is the definition of @('fun2'),
      whose name is the name of @('fun2').
      (Note that by construction, since @('fun2') is an instance of @('fun1'),
      @('fun2') is introduced by a @(tsee defun).)")
    (xdoc::li
     "If @('fun1') is a choice second-order function,
      the fact used in the proof is the @(tsee defchoose) axiom of @('fun2'),
      whose name is the name of @('fun2').
      (Note that by construction, since @('fun2') is an instance of @('fun1'),
      @('fun2') is introduced by a @(tsee defchoose).)")
    (xdoc::li
     "If @('fun1') is a quantifier second-order function,
      the facts used in the proof are
      (1) the @(tsee defun-sk) rewrite rule of @('fun2')
      and (2)
      either (i) the definition of @('fun2')
      (if @('fun2') was introduced with @(':constrain nil')),
      whose name is the name of @('fun2'),
      or (ii) the defining theorem of @('fun2')
      (if @('fun2') was introduced with @(':constrain t')),
      whose name is @('fun2') followed by @('-definition').
      (Note that by construction, since @('fun2') is an instance of @('fun1'),
      @('fun2') is introduced by a @(tsee defun-sk).)")
    (xdoc::li
     "Otherwise, @('fun1') is a function variable, which has no constraints,
      so no fact is used in the proof.")))
  (if (endp fsbs)
      nil
    (let* ((pair (car fsbs))
           (1st (car pair))
           (2nd (cdr pair)))
      (cond ((or (plain-sofunp 1st wrld)
                 (choice-sofunp 1st wrld))
             (cons 2nd (sothm-inst-facts (cdr fsbs) wrld)))
            ((quant-sofunp 1st wrld)
             `(,(defun-sk-rewrite-name 2nd wrld)
               ,(if (definedp 2nd wrld)
                    2nd
                  (defun-sk-definition-name 2nd wrld))
               ,@(sothm-inst-facts (cdr fsbs) wrld)))
            (t (sothm-inst-facts (cdr fsbs) wrld))))))

(define sothm-inst-proof
  ((sothm symbolp) (fsbs fun-substp) (wrld plist-worldp))
  :returns (instructions "A @(tsee true-listp).")
  :mode :program
  :short "Proof builder instructions to prove
          instances of second-order theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "Instances of second-order theorems are proved using the ACL2 proof builder.
     Each such instance is proved by
     first using the @(':functional-instance')
     determined by @(tsee sothm-inst-pairs),
     then using the facts computed by @(tsee sothm-inst-facts) on the subgoals.
     Each sugoal only needs a subset of those facts,
     but for simplicity all the facts are used for each subgoal,
     using the proof builder
     <see topic='@(url acl2-pc::repeat)'>@(':repeat')</see> command.
     Since sometimes the facts are not quite identical to the subgoals,
     the proof builder
     <see topic='@(url acl2-pc::prove)'>@(':prove')</see> command
     is used to iron out any such differences."))
  `(:instructions
    ((:use (:functional-instance ,sothm ,@(sothm-inst-pairs fsbs wrld)))
     (:repeat (:then (:use ,@(sothm-inst-facts fsbs wrld)) :prove)))))

(define check-sothm-inst (sothm-inst (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "Recognize designations of instances of second-order theorems."
  :long
  (xdoc::topstring-p
   "A designation of an instance of a second-order theorem has the form
    @('(sothm (f1 . g1) ... (fM . gM))'),
    where @('sothm') is a second-order theorem
    and @('((f1 . g1) ... (fM . gM))') is an instantiation.
    These designations are used in @(tsee defthm-inst).")
  (and (true-listp sothm-inst)
       (>= (len sothm-inst) 2)
       (sothmp (car sothm-inst) wrld)
       (funvar-instp (cdr sothm-inst) wrld)))

(define defthm-inst-fn (thm
                        sothm-inst
                        options
                        (ctx "Context for errors.")
                        state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event "A @(tsee maybe-pseudo-event-formp).")
               state)
  :mode :program
  :short "Validate some of the inputs to @(tsee defthm-inst)
          and generate the event form to submit."
  :long
  (xdoc::topstring-p
   "We directly check all the inputs except for the @(':rule-classes') option,
    relying on @(tsee defthm) to check it.")
  (b* ((wrld (w state))
       ((unless (symbolp thm))
        (er-soft+ ctx t nil
                  "The first input must be a symbol, but ~x0 is not."
                  thm))
       ((unless (check-sothm-inst sothm-inst wrld))
        (er-soft+ ctx t nil
                  "The second input must be ~
                   the name of a second-order theorem ~
                   followed by the pairs of an instantiation, ~
                   but ~x0 is not."
                  sothm-inst))
       (sothm (car sothm-inst))
       (inst (cdr sothm-inst))
       ((unless (subsetp (alist-keys inst) (funvars-of-thm sothm wrld)))
        (er-soft+ ctx t nil
                  "Each function variable key of ~x0 must be ~
                   among function variable that ~x1 depends on."
                  inst sothm))
       ((unless (keyword-value-listp options))
        (er-soft+ ctx t nil
                  "The inputs after the second input ~
                   must be a keyword-value list, ~
                   but ~x0 is not."
                  options))
       (keywords (evens options))
       ((unless (no-duplicatesp keywords))
        (er-soft+ ctx t nil
                  "The inputs keywords must be unique."))
       ((unless (subsetp keywords '(:rule-classes :print)))
        (er-soft+ ctx t nil
                  "Only the input keywords ~
                   :RULE-CLASSES and :PRINT are allowed."))
       (print-pair (assoc-keyword :print options))
       (print (if print-pair
                  (cadr print-pair)
                :result))
       ((unless (member-eq print '(nil :all :result)))
        (er-soft+ ctx t nil
                  "The :PRINT input must be NIL, :ALL, or :RESULT, ~
                   but ~x0 is not."
                  print))
       (options (remove-keyword :print options))
       (sothm-formula (formula sothm nil wrld))
       (thm-formula (fun-subst-term inst sothm-formula wrld))
       (thm-formula (untranslate thm-formula t wrld))
       (fsbs (ext-fun-subst-term sothm-formula inst wrld))
       (thm-proof (sothm-inst-proof sothm fsbs wrld))
       (defthm-event `(defthm ,thm ,thm-formula ,@thm-proof ,@options))
       (defthm-event-without-proof `(defthm ,thm ,thm-formula ,@options))
       (return-value-event `(value-triple ',thm))
       (event (cond ((eq print nil)
                     `(progn
                        ,defthm-event
                        ,return-value-event))
                    ((eq print :all)
                     (restore-output
                      `(progn
                         ,defthm-event
                         ,return-value-event)))
                    ((eq print :result)
                     `(progn
                        ,defthm-event
                        (cw-event "~x0~|" ',defthm-event-without-proof)
                        ,return-value-event))
                    (t (impossible)))))
    (value event)))

(defsection defthm-inst-implementation
  :short "Implementation of @(tsee defthm-inst)."
  :long
  "@(def defthm-inst)
   @(def acl2::defthm-inst)"

  (defmacro defthm-inst (thm sothminst &rest options)
    `(make-event-terse (defthm-inst-fn
                         ',thm
                         ',sothminst
                         ',options
                         (cons 'defthm-inst ',thm)
                         state)))

  (defmacro acl2::defthm-inst (&rest args)
    `(defthm-inst ,@args)))

(defsection show-defthm-inst
  :short "Show the event form generated by @(tsee defthm-inst),
          without submitting them."
  :long
  "@(def show-defthm-inst)
   @(def acl2::show-defthm-inst)"

  (defmacro show-defthm-inst (thm sothminst &rest options)
    `(defthm-inst-fn
       ',thm
       ',sothminst
       ',options
       (cons 'defthm-inst ',thm)
       state))

  (defmacro acl2::show-defthm-inst (&rest args)
    `(show-defthm-inst ,@args)))

(define check-sofun-inst (sofun-inst (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :verify-guards nil
  :short "Recognize designations of instances of second-order functions."
  :long
  (xdoc::topstring-p
   "A designation of an instance of a second-order function has the form
    @('(sofun (f1 . g1) ... (fM . gM))'),
    where @('sofun') is a second-order function
    and @('((f1 . g1) ... (fM . gM))') is an instantiation.
    These designations are used in @(tsee defun-inst).")
  (and (true-listp sofun-inst)
       (>= (len sofun-inst) 2)
       (sofunp (car sofun-inst) wrld)
       (funvar-instp (cdr sofun-inst) wrld)))

(define defun-inst-plain-events ((fun symbolp)
                                 (sofun (plain-sofunp sofun (w state)))
                                 inst
                                 (options keyword-value-listp)
                                 (ctx "Context for errors.")
                                 state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (events+result+funvars
                "A tuple @('(events result funvars)') where
                 @('events') is a @(tsee pseudo-event-form-listp),
                 @('result') is a @(tsee maybe-pseudo-event-formp),
                 and @('funvars') is a @(tsee funvar-listp).")
               state)
  :mode :program
  :short "Generate a list of events to submit,
          when instantiating a plain second-order function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the @(tsee defun2) or @(tsee defun) event form,
     without the termination hints.
     This is printed when @(':print') is @(':result').")
   (xdoc::p
    "Also return the function variables that the new function depends on.")
   (xdoc::p
    "Only the @(':verify-guards') and @(':print') options may be present.")
   (xdoc::p
    "We add @('fun') to the table of second-order functions
     iff it is second-order.")
   (xdoc::p
    "If @('sofun') (and consequently @('fun')) is recursive,
     we extend the instantiation with @('(sofun . fun)'),
     to ensure that the recursive calls are properly transformed."))
  (b* ((wrld (w state))
       ((unless (subsetp (evens options)
                         '(:verify-guards :print)))
        (er-soft+ ctx t nil
                  "Only the input keywords ~
                   :VERIFY-GUARDS and :PRINT are allowed, ~
                   because ~x0 is a plain second-order function."
                  sofun))
       (verify-guards (let ((verify-guards-option
                             (assoc-keyword :verify-guards options)))
                        (if verify-guards-option
                            (cadr verify-guards-option)
                          (guard-verified-p sofun wrld))))
       (sofun-body (ubody sofun wrld))
       (sofun-measure (if (recursivep sofun nil wrld)
                          (measure sofun wrld)
                        nil))
       (sofun-guard (uguard sofun wrld))
       (fsbs (if sofun-measure (acons sofun fun inst) inst))
       (fun-body (fun-subst-term fsbs sofun-body wrld))
       (fun-body-funvars (funvars-of-term fun-body wrld))
       (fun-body (untranslate fun-body nil wrld))
       (fun-measure (fun-subst-term inst sofun-measure wrld))
       (fun-measure-funvars (funvars-of-term fun-measure wrld))
       (fun-measure (untranslate fun-measure nil wrld))
       (fun-guard (fun-subst-term inst sofun-guard wrld))
       (fun-guard-funvars (funvars-of-term fun-guard wrld))
       (fun-guard (untranslate fun-guard t wrld))
       (sofun-tt-name `(:termination-theorem ,sofun))
       (sofun-tt-formula (and (recursivep sofun nil wrld)
                              (termination-theorem sofun wrld)))
       (fsbs (ext-fun-subst-term sofun-tt-formula inst wrld))
       (fun-tt-proof (sothm-inst-proof sofun-tt-name fsbs wrld))
       (hints (if fun-measure `(:hints (("Goal" ,@fun-tt-proof))) nil))
       (measure (if fun-measure `(:measure ,fun-measure) nil))
       (formals (formals sofun wrld))
       (funvars (remove-duplicates (append fun-body-funvars
                                           fun-measure-funvars
                                           fun-guard-funvars)))
       (defun-event `(defun ,fun ,formals
                       (declare (xargs :guard ,fun-guard
                                       :verify-guards ,verify-guards
                                  ,@measure
                                  ,@hints))
                       ,fun-body))
       (result `(,(if funvars 'defun2 'defun)
                 ,fun
                 ,formals
                 (declare (xargs :guard ,fun-guard
                                 :verify-guards ,verify-guards
                            ,@measure))
                 ,fun-body))
       (table-event?
        (if funvars
            `((table second-order-functions ',fun ',funvars))
          nil)))
    (value (list `(,defun-event ,@table-event?)
                 result
                 funvars))))

(define defun-inst-choice-events ((fun symbolp)
                                  (sofun (choice-sofunp sofun (w state)))
                                  inst
                                  (options keyword-value-listp)
                                  (ctx "Context for errors.")
                                  state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (events+result+funvars
                "A tuple @('(events result funvars)') where
                 @('events') is a @(tsee pseudo-event-form-listp),
                 @('result') is a @(tsee maybe-pseudo-event-formp),
                 and @('funvars') is a @(tsee funvar-listp).")
               state)
  :mode :program
  :short "Generate a list of events to submit,
          when instantiating a choice second-order function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the @(tsee defchoose2) or @(tsee defchoose) event form.
     This is printed when @(':print') is @(':result').")
   (xdoc::p
    "Also return the function variables that the new function depends on.")
   (xdoc::p
    "Only the @(':print') option may be present.")
   (xdoc::p
    "We add @('fun') to the table of second-order functions
     iff it is second-order."))
  (b* ((wrld (w state))
       ((unless (subsetp (evens options)
                         '(:print)))
        (er-soft+ ctx t nil
                  "Only the input keyword :PRINT is allowed, ~
                   because ~x0 is a choice second-order function."
                  sofun))
       (bound-vars (defchoose-bound-vars sofun wrld))
       (sofun-body (defchoose-body sofun wrld))
       (fun-body (fun-subst-term inst sofun-body wrld))
       (funvars (funvars-of-term fun-body wrld))
       (fun-body (untranslate fun-body nil wrld))
       (formals (formals sofun wrld))
       (strengthen (defchoose-strengthen sofun wrld))
       (funvars (remove-duplicates funvars))
       (defchoose-event `(defchoose ,fun ,bound-vars ,formals
                           ,fun-body
                           :strengthen ,strengthen))
       (result `(,(if funvars 'defchoose2 'defchoose)
                 ,fun
                 ,bound-vars
                 ,formals
                 ,fun-body
                 :strengthen ,strengthen))
       (table-event?
        (if funvars
            `((table second-order-functions ',fun ',funvars))
          nil)))
    (value (list `(,defchoose-event ,@table-event?)
                 result
                 funvars))))

(define defun-inst-quant-events ((fun symbolp)
                                 (sofun (quant-sofunp sofun (w state)))
                                 inst
                                 (options keyword-value-listp)
                                 (ctx "Context for errors.")
                                 state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (events+result+funvars
                "A tuple @('(events result funvars)') where
                 @('events') is a @(tsee pseudo-event-form-listp),
                 @('result') is a @(tsee maybe-pseudo-event-formp),
                 and @('funvars') is a @(tsee funvar-listp).")
               state)
  :mode :program
  :short "Generate a list of events to submit,
          when instantiating a quantifier second-order function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return the @(tsee defun-sk2) or @(tsee defun-sk) event form.
     This is printed when @(':print') is @(':result').")
   (xdoc::p
    "Also return the function variables that the new function depends on.")
   (xdoc::p
    "Only the
     @(':skolem-name'),
     @(':thm-name'),
     @(':rewrite'),
     @(':constrain'), and
     @(':print')
     options may be present.")
   (xdoc::p
    "We add @('fun') to the table of second-order functions
     iff it is second-order."))
  (b* ((wrld (w state))
       ((unless (subsetp (evens options)
                         '(:skolem-name :thm-name :rewrite :constrain :print)))
        (er-soft+ ctx t nil
                  "Only the input keywords ~
                   :SKOLEM-NAME, :THM-NAME, :REWRITE, :CONSTRAIN and :PRINT ~
                   are allowed, ~
                   because ~x0 is a quantifier second-order function."
                  sofun))
       (bound-vars (defun-sk-bound-vars sofun wrld))
       (quant (defun-sk-quantifier sofun wrld))
       (sofun-matrix (defun-sk-matrix sofun wrld))
       (fun-matrix (fun-subst-term inst sofun-matrix wrld))
       (fun-matrix-funvars (funvars-of-term fun-matrix wrld))
       (fun-matrix (untranslate fun-matrix nil wrld))
       (rewrite-option (assoc-keyword :rewrite options))
       (rewrite
        (if rewrite-option
            (cadr rewrite-option)
          (let ((qrkind (defun-sk-rewrite-kind sofun wrld)))
            (case qrkind
              (:default :default)
              (:direct :direct)
              (:custom
               (let* ((fsbs (acons sofun fun inst))
                      (rule-name (defun-sk-rewrite-name sofun wrld))
                      (term (formula rule-name nil wrld)))
                 (fun-subst-term fsbs term wrld)))))))
       (skolem-name (let ((skolem-name-option
                           (assoc-keyword :skolem-name options)))
                      (if skolem-name-option
                          `(:skolem-name ,(cadr skolem-name-option))
                        nil)))
       (thm-name (let ((thm-name-option
                        (assoc-keyword :thm-name options)))
                   (if thm-name-option
                       `(:thm-name ,(cadr thm-name-option))
                     nil)))
       (constrain (let ((constrain-option
                         (assoc-keyword :constrain options)))
                    (if constrain-option
                        `(:constrain ,(cadr constrain-option))
                      nil)))
       (sofun-guard (uguard sofun wrld))
       (fun-guard (fun-subst-term inst sofun-guard wrld))
       (fun-guard-funvars (funvars-of-term fun-guard wrld))
       (fun-guard (untranslate fun-guard t wrld))
       (wit-dcl `(declare (xargs :guard ,fun-guard :verify-guards nil)))
       (formals (formals sofun wrld))
       (strengthen (defun-sk-strengthen sofun wrld))
       (body (list quant bound-vars fun-matrix))
       (rest `(:strengthen ,strengthen
               :quant-ok t
               ,@(and (eq quant 'forall)
                      (list :rewrite rewrite))
               ,@skolem-name
               ,@thm-name
               ,@constrain
               :witness-dcls (,wit-dcl)))
       (funvars (remove-duplicates (append fun-matrix-funvars
                                           fun-guard-funvars)))
       (defun-sk-event `(defun-sk ,fun ,formals
                          ,body
                          ,@rest))
       (result `(,(if funvars 'defun-sk2 'defun-sk)
                 ,fun
                 ,formals
                 ,body
                 ,@rest))
       (table-event?
        (if funvars
            `((table second-order-functions ',fun ',funvars))
          nil))
       (check-event `(make-event-terse
                      (b* ((err-msg?
                            (check-qrewrite-rule-funvars ',sofun (w state))))
                        (if err-msg?
                            (er-soft+
                             (cons 'defun-inst ',fun) t nil "~@0" err-msg?)
                          (value '(value-triple :invisible)))))))
    (value (list `(,defun-sk-event ,@table-event? ,check-event)
                 result
                 funvars))))

(define defun-inst-fn (fun
                       sofun-inst
                       options
                       (ctx "Context for errors.")
                       state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event "A @(tsee maybe-pseudo-event-formp).")
               state)
  :mode :program
  :short "Validate some of the inputs to @(tsee defun-inst)
          and generate the event form to submit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We directly check the name and instance designation,
     we directly check the correct presence of keyed options
     (we do that in
     @(tsee defun-inst-plain-events),
     @(tsee defun-inst-choice-events), and
     @(tsee defun-inst-quant-events)), and
     we directly check the correct value of the @(':print') option (if present),
     but rely on @(tsee defun), @(tsee defchoose), and @(tsee defun-sk)
     to check the values of the other keyed options.")
   (xdoc::p
    "Prior to introducing @('fun'),
     we generate local events
     to avoid errors due to ignored or irrelevant formals in @('fun')
     (which may happen if @('sofun') has ignored or irrelevant formals).
     We add @('fun') to the table of instances of second-order functions."))
  (b* ((wrld (w state))
       ((unless (symbolp fun))
        (er-soft+ ctx t nil
                  "The first input must be a name, but ~x0 is not."
                  fun))
       ((unless (check-sofun-inst sofun-inst wrld))
        (er-soft+ ctx t nil
                  "The second input must be ~
                   the name of a second-order function ~
                   followed by the pairs of an instantiation, ~
                   but ~x0 is not."
                  sofun-inst))
       (sofun (car sofun-inst))
       (inst (cdr sofun-inst))
       ((unless (subsetp (alist-keys inst) (sofun-funvars sofun wrld)))
        (er-soft+ ctx t nil
                  "Each function variable key of ~x0 must be ~
                   among the function variables ~x1 ~
                   that ~x2 depends on."
                  inst (sofun-funvars sofun wrld) sofun))
       ((unless (keyword-value-listp options))
        (er-soft+ ctx t nil
                  "The inputs after the second input ~
                   must be a keyword-value list, ~
                   but ~x0 is not."
                  options))
       (keywords (evens options))
       ((unless (no-duplicatesp keywords))
        (er-soft+ ctx t nil
                  "The input keywords must be unique."))
       (print-pair (assoc-keyword :print options))
       (print (if print-pair
                  (cadr print-pair)
                :result))
       ((unless (member-eq print '(nil :all :result)))
        (er-soft+ ctx t nil
                  "The :PRINT input must be NIL, :ALL, or :RESULT, ~
                   but ~x0 is not."
                  print))
       ((er (list fun-intro-events result funvars))
        (case (sofun-kind sofun wrld)
          (plain
           (defun-inst-plain-events fun sofun inst options ctx state))
          (choice
           (defun-inst-choice-events fun sofun inst options ctx state))
          (quant
           (defun-inst-quant-events fun sofun inst options ctx state))
          (t (prog2$ (impossible) (value (list nil nil))))))
       (instmap (sof-instances sofun wrld))
       (new-instmap (put-sof-instance inst fun instmap wrld))
       (encapsulate
         `(encapsulate
            ()
            (set-ignore-ok t)
            (set-irrelevant-formals-ok t)
            ,@fun-intro-events
            (table sof-instances ',sofun ',new-instmap)))
       (result-event `(cw-event "~x0~|" ',result))
       (print-funvar-event
        (if funvars
            `(cw-event
              "The function ~x0 depends on the function variables ~x1.~%"
              ',fun ',funvars)
          `(cw-event "The function ~x0 depends on no function variables.~%"
                     ',fun)))
       (return-value-event `(value-triple ',fun))
       (event (cond ((eq print nil)
                     `(progn
                        ,encapsulate
                        ,print-funvar-event
                        ,return-value-event))
                    ((eq print :all)
                     (restore-output
                      `(progn
                         ,encapsulate
                         ,print-funvar-event
                         ,return-value-event)))
                    ((eq print :result)
                     `(progn
                        ,encapsulate
                        ,result-event
                        ,print-funvar-event
                        ,return-value-event))
                    (t (impossible)))))
    (value event)))

(defsection defun-inst-implementation
  :short "Implementation of @(tsee defun-inst)."
  :long
  "@(def defun-inst)
   @(def acl2::defun-inst)"

  (defmacro defun-inst (fun sofun-inst &rest rest)
    `(make-event-terse (defun-inst-fn
                         ',fun
                         ',sofun-inst
                         ',rest
                         (cons 'defun-inst ',fun)
                         state)))

  (defmacro acl2::defun-inst (&rest args)
    `(defun-inst ,@args)))

(defsection show-defun-inst
  :short "Show the event form generated by @(tsee defun-inst),
          without submitting them."
  :long
  "@(def show-defun-inst)
   @(def acl2::show-defun-inst)"

  (defmacro show-defun-inst (fun sofun-inst &rest rest)
    `(defun-inst-fn
       ',fun
       ',sofun-inst
       ',rest
       (cons 'defun-inst ',fun)
       state))

  (defmacro acl2::show-defun-inst (&rest args)
    `(show-defun-inst ,@args)))
