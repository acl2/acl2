; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/pseudo-event-formp" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc def-error-checker

  :parents (error-checking)

  :short "Generate an error checking function
          and an associated macro abbreviation."

  :long

  (xdoc::topstring

   (xdoc::p
    "This macro generates an error checking function
     and an associated macro abbreviation of the following form:")
   (xdoc::codeblock
    "(define <name> (<x1> ... <xn>"
    "                (description msgp)"
    "                (error-erp (not (null error-erp))"
    "                           \"Flag to return in case of error.\")"
    "                (error-val \"Value to return in case of error.\")"
    "                (ctx \"Context for errors.\")"
    "                state)"
    "  :returns (mv <erp>"
    "               <val>"
    "               state)"
    "  :mode <mode>"
    "  :verify-guards <verify-guards> ; may be absent"
    "  :parents <parents> ; may be absent"
    "  :short <short> ; may be absent"
    "  :long <long> ; may be absent"
    "  (b* (((unless <condition1>) (er-soft+"
    "                               ctx error-erp error-val . <message1>))"
    "       ..."
    "       ((unless <conditionm>) (er-soft+"
    "                               ctx error-erp error-val . <messagem>)))"
    "    (value <result>))"
    "  :no-function t)"
    ""
    "(defsection <name>$"
    "  :parents (<name>)"
    "  :short \"Calls @(tsee <name>) with"
    "          @('ctx') and @('state') as the last two arguments.\""
    "  :long \"@(def <name>$)\""
    "  (defmacro <name>$ (<x1'> ... <xn'> description error-erp error-val)"
    "    `(<name> ,<x1'> ... ,<xn'> description error-erp error-val ctx state)))")
   (xdoc::p
    "where each @('<...>'),
     except @('<erp>'), @('<val>'), and @('<x1\'>'), ..., @('<xn\'>'),
     is supplied as argument to the macro:")
   (xdoc::ul
    (xdoc::li
     "@('<name>') is the name of the function,
      and, with a @('$') added at the end, the name of the macro.")
    (xdoc::li
     "Each @('<xi>') is a symbol or
      an " (xdoc::seetopic "std::extended-formals" "extended formal") ".
      Let @('<xi\'>') be:
      @('<xi>') if @('<xi>') is a symbol;
      the name of the @('<xi>') extended formal otherwise.")
    (xdoc::li
     "@('<erp>') is a "
     (xdoc::seetopic "std::returns-specifiers" "return specifier")
     " that describes the error flag returned
      inside the " (xdoc::seetopic "error-triple" "error triple") ".
      This return specifier is:
      @('(erp (implies erp (equal erp error-erp)))')
      if @('<mode>') is @(':logic'); and
      @('(erp \"@('nil') or @('error-erp').\")')
      if @('<mode>') is @(':program').")
    (xdoc::li
     "@('<val>') is a "
     (xdoc::seetopic "std::returns-specifiers" "return specifier")
     " that describes the value returned
      inside the " (xdoc::seetopic "error-triple" "error triple") ".
      This return specifier depends on the @('<returns>') argument to the macro
      (see below for the complete list of arguments to the macro)
      and on @('<mode>'):
      if no @('<returns>') argument is supplied and @('<mode>') is @(':logic'),
      then @('<val>') is
      @('(val (and (implies erp (equal val error-val))
                   (implies (and (not erp) error-erp) (not val))))');
      if no @('<returns>') argument is supplied and @('<mode>') is @(':program'),
      then @('<val>') is
      @('(val \"@('nil') if @('erp') is @('nil'), otherwise @('error-val').\")');
      if a @('<returns>') argument is supplied,
      then @('<val>') is @('<returns>').")
    (xdoc::li
     "@('<mode>') is either @(':logic') or @(':program').")
    (xdoc::li
     "@('<verify-guards>') is either @('t') or @('nil').
      If @('<verify-guards>') is not supplied as argument,
      @(':verify-guards') is absent.")
    (xdoc::li
     "@('<parents>') is a list of parent XDOC topics.
      If @('<parents>') is not supplied as argument, @(':parents') is absent.")
    (xdoc::li
     "@('<short>') and @('<long>') are strings that document the function.
      If @('<short>') is not supplied as argument, @(':short') is absent.
      If @('<long>') is not supplied as argument, @(':long') is absent.")
    (xdoc::li
     "Each @('<conditionj>') is a term
      whose evaluation checks a condition
      on the @('<x1>'), ..., @('<xn>') arguments.
      The conditions are checked in order.")
    (xdoc::li
     "Each @('<messagej>') is a list that consists of
      a " (xdoc::seetopic "fmt" "format string") "
      followed by up to 10 terms,
      whose values fill in the placeholders of the format string.
      Generally, one of these terms should be @('description')
      and it should correspond to a @('~@') placeholder
      in the format string,
      which is appropriate for the @(tsee msgp) type of @('description').
      The @('<messagej>') list is inserted into the @(tsee er-soft+) call,
      providing an error message when @('<conditionj>') is not satisfied
      (but the previous conditions are).")
    (xdoc::li
     "@('<result>') is a term whose value is returned
      when all the conditions are satisfied."))

   (xdoc::p
    "The generated formal arguments
     @('description'), @('error-erp'), and @('error-val')
     and the generated return variables @('erp') and @('val')
     are symbols with those names in the same package as
     the @('<name>') symbol used as the name of the generated function.")

   (xdoc::p
    "The macro is called as follows:")
   (xdoc::codeblock
    "(def-error-checker <name>"
    "  (<x1> ... <xn>)"
    "  :body ((<condition1> . <message1>) ... (<conditionm> . <messagem>))"
    "  :returns <returns> ; default not used"
    "  :result <result> ; default is nil"
    "  :mode <mode> ; default is :logic"
    "  :verify-guards <verify-guards> ; default not used"
    "  :parents <parents> ; default not used"
    "  :short <short> ; default not used"
    "  :long <long> ; default not used"
    "  )")

   (xdoc::p
    "A table keeps track of all the successful calls to this macro,
     for " (xdoc::seetopic "redundant-events" "redundancy") " checking.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ def-error-checker-implementation
  :parents (def-error-checker)
  :short "Implementation of @(tsee def-error-checker)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-error-checker-table
  :short "Table of successful @(tsee def-error-checker) calls."
  :long
  (xdoc::topstring-p
   "This table records these calls as keys, with associated @('nil') values.
    This is used of redundancy checking.")

  (table def-error-checker-calls nil nil
    :guard (and (pseudo-event-formp key)
                (eq (car key) 'def-error-checker)
                (null val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-error-checker-bindings
  ((conditions-messages true-list-listp)
   (error-erp symbolp "The @('error-erp') formal.")
   (error-val symbolp "The @('error-val') formal."))
  :returns (bindings true-list-listp)
  :short "Generate the @(tsee b*) bindings of the error checking function."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the")
   (xdoc::codeblock
    "((unless <conditionj>) (er-soft+ ctx error-erp error-val . <messagej>))")
   (xdoc::p
    "bindings,
     but a binder of the form @('(unless (not <condition>))')
     is turned into @('(when <condition>)') to improve readability."))
  (b* (((when (endp conditions-messages)) nil)
       (condition-message (car conditions-messages))
       (condition (car condition-message))
       (message (cdr condition-message))
       ((mv unless/when condition)
        (case-match condition
          (('not negated-condition) (mv 'when negated-condition))
          (& (mv 'unless condition))))
       (binding `((,unless/when ,condition)
                  (er-soft+ ctx ,error-erp ,error-val ,@message)))
       (bindings (def-error-checker-bindings
                   (cdr conditions-messages)
                   error-erp
                   error-val)))
    (cons binding bindings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-error-checker-x-symbols ((xs true-listp))
  :returns (x-symbols true-listp)
  :short "Turn each @('xi') symbol into itself
          and each @('xi') extended formal into its underlying symbol."
  (b* (((when (endp xs)) nil)
       (x (car xs))
       (x-symbol (if (atom x) x (car x)))
       (x-symbols (def-error-checker-x-symbols (cdr xs))))
    (cons x-symbol x-symbols)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-error-checker-fn ((name symbolp)
                              (xs true-listp)
                              returns
                              (returns-supplied-p booleanp)
                              (conditions-messages true-list-listp)
                              result
                              (mode (member-eq mode '(:logic :program)))
                              (verify-guards booleanp)
                              (verify-guards-supplied-p booleanp)
                              (parents (symbol-listp parents))
                              (parents-supplied-p booleanp)
                              short ; could be a form with XDOC constructors
                              (short-supplied-p booleanp)
                              long ; could be a form with XDOC constructors
                              (long-supplied-p booleanp)
                              (def-error-checker-call pseudo-event-formp)
                              state)
  :returns (function+macro pseudo-event-formp)
  :verify-guards nil
  :short "Generate the function and the macro."
  (b* (((when (assoc-equal def-error-checker-call
                           (table-alist 'def-error-checker-calls (w state))))
        '(value-triple :redundant))
       (function-name name)
       (macro-name (add-suffix name "$"))
       (description (intern-in-package-of-symbol "DESCRIPTION" name))
       (error-erp (intern-in-package-of-symbol "ERROR-ERP" name))
       (error-val (intern-in-package-of-symbol "ERROR-VAL" name))
       (erp (intern-in-package-of-symbol "ERP" name))
       (val (intern-in-package-of-symbol "VAL" name))
       (function
        `(define ,function-name
           (,@xs
            (,description msgp)
            (,error-erp "Flag to return in case of error.")
            (,error-val "Value to return in case of error.")
            (ctx "Context for errors.")
            state)
           :returns (mv ,(case mode
                           (:logic
                            `(,erp (implies ,erp (equal ,erp ,error-erp))))
                           (:program
                            `(,erp "@('nil') or @('error-erp')."))
                           (t (impossible)))
                        ,(if returns-supplied-p
                             returns
                           (case mode
                             (:logic
                              `(,val (and (implies ,erp
                                                   (equal ,val ,error-val))
                                          (implies (and (not ,erp) ,error-erp)
                                                   (not ,val)))))
                             (:program
                              `(,val
                                "@('nil') if @('erp') is @('nil'),
                                   otherwise @('error-val')."))
                             (t (impossible))))
                        state)
           :mode ,mode
           ,@(and verify-guards-supplied-p
                  (list :verify-guards verify-guards))
           ,@(and parents-supplied-p
                  (list :parents parents))
           ,@(and short-supplied-p
                  (list :short short))
           ,@(and long-supplied-p
                  (list :long long))
           (b* ,(def-error-checker-bindings
                  conditions-messages error-erp error-val)
             (value ,result))
           :no-function t))
       (x-symbols (def-error-checker-x-symbols xs))
       (macro
        `(defmacro ,macro-name
             (,@x-symbols ,description ,error-erp ,error-val)
           (list ',function-name
                 ,@x-symbols
                 ,description
                 ,error-erp
                 ,error-val
                 'ctx
                 'state)))
       (section-short (concatenate 'string
                                   "Calls @(tsee "
                                   (string-downcase
                                    (symbol-name function-name))
                                   ") with @('ctx') and @('state')"
                                   " as the last two arguments."))
       (section-long (concatenate 'string
                                  "@(def "
                                  (string-downcase
                                   (symbol-name macro-name))
                                  ")"))
       (section
        `(defsection ,macro-name
           :parents (,function-name)
           :short ,section-short
           :long ,section-long
           ,macro)))
    `(progn ,function ,section)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-error-checker-macro-definition
  :short "Definition of the @(tsee def-error-checker) macro."
  :long (xdoc::topstring-@def "def-error-checker")

  (defmacro def-error-checker (&whole
                               def-error-checker-call
                               name
                               xs
                               &key
                               body
                               (returns 'nil returns-supplied-p)
                               (result 'nil)
                               (mode ':logic)
                               (verify-guards 'nil verify-guards-supplied-p)
                               (parents 'nil parents-supplied-p)
                               (short '"" short-supplied-p)
                               (long '"" long-supplied-p))
    `(make-event (def-error-checker-fn
                   ',name
                   ',xs
                   ',returns
                   ',returns-supplied-p
                   ',body
                   ',result
                   ',mode
                   ',verify-guards
                   ',verify-guards-supplied-p
                   ',parents
                   ',parents-supplied-p
                   ',short
                   ',short-supplied-p
                   ',long
                   ',long-supplied-p
                   ',def-error-checker-call
                   state))))
