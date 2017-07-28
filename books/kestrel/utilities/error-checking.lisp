; Error Checking
;
; Copyright (C) 2016-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "enumerations")
(include-book "event-forms")
(include-book "numbered-names")
(include-book "strings")
(include-book "symbol-true-list-alists")
(include-book "terms")

(local (set-default-parents error-checking))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc error-checking
  :parents (kestrel-utilities errors)
  :short "Utilities for error checking."
  :long
  "<p>
   Each error-checking function in these utilities
   causes a <see topic='@(url er)'>soft error</see>,
   with an informative message,
   when certain conditions are not satisified.
   These error-checking functions are useful, for instance,
   to programmatically validate inputs from the user to a macro.
   Inside @(tsee b*), the <see topic='@(url patbind-er)'>@('er') binder</see>
   can be used with calls to these functions.
   </p>
   <p>
   These error-checking functions include @(tsee msgp) parameters
   to describe the values being checked in error message.
   When these functions are called,
   the strings in the description parameters
   should be capitalized based on where they occur in the error messages.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-error-checker

  :short "Generate an error-checking function
          and associated macro abbreviation."

  :long

  "<p>
   This macro generates an error-checking function
   and an associated macro abbreviation of the following form:
   </p>

   @({
     (define <name> (<x1> ... <xn>
                     (description msgp)
                     (ctx \"Context for errors.\")
                     state)
       :returns (mv (erp
                     \"<see topic='@(url acl2::booleanp)'>@('booleanp')</see>
                      flag of the
                      <see topic='@(url acl2::error-triple)'>error
                      triple</see>.\")
                    <y>
                    state)
       :mode :program
       :parents <parents>  ; optional
       :short <short>
       :long <long>  ; optional
       (b* (((unless <condition1>) (er soft ctx . <message1>))
            ...
            ((unless <conditionm>) (er soft ctx . <messagem>)))
         (value <result>))
       :no-function t)

     (defsection <name>$
       :parents (<name>)
       :short \"Calls @(tsee <name>) with
               @('ctx') and @('state') as the last two arguments.\"
       :long \"@(def <name>$)\"
       (defmacro <name>$ (<x1'> ... <xn'> description)
         `(<name> ,<x1'> ... ,<xn'> description ctx state)))
   })

   <p>
   where each @('<...>') element is supplied as argument to the macro:
   </p>

   <ul>

     <li>
     @('<name>') is the name of the function,
     and, with a @('$') added at the end, the name of the macro.
     </li>

     <li>
     Each @('<xi>') is a symbol or
     an <see topic='@(url std::extended-formals)'>extended formal</see>.
     Let @('<xi\'>') be:
     @('<xi>') if @('<xi>') is a symbol;
     the name of the @('<xi>') extended formal otherwise.
     </li>

     <li>
     @('<y>') is a symbol
     or <see topic='@(url std::returns-specifiers)'>return specifier</see>
     that describes the value returned
     inside an <see topic='@(url error-triple)'>error triple</see>.
     Since the error-checking function is generated in program mode
     (because @(tsee er) expands into a term
     that calls the program-mode function @(tsee error1)),
     these return specifier should not use types but only documentation strings.
     </li>

     <li>
     @('<parents>') is a list of parent <see topic='@(url xdoc)'>topics</see>.
     This is absent if @('<parents>') is not supplied as argument,
     in which case the default parent topics are used, as usual.
     </li>

     <li>
     @('<short>') and @('<long>') are strings that document the function.
     </li>

     <li>
     Each @('<conditionj>') is a term
     whose evaluation checks a condition
     on the @('<x1>'), ..., @('<xn>') arguments.
     The conditions are checked in order.
     </li>

    <li>
     Each @('<messagej>') is a list that consists of
     a <see topic='@(url fmt)'>format string</see>
     followed by up to 10 terms,
     whose values fill in the placeholders of the format string.
     Generally, one of these terms should be @('description')
     and it should correspond to a @('~@') placeholder
     in the format string,
     which is appropriate for the @(tsee msgp) type of @('description').
     The @('<messagej>') list is inserted into the @(tsee er) call,
     providing an error message when @('<conditionj>') is not satisfied
     (but the previous conditions are).
     </li>

     <li>
     @('<result>') is a term whose value is returned
     when all the conditions are satisfied.
     </li>

   </ul>

   <p>
   The macro is called as follows:
   </p>

   @({
     (def-error-checker <name>
       (<x1> ... <xn>)
       <short>
       ((<condition1> . <message1>) ... (<conditionm> . <messagem>))
       <y> ; optional - default is (nothing \"Always @('nil').\")
       <result> ; optional - default is nil
       :parents <parents> ; optional - default is :not-supplied
       :long <long> ; optional - default is :not-supplied
       )
   })

   <p>
   A table keeps track of all the successful calls to this macro,
   for <see topic='@(url redundant-events)'>redundancy</see> checking.
   </p>

   @(def def-error-checker)"

  ;; record successful calls to DEF-ERROR-CHECKER, for redundancy checking:
  (table def-error-checker-calls nil nil
    :guard (and (pseudo-event-formp key)
                (eq (car key) 'def-error-checker)
                (null val)))

  (define def-error-checker-bindings ((conditions-messages true-list-listp))
    :returns (bindings true-list-listp)
    :parents (def-error-checker)
    :short "Generate the @(tsee b*) bindings of the error-checking function."
    :long
    "<p>
     These are the
     </p>
     @({
       ((unless <conditionj>) (er soft ctx . <messagej>))
     })
     <p>
     bindings,
     but a binder of the form @('(unless (not <condition>))')
     is turned into @('(when <condition>)') to improve readability.
     </p>"
    (def-error-checker-bindings-aux conditions-messages nil)

    :prepwork
    ((define def-error-checker-bindings-aux
       ((conditions-messages true-list-listp)
        (rev-current-bindings true-list-listp))
       :returns (final-bindings true-list-listp
                                :hyp (true-list-listp rev-current-bindings))
       :parents (def-error-checker-bindings)
       (b* (((when (endp conditions-messages)) (rev rev-current-bindings))
            (condition-message (car conditions-messages))
            (condition (car condition-message))
            (message (cdr condition-message))
            ((mv unless/when condition)
             (case-match condition
               (('not negated-condition) (mv 'when negated-condition))
               (& (mv 'unless condition))))
            (binding `((,unless/when ,condition) (er soft ctx ,@message))))
         (def-error-checker-bindings-aux
           (cdr conditions-messages)
           (cons binding rev-current-bindings))))))

  (define def-error-checker-x-symbols ((xs true-listp))
    :returns (x-symbols true-listp)
    :parents (def-error-checker)
    :short
    "Turn each @('xi') symbol into itself
     and each @('xi')
     <see topic='@(url std::extended-formals)'>extended formal</see>
     into its underlying symbol."
    (def-error-checker-x-symbols-aux xs nil)

    :prepwork
    ((define def-error-checker-x-symbols-aux
       ((xs true-listp)
        (rev-current-x-symbols true-listp))
       :returns (final-x-symbols true-listp
                                 :hyp (true-listp rev-current-x-symbols)
                                 :rule-classes :type-prescription)
       :parents (def-error-checker-x-symbols)
       (cond ((endp xs) (rev rev-current-x-symbols))
             (t (let* ((x (car xs))
                       (x-symbol (if (atom x) x (car x))))
                  (def-error-checker-x-symbols-aux
                    (cdr xs)
                    (cons x-symbol rev-current-x-symbols))))))))

  (define def-error-checker-fn ((name symbolp)
                                (xs true-listp)
                                y
                                (conditions-messages true-list-listp)
                                result
                                (parents (or (symbol-listp parents)
                                             (eq parents :not-supplied)))
                                (short stringp)
                                (long (or (stringp long)
                                          (eq long :not-supplied)))
                                (def-error-checker-call pseudo-event-formp)
                                state)
    :returns (function+macro pseudo-event-formp)
    :verify-guards nil
    :parents (def-error-checker)
    :short "Generate the function and the macro."
    (b* (((when (assoc-equal def-error-checker-call
                             (table-alist 'def-error-checker-calls (w state))))
          '(value-triple :redundant))
         (function-name name)
         (macro-name (add-suffix name "$"))
         (description (intern-in-package-of-symbol "DESCRIPTION" name))
         (function
          `(define ,function-name
             (,@xs (,description msgp) (ctx "Context for errors.") state)
             :returns (mv
                       (erp
                        "<see topic='@(url acl2::booleanp)'>@('booleanp')</see>
                         flag of the
                         <see topic='@(url acl2::error-triple)'>error
                         triple</see>.")
                       ,y
                       state)
             :mode :program
             ,@(and (not (eq parents :not-supplied))
                    (list :parents parents))
             :short ,short
             ,@(and (not (eq long :not-supplied))
                    (list :long long))
             (b* ,(def-error-checker-bindings conditions-messages)
               (value ,result))
             :no-function t))
         (x-symbols (def-error-checker-x-symbols xs))
         (macro
          `(defmacro ,macro-name (,@x-symbols ,description)
             (list ',function-name ,@x-symbols ,description 'ctx 'state)))
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

  (defmacro def-error-checker (&whole def-error-checker-call
                                      name
                                      xs
                                      short
                                      conditions-messages
                                      &optional
                                      (y '(nothing "Always @('nil')."))
                                      (result 'nil)
                                      &key
                                      (parents ':not-supplied)
                                      (long ':not-supplied))
    `(make-event (def-error-checker-fn
                   ',name
                   ',xs
                   ',y
                   ',conditions-messages
                   ',result
                   ',parents
                   ',short
                   ',long
                   ',def-error-checker-call
                   state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-nil
  ((x "Value to check."))
  "Cause an error if a value is not @('nil')."
  (((eq x nil) "~@0 must be NIL." description)))

(def-error-checker ensure-boolean
  ((x "Value to check."))
  "Cause an error if a value is not a boolean."
  (((booleanp x) "~@0 must be T or NIL." description)))

(def-error-checker ensure-symbol
  ((x "Value to check."))
  "Cause an error if a value is not a symbol."
  (((symbolp x) "~@0 must be a symbol." description)))

(def-error-checker ensure-symbol-list
  ((x "Value to check."))
  "Cause an error if a value is not a @('nil')-terminated list of symbols."
  (((symbol-listp x)
    "~@0 must be a NIL-terminated list of symbols." description)))

(def-error-checker ensure-symbol-alist
  ((x "Value to check."))
  "Cause an error if a value is not a @('nil')-terminated alist
   whose keys are symbols."
  (((symbol-alistp x)
    "~@0 must be an alist with symbols as keys." description)))

(def-error-checker ensure-symbol-true-list-alist
  ((x "Value to check."))
  "Cause an error if a value is not
   an alist from symbols to @('nil')-terminated lists."
  (((symbol-true-list-alistp x)
    "~@0 must be an alist from symbols to NIL-terminated lists."
    description)))

(def-error-checker ensure-symbol-different
  ((symb symbolp "Symbol to check.")
   (symb1 symbolp "Symbol that @('symb') must be different from.")
   (description1 msgp "Description of @('symb1'), for the error message."))
  "Cause an error if a symbol is the same as another symbol."
  (((not (eq symb symb1))
    "~@0 must be different from ~@1." description description1)))

(def-error-checker ensure-list-no-duplicates
  ((list true-listp "List to check."))
  "Cause an error if a @('nil')-terminated list has duplicates."
  (((no-duplicatesp-equal list)
    "~@0 must have no duplicates." description)))

(def-error-checker ensure-list-subset
  ((list true-listp "List to check.")
   (super true-listp "List that must include all the elements of @('list')."))
  "Cause an error if any element of a @('nil')-terminated list
   is not a member of another list."
  (((subsetp-equal list super)
    "~@0 must have only elements in ~x1, but it includes the ~@2."
    description
    super
    (let ((extra (remove-duplicates-equal (set-difference-equal list super))))
      (if (= (len extra) 1)
          (msg "element ~x0" (car extra))
        (msg "elements ~&0" extra))))))

(def-error-checker ensure-doublet-list
  ((x "Value to check."))
  "Cause an error if a value is not a list of doublets."
  (((doublet-listp x) "~@0 must be a list of doublets." description)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-defun-mode
  ((x "Value to check."))
  "Cause an error if a value is not a @(see defun-mode)."
  (((logic/program-p x) "~@0 must be :LOGIC or :PROGRAM." description)))

(def-error-checker ensure-defun-mode-or-auto
  ((x "Value to check."))
  "Cause an error if a value is not a @(see defun-mode) or @(':auto')."
  (((logic/program/auto-p x)
    "~@0 must be :LOGIC, :PROGRAM, or :AUTO." description)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-boolean-or-auto
  ((x "Value to check."))
  "Cause an error if a value is not a boolean or @(':auto')."
  (((t/nil/auto-p x) "~@0 must be T, NIL, or :AUTO." description)))

(def-error-checker ensure-boolean-or-auto-and-return-boolean
  ((x "Value to check.")
   (r booleanp "Value to return if @('x') is @(':auto')."))
  "Cause an error if a value is not @('t'), @('nil'), or @(':auto');
   otherwise return a boolean result."
  (((t/nil/auto-p x) "~@0 must be T, NIL, or :AUTO." description))
  (result "A @(tsee booleanp).")
  (if (booleanp x) x r)
  :long
  "<p>
   If @('x') is a boolean, return it as result.
   If @('x') is @(':auto'), return the boolean @('r'),
   as if @(':auto') meant copying the result from @('r').
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-variable-name
  ((x "Value to check."))
  "Cause an error if a value is not a valid variable name."
  (((legal-variablep x)
    "~@0 must be a valid name for a variable." description)))

(def-error-checker ensure-constant-name
  ((x "Value to check."))
  "Cause an error if a value is not a valid constant name."
  (((legal-constantp x)
    "~@0 must be a valid name for a constant." description)))

(def-error-checker ensure-symbol-not-stobj
  ((symb symbolp "Symbol to check."))
  "Cause an error if a symbol is the name of a @(see stobj)."
  (((not (stobjp symb t (w state)))
    "~@0 must not be the name of a STOBJ." description)))

(def-error-checker ensure-symbol-function
  ((symb symbolp "Symbol to check."))
  "Cause an error if a symbol is not the name of an existing function."
  (((function-symbolp symb (w state))
    "~@0 must name an existing function." description)))

(def-error-checker ensure-symbol-new-event-name
  ((symb symbolp "Symbol to check."))
  "Cause an error if a symbol cannot be the name of a new event."
  (((not (equal (symbol-package-name symb) *main-lisp-package-name*))
    "~@0 must not be in the main Lisp package." description)
   ((not (keywordp symb))
    "~@0 must not be a keyword." description)
   ((not (logical-namep symb (w state)))
    "~@0 is already in use." description))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   The symbol must not be in the main Lisp package,
   must not be a keyword,
   and must not be already in use.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-name
  ((x "Value to check."))
  "Cause an error if a value is not the name of an existing function."
  (((function-namep x (w state))
    "~@0 must be the name of an existing function." description)))

(define ensure-function-name-or-numbered-wildcard ((x "Value to check.")
                                                   (description msgp)
                                                   (ctx "Context for errors.")
                                                   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url error-triple)'>error triple</see>.")
               (name "A @(tsee symbolp).")
               state)
  :mode :program
  :short "Cause an error if a value is not
          either the name of an existing function
          or a <see topic='@(url numbered-names)'>numbered name</see>
          with a wildcard index that
          <see topic='@(url resolve-numbered-name-wildcard)'>resolves</see>
          to the name of an existing function."
  :long
  "<p>
   If successful, return the name of the existing function.
   </p>
   <p>
   The string in the description should be capitalized
   because it occurs at the beginning of all the error messages except one;
   for that one, @(tsee msg-downcase-first) is applied to the description.
   </p>"
  (b* (((er &) (ensure-symbol$ x description))
       (name (resolve-numbered-name-wildcard x (w state)))
       ((er &) (ensure-symbol-function$
                name (if (eq x name)
                         (msg "~@0, which is the symbol ~x1," description x)
                       (msg "The symbol ~x0, to which ~@1 resolves to,"
                            name (msg-downcase-first description))))))
    (value name))
  ///

  (defsection ensure-function-name-or-numbered-wildcard$
    :parents (ensure-function-name-or-numbered-wildcard)
    :short "Call @(tsee ensure-function-name-or-numbered-wildcard)
            with @('ctx') and @('state') as the last two arguments."
    (defmacro ensure-function-name-or-numbered-wildcard$ (x description)
      `(ensure-function-name-or-numbered-wildcard ,x ,description ctx state))))

(define ensure-function/macro/lambda ((x "Value to check.")
                                      (description msgp)
                                      (ctx "Context for errors.")
                                      state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url error-triple)'>error triple</see>.")
               (result
                "A tuple @('(pfn stobjs-in stobjs-out new-description)')
                 consisting of
                 a @(tsee pseudo-fn/lambda-p),
                 a @(tsee symbol-listp),
                 a @(tsee symbol-listp), and
                 a @(tsee msgp).")
               state)
  :mode :program
  :short "Cause an error if a value is not
          the name of an existing function,
          the name of an existing macro,
          or a lambda expression."
  :long
  "<p>
   If @('x') is the name of a function, return @('x') itself,
   along with its @(tsee stobjs-in) and @(tsee stobjs-out) lists.
   If @('x') is the name of a macro,
   return the <see topic='@(url term)'>translation</see>
   of the lambda expression @('(lambda (x1 ... xn) (x x1 ... xn))'),
   where @('x1'), ..., @('xn') are the required arguments of @('x'),
   along with the @(tsee stobjs-in) and @(tsee stobjs-out) lists
   of the lambda expression (see below).
   If @('x') is a lambda expression,
   return its <see topic='@(url term)'>translation</see>,
   along with the @(tsee stobjs-in) and @(tsee stobjs-out) lists
   of the lambda expression (see below).
   </p>
   <p>
   In each of the above cases,
   also return a new description of @('x'),
   based on whether @('x') is a function, macro, or lambda expression.
   The new description can be passed to error-checking functions
   to check additional conditions on the function, macro, or lambda expression.
   </p>
   <p>
   The @(tsee stobjs-in) list of a lambda expression is calculated
   in the same way as the @(tsee stobjs-in) list of a function,
   using @('compute-stobj-flags') on the lambda expression's formals
   (instead of the function's formal).
   The @(tsee stobjs-out) list of a lambda expression is returned
   by @(tsee check-user-lambda).
   </p>
   <p>
   If the translation of a lambda expression fails,
   the error message returned by @(tsee check-user-lambda)
   is incorporated into a larger error message.
   Since the message returned starts with the lambda expression,
   it can be incorporated into the larger message
   without capitalization concerns.
   </p>"
  (b* ((wrld (w state)))
    (cond ((function-namep x wrld)
           (value (list x
                        (stobjs-in x wrld)
                        (stobjs-out x wrld)
                        (msg "~@0, which is the function ~x1," description x))))
          ((macro-namep x wrld)
           (b* ((args (macro-required-args x wrld))
                (ulambda `(lambda ,args (,x ,@args)))
                ((mv tlambda stobjs-out) (check-user-lambda ulambda wrld))
                (stobjs-in (compute-stobj-flags args t wrld)))
             (value
              (list tlambda
                    stobjs-in
                    stobjs-out
                    (msg "~@0, which is the lambda expression ~x1 ~
                          denoted by the macro ~x2,"
                         description ulambda x)))))
          ((symbolp x)
           (er soft ctx
               "~@0 must be a function name, a macro name, ~
                or a lambda expression.  ~
                The symbol ~x1 is not the name of a function or macro."
               description x))
          (t (b* (((mv tlambda/msg stobjs-out) (check-user-lambda x wrld))
                  ((when (msgp tlambda/msg))
                   (er soft ctx
                       "~@0 must be a function name, a macro name, ~
                        or a lambda expression.  ~
                        Since ~x1 is not a symbol, ~
                        it must be a lambda expression.  ~
                        But ~@2"
                       description x tlambda/msg))
                  (tlambda tlambda/msg)
                  (stobjs-in
                   (compute-stobj-flags (lambda-formals tlambda) t wrld)))
               (value (list tlambda
                            stobjs-in
                            stobjs-out
                            (msg "~@0, which is the lambda expression ~x1,"
                                 description x)))))))
  ///

  (defsection ensure-function/macro/lambda$
    :parents (ensure-function/macro/lambda)
    :short "Call @(tsee ensure-function/macro/lambda)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/macro/lambda$)"
    (defmacro ensure-function/macro/lambda$ (x description)
      `(ensure-function/macro/lambda ,x ,description ctx state))))

(define ensure-term ((x "Value to check.")
                     (description msgp)
                     (ctx "Context for errors.")
                     state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url error-triple)'>error triple</see>.")
               (result
                "A tuple @('(term stobjs-out)')
                 consisting of
                 a @(tsee pseudo-termp) and
                 a @(tsee symbol-listp).")
               state)
  :mode :program
  :short "Cause an error if a value is not a term."
  :long
  "<p>
   If successful,
   return the <see topic='@(url term)'>translation</see> of @('x')
   and the @(tsee stobjs-out) list returned by @(tsee check-user-term).
   </p>
   <p>
   If @(tsee check-user-term) fails,
   the error message it returns is incorporated into a larger error message.
   Since the message returned by @(tsee check-user-term) starts with the term,
   it can be incorporated into the larger message
   without capitalization concerns.
   </p>"
  (b* (((mv term/msg stobjs-out) (check-user-term x (w state))))
    (if (msgp term/msg)
        (er soft ctx
            "~@0 must be a term. But ~@1"
            description term/msg)
      (value (list term/msg stobjs-out))))
  ///

  (defsection ensure-term$
    :parents (ensure-term)
    :short "Call @(tsee ensure-term)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-term$)"
    (defmacro ensure-term$ (x description)
      `(ensure-term ,x ,description ctx state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-logic-mode
  ((fn (function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is in program mode."
  (((logicp fn (w state))
    "~@0 must be in logic mode." description)))

(def-error-checker ensure-function-defined
  ((fn (logic-function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is not defined."
  (((definedp fn (w state))
    "~@0 must be defined." description)))

(def-error-checker ensure-function-non-recursive
  ((fn (logic-function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is recursive."
  (((not (recursivep fn nil (w state)))
    "~@0 must not be recursive." description)))

(def-error-checker ensure-function-recursive
  ((fn (logic-function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is not recursive."
  (((recursivep fn nil (w state))
    "~@0 must be recursive." description)))

(def-error-checker ensure-function-singly-recursive
  ((fn (logic-function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is not singly recursive."
  (((= (len (recursivep fn nil (w state))) 1)
    "~@0 must be singly recursive." description)))

(def-error-checker ensure-function-known-measure
  ((fn (and (logic-function-namep fn (w state))
            (recursivep fn nil (w state)))
       "Function to check."))
  "Cause an error if a recursive function
   has an unknown measure (i.e. one with @(':?'))."
  (((not (eq (car (measure fn (w state))) :?))
    "~@0 must have a known measure, i.e. not one of the form (:? ...)."
    description)))

(def-error-checker ensure-function-not-in-termination-thm
  ((fn (and (logic-function-namep fn (w state))
            (recursivep fn nil (w state)))
       "Function to check."))
  "Cause an error if a recursive function
   occurs in its own termination theorem."
  (((not (member-eq fn (all-ffn-symbs (termination-theorem fn (w state)) nil)))
    "~@0 must not occur in its own termination theorem, which is~%~x1."
    description (termination-theorem fn (w state)))))

(def-error-checker ensure-function-no-stobjs
  ((fn (and (function-namep fn (w state))
            (not (member-eq fn *stobjs-out-invalid*))) "Function to check."))
  "Cause an error if a function has input or output @(see stobj)s."
  (((no-stobjs-p fn (w state))
    "~@0 must have no input or output stobjs." description))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   The function must not be one whose @(tsee stobjs-out) are invalid.
   </p>")

(def-error-checker ensure-function-arity
  ((fn (function-namep fn (w state)) "Function to check.")
   (n natp "Arity that @('fn') must have."))
  "Cause an error if a function does not have a given arity."
  (((= (arity fn (w state)) n)
    "~@0 must take ~x1 ~@2."
    description n (if (= n 1) "argument" "arguments"))))

(def-error-checker ensure-function-has-args
  ((fn (function-namep fn (w state)) "Function to check."))
  "Cause an error if a function has no arguments."
  (((/= (arity fn (w state)) 0)
    "~@0 must take at least one argument." description)))

(def-error-checker ensure-function-number-of-results
  ((fn (and (function-namep fn (w state))
            (not (member-eq fn *stobjs-out-invalid*))) "Function to check.")
   (n posp "Number of results that @('fn') must have."))
  "Cause an error if a function does not have a given number of results."
  (((= (number-of-results fn (w state)) n)
    "~@0 must return ~x1 ~@2."
    description n (if (= n 1) "result" "results")))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   The function must not be one whose @(tsee stobjs-out) are invalid.
   </p>")

(def-error-checker ensure-function-guard-verified
  ((fn (function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is not guard-verified."
  (((guard-verified-p fn (w state))
    "~@0 must be guard-verified." description)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-term-logic-mode
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term calls any program-mode function."
  (((logic-fnsp term (w state))
    "~@0 must call only logic-mode functions, ~
     but it calls the program-mode ~@1."
    description
    (let ((fns (all-program-ffn-symbs term nil (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns))))))

(def-error-checker ensure-term-free-vars-subset
  ((term pseudo-termp "Term to check.")
   (vars symbol-listp
         "Variables that must include all the free variables of @('term')."))
  "Cause an error if a term includes free variables outside a given set."
  (((subsetp-eq (all-vars term) vars)
    "~@0 must contain no free variables other than ~&1, ~
     but it contains the ~@2."
    description
    vars
    (let ((extra (set-difference-eq (all-vars term) vars)))
      (if (= (len extra) 1)
          (msg "variable ~x0" (car extra))
        (msg "variables ~&0" extra))))))

(def-error-checker ensure-term-ground
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term is not ground (i.e. it has free variables)."
  (((null (all-vars term))
    "~@0 must contain no free variables, but it contains the ~@1."
    description
    (let ((vars (all-vars term)))
      (if (= (len vars) 1)
          (msg "variable ~x0" (car vars))
        (msg "variables ~&0" vars))))))

(def-error-checker ensure-term-no-stobjs
  ((stobjs-out
    symbol-listp
    "@(tsee stobjs-out) list of the term
     whose @(see stobj)s are to be checked."))
  "Cause an error if a term has output @(see stobj)s."
  (((all-nils stobjs-out)
    "~@0 must have no (output) stobjs." description)))

(def-error-checker ensure-term-guard-verified-fns
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term calls any non-guard-verified function."
  (((guard-verified-fnsp term (w state))
    "~@0 must call only guard-verified functions ~
     but it calls the non-guard-verified ~@1."
    description
    (let ((fns (all-non-gv-ffn-symbs term nil (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns))))))

(def-error-checker ensure-term-guard-verified-exec-fns
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term
   calls any non-guard-verified function for execution."
  (((guard-verified-exec-fnsp term (w state))
    "~@0 must call only guard-verified functions ~
     (except possibly in the :LOGIC subterms of MBEs), ~
     but it calls the non-guard-verified ~@1."
    description
    (let ((fns (all-non-gv-exec-ffn-symbs term (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns))))))

(def-error-checker ensure-term-does-not-call
  ((term pseudo-termp "Term to check.")
   (fn symbolp "Function that @('term') must not call."))
  "Cause an error if a term calls a given function."
  (((not (ffnnamep fn term)) "~@0 must not call ~x1." description fn)))

(def-error-checker ensure-term-if-call
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term is not a call to @(tsee if)."
  (((and (nvariablep term) (eq (ffn-symb term) 'if))
    "~@0 must start with IF." description))
  (test+then+else "A @(tsee pseudo-term-listp) of length 3.")
  (list (fargn term 1) (fargn term 2) (fargn term 3))
  :long
  "<p>
   If the term is a call to @(tsee if),
   return its test, then&rdquo; branch, and else&rdquo; branch.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-lambda-logic-mode
  ((lambd pseudo-lambdap "Lambda expression to check."))
  "Cause an error if a lambda expression calls any program-mode function."
  (((lambda-logic-fnsp lambd (w state))
    "~@0 must call only logic-mode functions, ~
     but it calls the program-mode ~@1."
    description
    (let ((fns (all-program-ffn-symbs (lambda-body lambd) nil (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns))))))

(def-error-checker ensure-lambda-arity
  ((lambd pseudo-lambdap "Lambda expression to check.")
   (n natp "Arity that @('lambd') must have."))
  "Cause an error if a lambda expression does not have a given arity."
  (((= (arity lambd (w state)) n)
    "~@0 must take ~x1 ~@2."
    description n (if (= n 1) "argument" "arguments"))))

(def-error-checker ensure-lambda-guard-verified-fns
  ((lambd pseudo-lambdap "Lambda expression to check."))
  "Cause an error if a lambda expression calls any non-guard-verified function."
  (((lambda-guard-verified-fnsp lambd (w state))
    "~@0 must call only guard-verified functions, ~
     but it calls the non-guard-verified ~@1."
    description
    (let ((fns (all-non-gv-ffn-symbs (lambda-body lambd) nil (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns))))))

(def-error-checker ensure-lambda-guard-verified-exec-fns
  ((lambd pseudo-lambdap "Lambda expression to check."))
  "Cause an error if a lambda expression
   calls any non-guard-verified function for execution."
  (((lambda-guard-verified-exec-fnsp lambd (w state))
    "~@0 must call only guard-verified functions ~
     (except possibly in the :LOGIC subterms of MBEs), ~
     but it calls the non-guard-verified ~@1."
    description
    (let ((fns (all-non-gv-exec-ffn-symbs (lambda-body lambd) (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns))))))

(def-error-checker ensure-lambda-closed
  ((lambd pseudo-lambdap "Lambda expression to check."))
  "Cause an error if a lambda expression is not closed."
  (((lambda-closedp lambd) "~@0 must be closed." description)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function/lambda-arity
  ((stobjs-in
    symbol-listp
    "@(tsee stobjs-in) list of the function or lambda expression
     whose arity is to be checked.")
   (n natp "Arity that the function or lambda expression must have."))
  "Cause an error if a function or lambda expression
   does not have a given arity."
  (((= (len stobjs-in) n)
    "~@0 must take ~x1 ~@2."
    description n (if (= n 1) "argument" "arguments")))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   The arity of the function or lambda expression is checked
   by examining the @(tsee stobjs-in) list
   of the function or lambda expression.
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee stobjs-in) list)
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>")

(def-error-checker ensure-function/lambda-no-stobjs
  ((stobjs-in
    symbol-listp
    "@(tsee stobjs-in) list of the function or lambda expression
     whose @(see stobj)s are to be checked.")
   (stobjs-out
    symbol-listp
    "@(tsee stobjs-out) list of the function or lambda expression
     whose @(see stobj)s are to be checked."))
  "Cause an error if a function or lambda expression
   has input or output @(see stobj)s."
  (((and (all-nils stobjs-in)
         (all-nils stobjs-out))
    "~@0 must have no input or output stobjs." description))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee stobjs-in) and @(tsee stobjs-out) lists)
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>")

(define ensure-function/lambda-logic-mode
  ((fn/lambda pseudo-fn/lambda-p "Function or lambda expression to check.")
   (description msgp)
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url error-triple)'>error triple</see>.")
               (nothing "Always @('nil').")
               state)
  :mode :program
  :short "Cause an error if a function or lambda expression is
          a function in program mode or
          a lambda expression that calls some program-mode function."
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-fn/lambda-p))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  (if (symbolp fn/lambda)
      (ensure-function-logic-mode$ fn/lambda description)
    (ensure-lambda-logic-mode$ fn/lambda description))
  ///

  (defsection ensure-function/lambda-logic-mode$
    :parents (ensure-function/lambda-logic-mode)
    :short "Call @(tsee ensure-function/lambda-logic-mode)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/lambda-logic-mode$)"
    (defmacro ensure-function/lambda-logic-mode$ (x description)
      `(ensure-function/lambda-logic-mode ,x ,description ctx state))))

(define ensure-function/lambda-guard-verified-fns
  ((fn/lambda pseudo-fn/lambda-p "Function or lambda expression to check.")
   (description msgp)
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url error-triple)'>error triple</see>.")
               (nothing "Always @('nil').")
               state)
  :mode :program
  :short "Cause an error if a function or lambda expression is
          a non-guard-verified function or
          a lambda expression that calls some non-guard-verified function."
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-fn/lambda-p))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  (if (symbolp fn/lambda)
      (ensure-function-guard-verified$ fn/lambda description)
    (ensure-lambda-guard-verified-fns$ fn/lambda description))
  ///

  (defsection ensure-function/lambda-guard-verified-fns$
    :parents (ensure-function/lambda-guard-verified-fns)
    :short "Call @(tsee ensure-function/lambda-guard-verified-fns)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/lambda-guard-verified-fns$)"
    (defmacro ensure-function/lambda-guard-verified-fns$ (x description)
      `(ensure-function/lambda-guard-verified-fns ,x ,description ctx state))))

(define ensure-function/lambda-guard-verified-exec-fns
  ((fn/lambda pseudo-fn/lambda-p "Function or lambda expression to check.")
   (description msgp)
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url error-triple)'>error triple</see>.")
               (nothing "Always @('nil').")
               state)
  :mode :program
  :short "Cause an error if a function or lambda expression is
          a non-guard-verified function or
          a lambda expression that calls some non-guard-verified function,
          except possibly in the @(':logic') subterms of @(tsee mbe)s."
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-fn/lambda-p))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  (if (symbolp fn/lambda)
      (ensure-function-guard-verified$ fn/lambda description)
    (ensure-lambda-guard-verified-exec-fns$ fn/lambda description))
  ///

  (defsection ensure-function/lambda-guard-verified-exec-fns$
    :parents (ensure-function/lambda-guard-verified-exec-fns)
    :short "Call @(tsee ensure-function/lambda-guard-verified-exec-fns)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/lambda-guard-verified-exec-fns$)"
    (defmacro ensure-function/lambda-guard-verified-exec-fns$ (x description)
      `(ensure-function/lambda-guard-verified-exec-fns
        ,x ,description ctx state))))

(def-error-checker ensure-function/lambda-closed
  ((fn/lambda pseudo-fn/lambda-p "Function or lambda expression to check."))
  "Cause an error if a function or lambda expression is
   a non-closed lambda expression."
  (((or (symbolp fn/lambda) (lambda-closedp fn/lambda))
    "~@0 must be closed." description))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-fn/lambda-p))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function/lambda/term-number-of-results
  ((stobjs-out
    symbol-listp
    "@(tsee stobjs-out) list of the function or lambda expression or term
     whose number of results is to be checked.")
   (n posp
      "Number of results that
       the function or lambda expression or term must have."))
  "Cause an error if a function or lambda expression or term
   does not have a given number of results."
  (((= (len stobjs-out) n)
    "~@0 must return ~x1 ~@2."
    description n (if (= n 1) "result" "results")))
  (nothing "Always @('nil').")
  nil
  :long
  "<p>
   The number of results of the function or lambda expression or term is checked
   by examining the @(tsee stobjs-out) list
   of the function or lambda expression or term.
   This error-checking function is useful after calling
   @(tsee ensure-function/macro/lambda) (for a function or lambda expression)
   or @(tsee ensure-term) (for a term),
   both of which return the @(tsee stobjs-out) list,
   to handle functions and lambda expressions and terms uniformly.
   The @('description') parameter
   should describe the function or lambda expression or term.
   </p>")
