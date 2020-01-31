; Error Checking
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/system/numbered-names" :dir :system)
(include-book "kestrel/utilities/system/terms" :dir :system)
(include-book "std/typed-alists/symbol-truelist-alistp" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "def-error-checker")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ error-checking
  :parents (kestrel-utilities errors)
  :short "Utilities for error checking."
  :long
  "<p>
   Each error-checking function in these utilities
   causes a <see topic='@(url er-soft+)'>soft error</see>,
   with an informative message,
   and optionally informative error flag and value,
   when certain conditions are not satisified.
   These error-checking functions are useful, for instance,
   to programmatically validate inputs from the user to a macro,
   providing the informative error messages to the user.
   The informative error flags and values are useful
   when such a macro is invoked programmatically,
   to enable the caller to take appropriate actions
   based on the nature of the error,
   as with an exception mechanism.
   </p>
   <p>
   Inside @(tsee b*), the <see topic='@(url patbind-er)'>@('er') binder</see>
   can be used with calls to these error-checking functions.
   </p>
   <p>
   These error-checking functions include @(tsee msgp) parameters
   to describe the values being checked in error message.
   When these functions are called,
   the strings in the description parameters
   should be capitalized based on where they occur in the error messages.
   </p>"
  :default-parent t)

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

(def-error-checker ensure-string
  ((x "Value to check."))
  "Cause an error if a value is not a string."
  (((stringp x) "~@0 must be a string." description)))

(def-error-checker ensure-string-or-nil
  ((x "Value to check."))
  "Cause an error if a value is not a string or @('nil')."
  (((maybe-stringp x) "~@0 must be a string or NIL." description)))

(def-error-checker ensure-symbol-list
  ((x "Value to check."))
  "Cause an error if a value is not a true list of symbols."
  (((symbol-listp x)
    "~@0 must be a true list of symbols." description)))

(def-error-checker ensure-symbol-alist
  ((x "Value to check."))
  "Cause an error if a value is not a true alist
   whose keys are symbols."
  (((symbol-alistp x)
    "~@0 must be an alist with symbols as keys." description)))

(def-error-checker ensure-symbol-truelist-alist
  ((x "Value to check."))
  "Cause an error if a value is not an alist from symbols to true lists."
  (((symbol-truelist-alistp x)
    "~@0 must be an alist from symbols to true lists."
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
  "Cause an error if a true list has duplicates."
  (((no-duplicatesp-equal list)
    "~@0 must have no duplicates." description)))

(def-error-checker ensure-list-subset
  ((list true-listp "List to check.")
   (super true-listp "List that must include all the elements of @('list')."))
  "Cause an error if any element of a true list
   is not a member of another true list."
  (((subsetp-equal list super)
    "~@0 must have only elements in the list ~x1, but it includes the ~@2."
    description
    super
    (let ((extra (remove-duplicates-equal (set-difference-equal list super))))
      (if (= (len extra) 1)
          (msg "element ~x0" (car extra))
        (msg "elements ~&0" extra))))))

(def-error-checker ensure-doublet-list
  ((x "Value to check."))
  "Cause an error if a value is not a true list of doublets."
  (((doublet-listp x)
    "~@0 must be a true list of doublets."
    description)))

(def-error-checker ensure-keyword-value-list
  ((x "Value to check."))
  "Cause an error if a value if not a true list of even length
   with keywords at its even-numbered positions (counting from 0)."
  (((keyword-value-listp x) "~@0 must a true list of even length ~
                             with keywords at its even-numbered positions ~
                             (counting from 0)." description)))

(def-error-checker ensure-member-of-list
  ((x "Value to check.")
   (list true-listp "List that must include @('x') as member.")
   (list-description msgp "Description of @('list') for the error message."))
  "Cause an error if a value is not a member of a list."
  (((member-equal x list)
    "~@0 must be ~@1." description list-description)))

(def-error-checker ensure-not-member-of-list
  ((x "Value to check.")
   (list true-listp "List that must not include @('x') as member.")
   (list-description msgp "Description of @('list') for the error message."))
  "Cause an error if a value is a member of a list."
  (((not (member-equal x list))
    "~@0 must not be ~@1." description list-description)))

(def-error-checker ensure-symbol-not-keyword
  ((symb symbolp "Symbol to check."))
  "Cause an error if a symbol is a keyword."
  (((not (keywordp symb)) "~@0 must not be a keyword." description)))

(def-error-checker ensure-tuple
  ((x "Value to check.")
   (n natp "Length that @('x') must have."))
  "Cause an error if a value is not a tuple of a given length."
  (((acl2::tuplep n x)
    "~@0 must be a NIL-terminated list of ~x1 elements."
    description n)))

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
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp (booleanp r))
                              (booleanp val))))
  :result (if (booleanp x) x r)
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
  :long
  "<p>
   The symbol must not be in the main Lisp package,
   must not be a keyword,
   and must not be already in use.
   </p>"
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-name
  ((x "Value to check."))
  "Cause an error if a value is not the name of an existing function."
  (((function-namep x (w state))
    "~@0 must be the name of an existing function." description)))

(def-error-checker ensure-function-name-list
  ((x "Value to check."))
  "Cause an error if a value is not
   a true list of names of existing functions."
  (((function-name-listp x (w state))
    "~@0 must be a true list of names of existing functions."
    description)))

(def-error-checker ensure-list-functions
  ((list true-listp "List to check."))
  "Cause an error if a true list
   does not consist of names of existing functions."
  (((and (symbol-listp list)
         (function-symbol-listp list (w state)))
    "~@0 must consist of names of existing functions." description)))

(define ensure-function-name-or-numbered-wildcard
  ((x "Value to check.")
   (description msgp)
   (error-erp "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp (implies erp (equal erp error-erp)))
               (val (and (implies erp (equal val error-val))
                         (implies (and (not erp) error-erp)
                                  (symbolp val))))
               state)
  :verify-guards nil
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
  (b* (((er &) (ensure-symbol$ x description error-erp error-val))
       (name (resolve-numbered-name-wildcard x (w state)))
       ((er &) (ensure-symbol-function$
                name
                (if (eq x name)
                    (msg "~@0, which is the symbol ~x1," description x)
                  (msg "The symbol ~x0, to which ~@1 resolves to,"
                       name (msg-downcase-first description)))
                error-erp
                error-val)))
    (value name))
  ///

  (defsection ensure-function-name-or-numbered-wildcard$
    :parents (ensure-function-name-or-numbered-wildcard)
    :short "Call @(tsee ensure-function-name-or-numbered-wildcard)
            with @('ctx') and @('state') as the last two arguments."
    (defmacro ensure-function-name-or-numbered-wildcard$
        (x description error-erp error-val)
      `(ensure-function-name-or-numbered-wildcard
        ,x ,description ,error-erp ,error-val ctx state))))

(define ensure-function/macro/lambda
  ((x "Value to check.")
   (description msgp)
   (error-erp "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@('nil') or @('error-erp').")
               (val
                "A tuple @('(fn stobjs-in stobjs-out new-description)')
                 consisting of
                 a @(tsee pseudo-termfnp),
                 a @(tsee symbol-listp),
                 a @(tsee symbol-listp), and
                 a @(tsee msgp)
                 if @('erp') is @('nil'),
                 otherwise @('error-val').")
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
           (er-soft+
            ctx
            error-erp
            error-val
            "~@0 must be a function name, a macro name, ~
             or a lambda expression.  ~
             The symbol ~x1 is not the name of a function or macro."
            description x))
          (t (b* (((mv tlambda/msg stobjs-out) (check-user-lambda x wrld))
                  ((when (msgp tlambda/msg))
                   (er-soft+
                    ctx
                    error-erp
                    error-val
                    "~@0 must be a function name, a macro name, ~
                     or a lambda expression.  ~
                     Since ~x1 is not a symbol, ~
                     it must be a lambda expression.  ~
                     ~@2"
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
    (defmacro ensure-function/macro/lambda$ (x description error-erp error-val)
      `(ensure-function/macro/lambda
        ,x ,description ,error-erp ,error-val ctx state))))

(define ensure-term ((x "Value to check.")
                     (description msgp)
                     (error-erp "Flag to return in case of error.")
                     (error-val "Value to return in case of error.")
                     (ctx "Context for errors.")
                     state)
  :returns (mv (erp "@('nil') or @('error-erp').")
               (val
                "A tuple @('(term stobjs-out)')
                 consisting of
                 a @(tsee pseudo-termp) and
                 a @(tsee symbol-listp)
                 if @('erp') is @('nil'),
                 otherwise @('error-val').")
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
        (er-soft+ ctx error-erp error-val
                  "~@0 must be a term.  ~@1"
                  description term/msg)
      (value (list term/msg stobjs-out))))
  ///

  (defsection ensure-term$
    :parents (ensure-term)
    :short "Call @(tsee ensure-term)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-term$)"
    (defmacro ensure-term$ (x description error-erp error-val)
      `(ensure-term ,x ,description ,error-erp ,error-val ctx state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-logic-mode
  ((fn (function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is in program mode."
  (((logicp fn (w state))
    "~@0 must be in logic mode." description)))

(def-error-checker ensure-function-program-mode
  ((fn (function-namep fn (w state)) "Function to check."))
  "Cause an error if a function is in logic mode."
  (((programp fn (w state))
    "~@0 must be in program mode." description)))

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
    description))
  :verify-guards nil)

(def-error-checker ensure-function-not-in-termination-thm
  ((fn (and (logic-function-namep fn (w state))
            (recursivep fn nil (w state)))
       "Function to check."))
  "Cause an error if a recursive function
   occurs in its own termination theorem."
  (((not (member-eq fn (all-ffn-symbs (termination-theorem fn (w state)) nil)))
    "~@0 must not occur in its own termination theorem, which is~%~x1."
    description (termination-theorem fn (w state))))
  :mode :program)

(def-error-checker ensure-function-no-stobjs
  ((fn (and (function-namep fn (w state))
            (not (member-eq fn *stobjs-out-invalid*))) "Function to check."))
  "Cause an error if a function has input or output @(see stobj)s."
  (((no-stobjs-p fn (w state))
    "~@0 must have no input or output stobjs." description))
  :long
  "<p>
   The function must not be one whose @(tsee stobjs-out) are invalid.
   </p>"
  :verify-guards nil)

(def-error-checker ensure-function-arity
  ((fn (function-namep fn (w state)) "Function to check.")
   (n natp "Arity that @('fn') must have."))
  "Cause an error if a function does not have a given arity."
  (((= (arity fn (w state)) n)
    "~@0 must take ~x1 ~@2."
    description n (if (= n 1) "argument" "arguments")))
  :verify-guards nil)

(def-error-checker ensure-function-has-args
  ((fn (function-namep fn (w state)) "Function to check."))
  "Cause an error if a function has no arguments."
  (((/= (arity fn (w state)) 0)
    "~@0 must take at least one argument." description))
  :verify-guards nil)

(def-error-checker ensure-function-number-of-results
  ((fn (and (function-namep fn (w state))
            (not (member-eq fn *stobjs-out-invalid*))) "Function to check.")
   (n posp "Number of results that @('fn') must have."))
  "Cause an error if a function does not have a given number of results."
  (((= (number-of-results fn (w state)) n)
    "~@0 must return ~x1 ~@2."
    description n (if (= n 1) "result" "results")))
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
        (msg "variables ~&0" extra)))))
  :verify-guards nil)

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
        (msg "functions ~&0" fns)))))
  :verify-guards nil)

(def-error-checker ensure-term-guard-verified-exec-fns
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term
   calls any non-guard-verified function for execution."
  (((guard-verified-exec-fnsp term (w state))
    "~@0 must call only guard-verified functions ~
     (except possibly in the :LOGIC subterms of MBEs and via EC-CALL), ~
     but it calls the non-guard-verified ~@1."
    description
    (let ((fns (all-non-gv-exec-ffn-symbs term (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns)))))
  :mode :program)

(def-error-checker ensure-term-does-not-call
  ((term pseudo-termp "Term to check.")
   (fn symbolp "Function that @('term') must not call."))
  "Cause an error if a term calls a given function."
  (((not (ffnnamep fn term)) "~@0 must not call ~x1." description fn)))

(def-error-checker ensure-term-if-call
  ((term pseudo-termp "Term to check."))
  "Cause an error if a term is not a call of @(tsee if)."
  (((and (nvariablep term)
         (not (fquotep term))
         (eq (ffn-symb term) 'if))
    "~@0 must be a call of IF." description))
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp (pseudo-termp term))
                              (and (pseudo-term-listp val)
                                   (equal (len val) 3)))))
  :result (list (fargn term 1) (fargn term 2) (fargn term 3))
  :long
  "<p>
   If the term is a call to @(tsee if),
   return its test, `then' branch, and `else' branch.
   </p>")

(def-error-checker ensure-term-not-call-of
  ((term pseudo-termp "Term to check.")
   (fn symbolp "Function that @('term') must not be a call of."))
  "Cause an error if a term is a call of a given function."
  (((or (variablep term)
        (fquotep term)
        (not (eq (ffn-symb term) fn)))
    "~@0 must not be a call of ~x1." description fn)))

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
        (msg "functions ~&0" fns)))))
  :verify-guards nil)

(def-error-checker ensure-lambda-arity
  ((lambd pseudo-lambdap "Lambda expression to check.")
   (n natp "Arity that @('lambd') must have."))
  "Cause an error if a lambda expression does not have a given arity."
  (((= (arity lambd (w state)) n)
    "~@0 must take ~x1 ~@2."
    description n (if (= n 1) "argument" "arguments")))
  :verify-guards nil)

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
        (msg "functions ~&0" fns)))))
  :verify-guards nil)

(def-error-checker ensure-lambda-guard-verified-exec-fns
  ((lambd pseudo-lambdap "Lambda expression to check."))
  "Cause an error if a lambda expression
   calls any non-guard-verified function for execution."
  (((lambda-guard-verified-exec-fnsp lambd (w state))
    "~@0 must call only guard-verified functions ~
     (except possibly in the :LOGIC subterms of MBEs and via EC-CALL), ~
     but it calls the non-guard-verified ~@1."
    description
    (let ((fns (all-non-gv-exec-ffn-symbs (lambda-body lambd) (w state))))
      (if (= (len fns) 1)
          (msg "function ~x0" (car fns))
        (msg "functions ~&0" fns)))))
  :mode :program)

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
  ((fn/lambda pseudo-termfnp "Function or lambda expression to check.")
   (description msgp)
   (error-erp "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp (implies erp (equal erp error-erp)))
               (val (and (implies erp (equal val error-val))
                         (implies (and (not erp) error-erp) (not val))))
               state)
  :verify-guards nil
  :short "Cause an error if a function or lambda expression is
          a function in program mode or
          a lambda expression that calls some program-mode function."
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-termfnp))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  (if (symbolp fn/lambda)
      (ensure-function-logic-mode$ fn/lambda description error-erp error-val)
    (ensure-lambda-logic-mode$ fn/lambda description error-erp error-val))
  ///

  (defsection ensure-function/lambda-logic-mode$
    :parents (ensure-function/lambda-logic-mode)
    :short "Call @(tsee ensure-function/lambda-logic-mode)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/lambda-logic-mode$)"
    (defmacro ensure-function/lambda-logic-mode$
        (x description error-erp error-val)
      `(ensure-function/lambda-logic-mode
        ,x ,description ,error-erp ,error-val ctx state))))

(define ensure-function/lambda-guard-verified-fns
  ((fn/lambda pseudo-termfnp "Function or lambda expression to check.")
   (description msgp)
   (error-erp "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp (implies erp (equal erp error-erp)))
               (val (and (implies erp (equal val error-val))
                         (implies (and (not erp) error-erp) (not val))))
               state)
  :verify-guards nil
  :short "Cause an error if a function or lambda expression is
          a non-guard-verified function or
          a lambda expression that calls some non-guard-verified function."
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-termfnp))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  (if (symbolp fn/lambda)
      (ensure-function-guard-verified$
       fn/lambda description error-erp error-val)
    (ensure-lambda-guard-verified-fns$
     fn/lambda description error-erp error-val))
  ///

  (defsection ensure-function/lambda-guard-verified-fns$
    :parents (ensure-function/lambda-guard-verified-fns)
    :short "Call @(tsee ensure-function/lambda-guard-verified-fns)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/lambda-guard-verified-fns$)"
    (defmacro ensure-function/lambda-guard-verified-fns$
        (x description error-erp error-val)
      `(ensure-function/lambda-guard-verified-fns
        ,x ,description ,error-erp ,error-val ctx state))))

(define ensure-function/lambda-guard-verified-exec-fns
  ((fn/lambda pseudo-termfnp "Function or lambda expression to check.")
   (description msgp)
   (error-erp "Flag to return in case of error.")
   (error-val "Value to return in case of error.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@('nil') or @('error-erp').")
               (val "@('nil') if @('erp') is @('nil'),
                     otherwise @('error-val').")
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
   (which returns the @(tsee pseudo-termfnp))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  (if (symbolp fn/lambda)
      (ensure-function-guard-verified$
       fn/lambda description error-erp error-val)
    (ensure-lambda-guard-verified-exec-fns$
     fn/lambda description error-erp error-val))
  ///

  (defsection ensure-function/lambda-guard-verified-exec-fns$
    :parents (ensure-function/lambda-guard-verified-exec-fns)
    :short "Call @(tsee ensure-function/lambda-guard-verified-exec-fns)
            with @('ctx') and @('state') as the last two arguments."
    :long "@(def ensure-function/lambda-guard-verified-exec-fns$)"
    (defmacro ensure-function/lambda-guard-verified-exec-fns$
        (x description error-erp error-val)
      `(ensure-function/lambda-guard-verified-exec-fns
        ,x ,description ,error-erp ,error-val ctx state))))

(def-error-checker ensure-function/lambda-closed
  ((fn/lambda pseudo-termfnp "Function or lambda expression to check."))
  "Cause an error if a function or lambda expression is
   a non-closed lambda expression."
  (((or (symbolp fn/lambda) (lambda-closedp fn/lambda))
    "~@0 must be closed." description))
  :long
  "<p>
   This error-checking function is useful
   after calling @(tsee ensure-function/macro/lambda)
   (which returns the @(tsee pseudo-termfnp))
   to handle functions and lambda expressions uniformly.
   The @('description') parameter
   should describe the function or lambda expression.
   </p>"
  :verify-guards nil)

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
