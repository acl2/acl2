; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "pretty-printer" :ttags ((:open-output-channel!)))
(include-book "static-semantics")
(include-book "dynamic-semantics")
(include-book "shallow-embedding")
(include-book "proof-support")
(include-book "table")

(include-book "fty-pseudo-terms")

(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/std/strings/strtok-bang" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/measure-plus" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/std/system/uguard-plus" :dir :system)
(include-book "kestrel/std/system/well-founded-relation-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "std/typed-alists/keyword-symbol-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "tools/trivial-ancestors-check" :dir :system)

(local (include-book "kestrel/std/system/flatten-ands-in-lit" :dir :system))
(local (include-book "kestrel/std/system/w" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

(defrule pseudo-term-list-count-of-pseudo-term-call->args
  (implies (pseudo-term-case term :call)
           (< (pseudo-term-list-count (pseudo-term-call->args term))
              (pseudo-term-count term)))
  :rule-classes :linear)

(defrule pseudo-term-count-of-pseudo-lambda->body
  (implies (and (not (member-eq (pseudo-term-kind term)
                                '(:null :var :quote)))
                (pseudo-lambda-p (pseudo-term-call->fn term)))
           (< (pseudo-term-count
               (pseudo-lambda->body (pseudo-term-call->fn term)))
              (pseudo-term-count term)))
  :expand ((pseudo-term-count term))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

(defun list-lenp-fn (n l)
  (if (zp n)
      `(endp ,l)
    `(and (consp ,l)
          ,(list-lenp-fn (1- n) `(cdr ,l)))))

(defmacro list-lenp (n l)
  (declare (xargs :guard (natp n)))
  `(let ((l ,l)) ,(list-lenp-fn n 'l)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

; (these serve to speed up some proofs in this file)

(defrulel tuplep-of-2-of-list
  (std::tuplep 2 (list x1 x2)))

(defrulel tuplep-of-3-of-list
  (std::tuplep 3 (list x1 x2 x3)))

(defrulel tuplep-of-4-of-list
  (std::tuplep 4 (list x1 x2 x3 x4)))

(defrulel tuplep-of-5-of-list
  (std::tuplep 5 (list x1 x2 x3 x4 x5)))

(defrulel tuplep-of-6-of-list
  (std::tuplep 6 (list x1 x2 x3 x4 x5 x6)))

(local (in-theory (disable std::tuplep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-event-and-code-generation
  :parents (atc-implementation)
  :short "Event generation and code generation performed by @(tsee atc)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate C abstract syntax,
     which we pretty-print to a file
     and also assign to a named constant.")
   (xdoc::p
    "Given the restrictions on the target functions,
     the translation is fairly straightforward -- intentionally so.")
   (xdoc::p
    "Some events are generated in two slightly different variants:
     one that is local to the generated @(tsee encapsulate),
     and one that is exported from the  @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean'';
     some proof hints may refer to events
     that are generated only locally to the @(tsee encapsulate)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-appconds ((fns symbol-listp) (wrld plist-worldp))
  :returns (mv (appconds "A @(tsee evmac-appcond-listp).")
               (fn-appconds "A @(tsee symbol-symbol-alistp)."))
  :mode :program
  :short "Generate the applicability conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return an alist from the recursive target functions
     to the corresponding applicability condition names."))
  (b* (((when (endp fns)) (mv nil nil))
       (fn (car fns))
       ((when (not (irecursivep+ fn wrld)))
        (atc-gen-appconds (cdr fns) wrld))
       (meas (measure+ fn wrld))
       (name (packn-pos (list 'natp-of-measure-of- fn) :keyword))
       (formula (untranslate `(natp ,meas) nil wrld))
       (appcond (make-evmac-appcond :name name :formula formula))
       ((mv appconds fn-appconds) (atc-gen-appconds (cdr fns) wrld)))
    (mv (cons appcond appconds)
        (acons fn name fn-appconds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-symbol-type-alist
  :short "Fixtype of  alists from symbols to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent scopes in the symbol tables for variables."))
  :key-type symbol
  :val-type type
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred atc-symbol-type-alistp
  ///

  (defrule typep-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-type-alistp x)
                  (assoc-equal k x))
             (typep (cdr (assoc-equal k x)))))

  (defruled symbol-listp-of-strip-cars-when-atc-symbol-type-alistp
    (implies (atc-symbol-type-alistp x)
             (symbol-listp (strip-cars x))))

  (defruled symbol-alistp-when-atc-symbol-type-alistp
    (implies (atc-symbol-type-alistp x)
             (symbol-alistp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atc-symbol-type-alist-list
  :short "Fixtype of lists of alists from symbols to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent symbol tables for variables.
     The @(tsee car) is the innermost scope."))
  :elt-type atc-symbol-type-alist
  :true-listp t
  :elementp-of-nil t
  :pred atc-symbol-type-alist-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-var ((var symbolp) (inscope atc-symbol-type-alist-listp))
  :returns (type? type-optionp)
  :short "Obtain the type of a variable from the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look through the scopes, from innermost to outermost.
     Actually, currently it is an invariant that the scopes are disjoint,
     so any lookup order would give the same result.")
   (xdoc::p
    "Return @('nil') if the variable is not in scope."))
  (if (endp inscope)
      nil
    (or (cdr (assoc-eq var (atc-symbol-type-alist-fix (car inscope))))
        (atc-get-var var (cdr inscope)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-vars ((vars symbol-listp) (inscope atc-symbol-type-alist-listp))
  :returns (type?-list type-option-listp)
  :short "Lift @(tsee atc-get-var) to lists."
  (cond ((endp vars) nil)
        (t (cons (atc-get-var (car vars) inscope)
                 (atc-get-vars (cdr vars) inscope)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-var-check-innermost ((var symbolp)
                                     (inscope atc-symbol-type-alist-listp))
  :returns (mv (type? type-optionp)
               (innermostp booleanp))
  :short "Obtain the type of a variable from the symbol table,
          and indicate whether the variable is in the innermost scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to define @(tsee atc-get-vars-check-innermost).
     See that function's documentation for motivation."))
  (atc-get-var-check-innermost-aux var inscope t)

  :prepwork
  ((define atc-get-var-check-innermost-aux
     ((var symbolp)
      (inscope atc-symbol-type-alist-listp)
      (innermostp booleanp))
     :returns (mv (type? type-optionp)
                  (innermostp booleanp :hyp (booleanp innermostp)))
     :parents nil
     (b* (((when (endp inscope)) (mv nil nil))
          (scope (atc-symbol-type-alist-fix (car inscope)))
          (type? (cdr (assoc-eq var scope)))
          ((when type?) (mv type? innermostp)))
       (atc-get-var-check-innermost-aux var (cdr inscope) nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-vars-check-innermost ((vars symbol-listp)
                                      (inscope atc-symbol-type-alist-listp))
  :returns (mv (type?-list type-option-listp)
               (innermostp-list boolean-listp))
  :short "Lift @(tsee atc-get-var-check-innermost) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when we encounter a @(tsee mv-let) in code generation.
     We need to ensure that all the variables are in scope,
     and we need to know which ones are in the innermost scope.
     This function returns that information."))
  (b* (((when (endp vars)) (mv nil nil))
       ((mv type? innermostp)
        (atc-get-var-check-innermost (car vars) inscope))
       ((mv type?-list innermostp-list)
        (atc-get-vars-check-innermost (cdr vars) inscope)))
    (mv (cons type? type?-list)
        (cons innermostp innermostp-list)))
  ///

  (defret len-of-atc-get-vars-check-innermost.type?-list
    (equal (len type?-list)
           (len vars)))

  (defret len-of-atc-get-vars-check-innermost.innermostp-list
    (equal (len innermostp-list)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-add-var ((var symbolp)
                     (type typep)
                     (inscope atc-symbol-type-alist-listp))
  :returns (new-inscope atc-symbol-type-alist-listp)
  :short "Add a variable with a type to the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is added to the innermost scope.
     The symbol table has always at least one scope.")
   (xdoc::p
    "This is always called after checking that
     the variable is not already in scope.
     So it unconditionally adds the variable without checking first."))
  (cons (acons (symbol-fix var)
               (type-fix type)
               (atc-symbol-type-alist-fix (car inscope)))
        (atc-symbol-type-alist-list-fix (cdr inscope))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-var ((var symbolp) (inscope atc-symbol-type-alist-listp))
  :returns (mv (type? type-optionp)
               (innermostp booleanp)
               (errorp booleanp))
  :short "Check a variable against a symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when we encounter a @(tsee let) in code generation.
     We need to decide how to treat the @(tsee let)
     based on whether the variable is new or not,
     and whether if not new it is in the innermost scope or not,
     and whether if new there is a different variable with the same symbol name.
     This function checks all of these conditions.")
   (xdoc::p
    "If the variable is in the symbol table, we return its type,
     along with a flag indicating whether
     the variable is in the innermost scope.
     If the symbol table contains
     a different variable with the same symbol name,
     we return an indication of error;
     this is because ACL2 variables represent C variables
     whose names are just the symbol names of the ACL2 variables,
     which therefore must be distinct for different ACL2 variables.")
   (xdoc::p
    "It is an invariant that
     all the variables in the symbol table have distinct symbol names."))
  (atc-check-var-aux var inscope t)

  :prepwork
  ((define atc-check-var-aux ((var symbolp)
                              (inscope atc-symbol-type-alist-listp)
                              (innermostp booleanp))
     :returns (mv (type? type-optionp)
                  (innermostp booleanp :hyp (booleanp innermostp))
                  (errorp booleanp))
     :parents nil
     (b* (((when (endp inscope)) (mv nil nil nil))
          (scope (car inscope))
          (type? (cdr (assoc-eq var (atc-symbol-type-alist-fix scope))))
          ((when type?) (mv type? innermostp nil))
          ((when (member-equal (symbol-name var)
                               (symbol-name-lst (strip-cars scope))))
           (mv nil nil t)))
       (atc-check-var-aux var (cdr inscope) nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atc-fn-info
  :short "Fixtype of
          information associated to an ACL2 function translated to C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of:
     an optional C type that is present,
     and represents the function's output type,
     when the function is not recursive;
     a list of C types representing the function's input types;
     an optional (loop) statement that is present,
     and is represented by the function,
     when the function is recursive;
     a list of variables affected by the function;
     the name of the locally generated theorem that asserts
     that the function (one or more) results have certain C types;
     the name of the locally generated theorem that asserts
     that the execution of the function is functionally correct;
     the name of the locally generated theorem that asserts
     that the measure of the function (when recursive) yields a natural number
     (@('nil') if the function is not recursive);
     the name of the locally generated theorem that asserts
     that looking up the function in the function environment
     yields the information for the function
     (@('nil') if the function is recursive);
     and a limit that suffices to execute the code generated from the function,
     as explained below.
     The limit is a term that may depend on the function's parameters.
     For a non-recursive function,
     the term expresses a limit that suffices to execute @(tsee exec-fun)
     on the C function generated from the ACL2 function
     when the arguments of the C functions have values
     symbolically expressed by the ACL2 function's formal parameters.
     For a recursive function,
     the term expressed a limit that suffices to execute @(tsee exec-stmt-while)
     on the C loop generated from the ACL2 function
     when the variables read by the C loop have values
     symbolically expressed by the ACL2 function's formal parameters.
     If none of the target ACL2 functions are recursive,
     all the limit terms are quoted constants;
     if there are recursive functions,
     then those, and all their direct and indirect callers,
     have limit terms that in general depend on each function's parameters.
     All these limit terms are calculated
     when the C code is generated from the ACL2 functions.")
   (xdoc::p
    "Note that exactly one of the first two fields is @('nil').
     This is an invariant."))
  ((out-type type-option)
   (in-types type-list)
   (loop? stmt-option)
   (affect symbol-list)
   (result-thm symbol)
   (correct-thm symbol)
   (measure-nat-thm symbol)
   (fun-env-thm symbol)
   (limit pseudo-term))
  :pred atc-fn-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-symbol-fninfo-alist
  :short "Fixtype of alists from symbols to function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent symbol tables for functions."))
  :key-type symbolp
  :val-type atc-fn-info
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred atc-symbol-fninfo-alistp
  ///

  (defrule atc-fn-infop-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-fninfo-alistp x)
                  (assoc-equal k x))
             (atc-fn-infop (cdr (assoc-equal k x)))))

  (defruled symbol-listp-of-strip-cars-when-atc-symbol-fninfo-alistp
    (implies (atc-symbol-fninfo-alistp prec-fns)
             (symbol-listp (strip-cars prec-fns)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-result-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the result theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of each of these theorems for a function @('fn')
     makes use of the same theorems for
     some of the preceding functions in @('prec-fns'),
     more precisely the ones called in the body of @('fn').
     This function serves to collect those theorem names from the alist.
     The list of symbols given as input consists of
     the functions called by @('fn'):
     it is fine if the list contains functions that are not keys of the alist,
     as it is merely used to filter.")
   (xdoc::p
    "The alist has no duplicate keys.
     So this function is correct."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (cons (atc-fn-info->result-thm (cdr (car prec-fns)))
               (atc-symbol-fninfo-alist-to-result-thms (cdr prec-fns) among)))
        (t (atc-symbol-fninfo-alist-to-result-thms (cdr prec-fns) among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-correct-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the execution correctness theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-symbol-fninfo-alist-to-result-thms).
     See that function's documentation for more details."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (cons (atc-fn-info->correct-thm (cdr (car prec-fns)))
               (atc-symbol-fninfo-alist-to-correct-thms (cdr prec-fns)
                                                        among)))
        (t (atc-symbol-fninfo-alist-to-correct-thms (cdr prec-fns)
                                                    among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-measure-nat-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the measure theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-symbol-fninfo-alist-to-result-thms).
     See that function's documentation for more details.")
   (xdoc::p
    "We skip over non-recursive functions,
     which have @('nil') as that entry."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (b* ((thm (atc-fn-info->measure-nat-thm (cdr (car prec-fns)))))
           (if thm
               (cons thm
                     (atc-symbol-fninfo-alist-to-measure-nat-thms (cdr prec-fns)
                                                                  among))
             (atc-symbol-fninfo-alist-to-measure-nat-thms (cdr prec-fns)
                                                          among))))
        (t (atc-symbol-fninfo-alist-to-measure-nat-thms (cdr prec-fns)
                                                        among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-fun-env-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the function envirionment theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-symbol-fninfo-alist-to-result-thms).
     See that function's documentation for more details.")
   (xdoc::p
    "We skip over recursive functions,
     which have @('nil') as that entry."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (b* ((thm (atc-fn-info->fun-env-thm (cdr (car prec-fns)))))
           (if thm
               (cons thm
                     (atc-symbol-fninfo-alist-to-fun-env-thms (cdr prec-fns)
                                                              among))
             (atc-symbol-fninfo-alist-to-fun-env-thms (cdr prec-fns)
                                                      among))))
        (t (atc-symbol-fninfo-alist-to-fun-env-thms (cdr prec-fns)
                                                    among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-2part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp))
  :short "Check if a symbol consists of two parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>'),
     with @('<part1>') and @('<part2>') non-empty and without dashes,
     we return an indication of success and the two parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The two returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 2)) (mv nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym)))
    (mv t part1 part2))
  :prepwork
  ((local (include-book "std/typed-lists/string-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-3part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp)
               (part3 symbolp))
  :short "Check if a symbol consists of three parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>-<part3>'),
     with @('<part1>') and @('<part2>') and @('<part3>')
     non-empty and without dashes,
     we return an indication of success and the three parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The three returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 3)) (mv nil nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym))
       (part3 (intern-in-package-of-symbol (third parts) sym)))
    (mv t part1 part2 part3))
  :prepwork
  ((local (include-book "std/typed-lists/string-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-4part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp)
               (part3 symbolp)
               (part4 symbolp))
  :short "Check if a symbol consists of four parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>-<part3>-<part4>'),
     with @('<part1>') and @('<part2>') and @('<part3>') and @('<part4>')
     non-empty and without dashes,
     we return an indication of success and the four parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The four returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 4)) (mv nil nil nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym))
       (part3 (intern-in-package-of-symbol (third parts) sym))
       (part4 (intern-in-package-of-symbol (fourth parts) sym)))
    (mv t part1 part2 part3 part4))
  :prepwork
  ((local (include-book "std/typed-lists/string-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-integer-fixtype-to-type ((fixtype symbolp))
  :returns (type type-optionp)
  :short "Integer type corresponding to a fixtype name, if any."
  (case fixtype
    (schar (type-schar))
    (uchar (type-uchar))
    (sshort (type-sshort))
    (ushort (type-ushort))
    (sint (type-sint))
    (uint (type-uint))
    (slong (type-slong))
    (ulong (type-ulong))
    (sllong (type-sllong))
    (ullong (type-ullong))
    (t nil))
  ///

  (defret type-integerp-of-atc-integer-fixtype-to-type
    (implies type
             (type-integerp type)))

  (defret type-arithmeticp-of-atc-integer-fixtype-to-type
    (implies type
             (type-arithmeticp type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-iconst ((term pseudo-termp) (ctx ctxp) state)
  :returns (mv erp
               (val (tuple (yes/no booleanp)
                           (const iconstp)
                           (out-type typep)
                           val))
               state)
  :short "Check if a term represents an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of a function @('<type>-<base>-const')
     on a quoted integer constant,
     we return the C integer constant represented by this call.
     We also return the C integer type of the constant."))
  (b* (((acl2::fun (no)) (list nil (irr-iconst) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (acl2::value (no)))
       ((pseudo-term-fncall term) term)
       ((mv okp type base const) (atc-check-symbol-3part term.fn))
       ((unless (and okp
                     (member-eq type '(sint uint slong ulong sllong ullong))
                     (member-eq base '(dec oct hex))
                     (eq const 'const)))
        (acl2::value (no)))
       ((unless (list-lenp 1 term.args))
        (raise "Internal error: ~x0 not applied to 1 argument." term)
        (acl2::value (no)))
       (arg (first term.args))
       ((unless (pseudo-term-case arg :quote))
        (er-soft+ ctx t (no)
                  "The function ~x0 must be applied to a quoted constant, ~
                   but it is applied to ~x1 instead."
                  term.fn arg))
       (val (pseudo-term-quote->val arg))
       ((unless (natp val))
        (er-soft+ ctx t (no)
                  "The function ~x0 ~
                   must be applied to a quoted natural number, ~
                   but it is applied to ~x1 instead. ~
                   Since this is required by the guard of ~x0, ~
                   this call is unreachable under the guard."
                  term.fn val))
       (inrangep (case type
                   (sint (sint-integerp val))
                   (uint (uint-integerp val))
                   (slong (slong-integerp val))
                   (ulong (ulong-integerp val))
                   (sllong (sllong-integerp val))
                   (ullong (ullong-integerp val))
                   (t (impossible))))
       ((unless inrangep)
        (er-soft+ ctx t (no)
                  "The function ~x0
                   must be applied to a quoted natural number ~
                   representable in the C type corresponding to ~x1, ~
                   but it is applied to ~x2 instead."
                  term.fn type val))
       (base (case base
               (dec (iconst-base-dec))
               (oct (iconst-base-oct))
               (hex (iconst-base-hex))
               (t (impossible))))
       ((mv const type)
        (case type
          (sint (mv (make-iconst :value val
                                 :base base
                                 :unsignedp nil
                                 :type (iconst-tysuffix-none))
                    (type-sint)))
          (uint (mv (make-iconst :value val
                                 :base base
                                 :unsignedp t
                                 :type (iconst-tysuffix-none))
                    (type-uint)))
          (slong (mv (make-iconst :value val
                                  :base base
                                  :unsignedp nil
                                  :type (iconst-tysuffix-long))
                     (type-slong)))
          (ulong (mv (make-iconst :value val
                                  :base base
                                  :unsignedp t
                                  :type (iconst-tysuffix-long))
                     (type-ulong)))
          (sllong (mv (make-iconst :value val
                                   :base base
                                   :unsignedp nil
                                   :type (iconst-tysuffix-llong))
                      (type-sllong)))
          (ullong (mv (make-iconst :value val
                                   :base base
                                   :unsignedp t
                                   :type (iconst-tysuffix-llong))
                      (type-ullong)))
          (t (mv (impossible) (impossible))))))
    (acl2::value (list t const type)))
  ///
  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name typeset-of-atc-check-iconst
        :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-unop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op unopp)
               (arg pseudo-termp)
               (in-type typep)
               (out-type typep))
  :short "Check if a term may represent a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C unary operators,
     we return the operator and the argument term.")
   (xdoc::p
    "We also return the input and output C types of the operator.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (b* (((acl2::fun (no)) (mv nil (irr-unop) nil (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp op fixtype) (atc-check-symbol-2part term.fn))
       ((when (not okp)) (no))
       (in-type (atc-integer-fixtype-to-type fixtype))
       ((when (not in-type)) (no))
       ((unless (list-lenp 1 term.args)) (no))
       (arg (first term.args)))
    (case op
      (plus (mv t (unop-plus) arg in-type (promote-type in-type)))
      (minus (mv t (unop-minus) arg in-type (promote-type in-type)))
      (bitnot (mv t (unop-bitnot) arg in-type (promote-type in-type)))
      (lognot (mv t (unop-lognot) arg in-type (type-sint)))
      (t (no))))
  ///

  (defret pseudo-term-count-of-atc-check-unop-arg
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-binop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op binopp)
               (arg1 pseudo-termp)
               (arg2 pseudo-termp)
               (in-type1 typep)
               (in-type2 typep)
               (out-type typep))
  :short "Check if a term may represent a strict pure binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C strict pure binary operators,
     we return the operator and the argument terms.")
   (xdoc::p
    "We also return the input and output C types of the operator.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure."))
  (b* (((acl2::fun (no))
        (mv nil (irr-binop) nil nil (irr-type) (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp op fixtype1 fixtype2) (atc-check-symbol-3part term.fn))
       ((when (not okp)) (no))
       (in-type1 (atc-integer-fixtype-to-type fixtype1))
       ((when (not in-type1)) (no))
       (in-type2 (atc-integer-fixtype-to-type fixtype2))
       ((when (not in-type2)) (no))
       ((unless (list-lenp 2 term.args)) (no))
       (arg1 (first term.args))
       (arg2 (second term.args)))
    (case op
      (add (mv t (binop-add) arg1 arg2
               in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (sub (mv t (binop-sub) arg1 arg2
               in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (mul (mv t (binop-mul) arg1 arg2
               in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (div (mv t (binop-div) arg1 arg2
               in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (rem (mv t (binop-rem) arg1 arg2
               in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (shl (mv t (binop-shl) arg1 arg2
               in-type1 in-type2 (promote-type in-type1)))
      (shr (mv t (binop-shr) arg1 arg2
               in-type1 in-type2 (promote-type in-type1)))
      (lt (mv t (binop-lt) arg1 arg2 in-type1 in-type2 (type-sint)))
      (le (mv t (binop-le) arg1 arg2 in-type1 in-type2 (type-sint)))
      (gt (mv t (binop-gt) arg1 arg2 in-type1 in-type2 (type-sint)))
      (ge (mv t (binop-ge) arg1 arg2 in-type1 in-type2 (type-sint)))
      (eq (mv t (binop-eq) arg1 arg2 in-type1 in-type2 (type-sint)))
      (ne (mv t (binop-ne) arg1 arg2 in-type1 in-type2 (type-sint)))
      (bitand (mv t (binop-bitand) arg1 arg2
                  in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (bitxor (mv t (binop-bitxor) arg1 arg2
                  in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (bitior (mv t (binop-bitior) arg1 arg2
                  in-type1 in-type2 (uaconvert-types in-type1 in-type2)))
      (t (no))))
  ///

  (defret pseudo-term-count-of-atc-check-binop-arg1
    (implies yes/no
             (< (pseudo-term-count arg1)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-binop-arg2
    (implies yes/no
             (< (pseudo-term-count arg2)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-conv ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (tyname tynamep)
               (arg pseudo-termp)
               (in-type typep)
               (out-type typep))
  :short "Check if a term may represent a conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represents C integer conversions,
     we return the C type name for the destination type
     and the argument term.")
   (xdoc::p
    "We also return the input and output C types of the conversion.
     The output type is redundant,
     because it can be determined from the returned type name.
     But we return it for uniformity and simplicity.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((acl2::fun (no)) (mv nil (irr-tyname) nil (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp dtype from stype) (atc-check-symbol-3part term.fn))
       ((unless (and okp
                     (eq from 'from)))
        (no))
       (in-type (atc-integer-fixtype-to-type stype))
       ((when (not in-type)) (no))
       (out-type (atc-integer-fixtype-to-type dtype))
       ((when (not out-type)) (no))
       ((unless (list-lenp 1 term.args)) (no))
       (arg (first term.args))
       (tyname (integer-type-to-type-name out-type)))
    (mv t tyname arg in-type out-type))
  ///

  (defret pseudo-term-count-of-atc-check-conv-arg
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-array-read ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arr pseudo-termp)
               (sub pseudo-termp)
               (in-type1 typep)
               (in-type2 typep)
               (out-type typep))
  :short "Check if a term may represent an array read."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C array read operations,
     we return the two argument terms.")
   (xdoc::p
    "We also return the input and output C types of the array read.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((acl2::fun (no)) (mv nil nil nil (irr-type) (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp etype array read itype) (atc-check-symbol-4part term.fn))
       ((unless (and okp
                     (eq array 'array)
                     (eq read 'read)))
        (no))
       (out-type (atc-integer-fixtype-to-type etype))
       ((when (not out-type)) (no))
       (in-type1 (type-pointer out-type))
       (in-type2 (atc-integer-fixtype-to-type itype))
       ((when (not in-type2)) (no))
       ((unless (list-lenp 2 term.args)) (no))
       (arr (first term.args))
       (sub (second term.args)))
    (mv t arr sub in-type1 in-type2 out-type))
  ///

  (defret pseudo-term-count-of-atc-check-array-read-arr
    (implies yes/no
             (< (pseudo-term-count arr)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-array-read-sub
    (implies yes/no
             (< (pseudo-term-count sub)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-from-boolean ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp))
  :short "Check if a term may represent a conversion
          from an ACL2 boolean to a C @('int') value."
  (b* (((acl2::fun (no)) (mv nil nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless (and okp
                     (eq fn 'c::sint-from-boolean)
                     (list-lenp 1 args)))
        (no)))
    (mv t (first args)))
  ///

  (defret pseudo-term-count-of-atc-check-sint-from-boolean
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-condexpr ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (test pseudo-termp)
               (then pseudo-termp)
               (else pseudo-termp))
  :short "Check if a term may represent a C conditional expression."
  (b* (((acl2::fun (no)) (mv nil nil nil nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless (and okp
                     (eq fn 'c::condexpr)
                     (list-lenp 1 args)))
        (no)))
    (fty-check-if-call (first args)))
  ///

  (defret pseudo-term-count-of-atc-check-condexpr.test
    (implies yes/no
             (< (pseudo-term-count test)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-condexpr.then
    (implies yes/no
             (< (pseudo-term-count then)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-condexpr.else
    (implies yes/no
             (< (pseudo-term-count else)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-boolean-from-type ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp)
               (in-type typep))
  :short "Check if a term may represent a conversion
          from a C integer value to an ACL2 boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return the input C type of the conversion.
     The output type is known (boolean), and it is in fact an ACL2 type."))
  (b* (((acl2::fun (no)) (mv nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp boolean from type) (atc-check-symbol-3part fn))
       ((unless (and okp
                     (eq boolean 'boolean)
                     (eq from 'from)))
        (no))
       (in-type (atc-integer-fixtype-to-type type))
       ((when (not in-type)) (no))
       ((unless (list-lenp 1 args)) (no)))
    (mv t (first args) in-type))
  ///

  (defret pseudo-term-count-of-atc-check-boolean-from-type
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-cfun-call ((term pseudo-termp)
                             (var-term-alist symbol-pseudoterm-alistp)
                             (prec-fns atc-symbol-fninfo-alistp)
                             (wrld plist-worldp))
  :returns (mv (yes/no booleanp)
               (fn symbolp)
               (args pseudo-term-listp)
               (in-types type-listp)
               (out-type typep)
               (affect symbol-listp)
               (limit pseudo-termp))
  :short "Check if a term may represent a call to a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, we return
     the called function along with the arguments.
     We also return the input and output types of the function,
     the variables affected by the function,
     and the limit sufficient to execute the function.")
   (xdoc::p
    "The limit retrieved from the function table
     refers to the formal parameters.
     We must instantiate it to the actual parameters
     in order to obtain an appropriate limit for the call,
     but we also need to substitute all the bindings
     in order to obtain the real arguments of the call
     from the point of view of the top level of
     where this call term occurs.")
   (xdoc::p
    "This is used on expression terms returning C values,
     so the called function must be non-recursive,
     i.e. it must represent a C function, not a C loop."))
  (b* (((acl2::fun (no)) (mv nil nil nil nil (irr-type) nil nil))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((when (irecursivep+ term.fn wrld)) (no))
       (fn+info (assoc-eq term.fn (atc-symbol-fninfo-alist-fix prec-fns)))
       ((unless (consp fn+info)) (no))
       (info (cdr fn+info))
       (in-types (atc-fn-info->in-types info))
       (out-type (atc-fn-info->out-type info))
       (affect (atc-fn-info->affect info))
       ((when (null out-type)) (no))
       (limit (atc-fn-info->limit info))
       (limit (fty-fsublis-var var-term-alist limit)))
    (mv t term.fn term.args in-types out-type affect limit))
  ///

  (defret pseudo-term-count-of-atc-check-cfun-call-args
    (implies yes/no
             (< (pseudo-term-list-count args)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-loop-call ((term pseudo-termp)
                             (var-term-alist symbol-pseudoterm-alistp)
                             (prec-fns atc-symbol-fninfo-alistp))
  :returns (mv (yes/no booleanp)
               (fn symbolp)
               (args pseudo-term-listp)
               (in-types type-listp)
               (affect symbol-listp)
               (loop stmtp)
               (limit pseudo-termp))
  :short "Check if a term may represent a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether this is a call of
     a function that has been previously processed
     (i.e. it is in the @('prec-fns') alist)
     and is recursive
     (indicated by the presence of the loop statement in its information).
     If the checks succeed, we return
     the function symbol,
     its arguments,
     the variables affected by the loop,
     the associated loop statement,
     and the limit sufficient to execute the function call.")
   (xdoc::p
    "The limit retrieved from the function table
     refers to the formal parameters.
     We must instantiate it to the actual parameters
     in order to obtain an appropriate limit for the call,
     but we also need to substitute all the bindings
     in order to obtain the real arguments of the call
     from the point of view of the top level of
     where this call term occurs."))
  (b* (((acl2::fun (no)) (mv nil nil nil nil nil (irr-stmt) nil))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       (fn+info (assoc-eq term.fn (atc-symbol-fninfo-alist-fix prec-fns)))
       ((unless (consp fn+info)) (no))
       (info (cdr fn+info))
       (loop (atc-fn-info->loop? info))
       ((unless (stmtp loop)) (no))
       (in-types (atc-fn-info->in-types info))
       (affect (atc-fn-info->affect info))
       (limit (atc-fn-info->limit info))
       (limit (fty-fsublis-var var-term-alist limit)))
    (mv t term.fn term.args in-types affect loop limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-array-write ((var symbolp) (val pseudo-termp))
  :returns (mv (yes/no booleanp)
               (sub pseudo-termp)
               (elem pseudo-termp)
               (sub-type typep)
               (elem-type typep))
  :short "Check if a @(tsee let) binding may represent an array write."
  :long
  (xdoc::topstring
   (xdoc::p
    "An array write, i.e. an assignment to an array element,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<arr> (<type1>-array-write-<type2> <arr> <sub> <elem>))) ...)")
   (xdoc::p
    "where @('<arr>') is a variable of pointer type,
     which must occur identically as
     both the @(tsee let) variable
     and as the first argument of @('<type1>-array-write-<type2>'),
     @('<sub>') is an expression that yields the index of the element to write,
     @('<elem>') is an expression that yields the element to write,
     and @('...') represents the code that follows the array assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the components are returned for further processing.
     We also return the types of the index and element
     as gathered from the name of the array write function."))
  (b* (((acl2::fun (no)) (mv nil nil nil (irr-type) (irr-type)))
       ((unless (pseudo-term-case val :fncall)) (no))
       ((pseudo-term-fncall val) val)
       ((mv okp etype array write itype) (atc-check-symbol-4part val.fn))
       ((unless (and okp
                     (eq array 'array)
                     (eq write 'write)))
        (no))
       (sub-type (atc-integer-fixtype-to-type itype))
       ((unless sub-type) (no))
       (elem-type (atc-integer-fixtype-to-type etype))
       ((when (not elem-type)) (no))
       ((unless (list-lenp 3 val.args)) (no))
       (arr (first val.args))
       (sub (second val.args))
       (elem (third val.args)))
    (if (eq arr var)
        (mv t sub elem sub-type elem-type)
      (no)))
  ///

  (defret pseudo-term-count-of-atc-check-array-write-sub
    (implies yes/no
             (< (pseudo-term-count sub)
                (pseudo-term-count val)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-array-write-elem
    (implies yes/no
             (< (pseudo-term-count elem)
                (pseudo-term-count val)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-let ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (var symbolp)
               (val pseudo-termp)
               (body pseudo-termp)
               (wrapper? symbolp))
  :short "Check if a term may represent
          a local variable declaration
          or a local variable assignment
          or a code affecting a single variable,
          followed by more code."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we recognize and decompose statement terms that are @(tsee let)s.
     In translated form, @('(let ((var val)) body)')
     is @('((lambda (var) body) val)').
     However, if @('rest') has other free variables in addition to @('var'),
     those appear as both formal parameters and actual arguments, e.g.
     @('((lambda (var x y) rest<var,x,y>) val x y)'):
     this is because ACL2 translated terms have all closed lambda expressions,
     so ACL2 adds formal parameters and actual arguments to make that happen.
     Here, we must remove them in order to get the ``true'' @(tsee let).
     This is done via a system utility.")
   (xdoc::p
    "We also return the @(tsee declar) or @(tsee assign) wrapper,
     if present; @('nil') if absent."))
  (b* (((acl2::fun (no)) (mv nil nil nil nil nil))
       ((mv okp formals body actuals) (fty-check-lambda-call term))
       ((when (not okp)) (no))
       ((mv formals actuals) (fty-remove-equal-formals-actuals formals actuals))
       ((unless (and (list-lenp 1 formals) (list-lenp 1 actuals))) (no))
       (var (first formals))
       (possibly-wrapped-val (first actuals))
       ((unless (pseudo-term-case possibly-wrapped-val :fncall))
        (mv t var possibly-wrapped-val body nil))
       ((pseudo-term-fncall possibly-wrapped-val) possibly-wrapped-val)
       ((unless (member-eq possibly-wrapped-val.fn '(declar assign)))
        (mv t var possibly-wrapped-val body nil))
       ((unless (list-lenp 1 possibly-wrapped-val.args)) (no)))
    (mv t var (first possibly-wrapped-val.args) body possibly-wrapped-val.fn))
  :guard-hints
  (("Goal" :in-theory (enable len-of-fty-check-lambda-calls.formals-is-args)))
  ///

  (defret pseudo-term-count-of-atc-check-let-val
    (implies yes/no
             (< (pseudo-term-count val)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-let-body
    (implies yes/no
             (< (pseudo-term-count body)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-let
    (implies yes/no
             (< (+ (pseudo-term-count val)
                   (pseudo-term-count body))
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-pure
  :short "Mutually recursive ACL2 functions to
          generate pure C expressions from ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for pure expression terms returning C values
     and for expression terms returning booleans (which are always pure)."))

  (define atc-gen-expr-cval-pure ((term pseudo-termp)
                                  (inscope atc-symbol-type-alist-listp)
                                  (fn symbolp)
                                  (ctx ctxp)
                                  state)
    :returns (mv erp
                 (val (tuple (expr exprp)
                             (type typep)
                             val))
                 state)
    :parents (atc-event-and-code-generation atc-gen-expr-pure)
    :short "Generate a C expression from an ACL2 term
            that must be a pure expression term returning a C value."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time,
       we check that the term is a pure expression term returning a C value,
       as described in the user documentation.")
     (xdoc::p
      "We also return the C type of the expression.")
     (xdoc::p
      "An ACL2 variable is translated to a C variable.
       Its type is looked up in the symbol table passed as input.")
     (xdoc::p
      "If the term fits the pattern of an integer constant
       we translate it to a C integer constant.")
     (xdoc::p
      "If the term fits the pattern of a unary or binary operation,
       we translate it to the application of the operator
       to the recursively generated expressions.
       The type is the result type of the operator.")
     (xdoc::p
      "If the term fits the pattern of a conversion,
       we translate it to a cast of
       the recursively generated subexpression.
       The type is the one of the cast.
       (Future versions of ATC will avoid the cast
       when the conversion happens automatically in C.)")
     (xdoc::p
      "If the terms fits the pattern of an array read,
       we translate it to an array subscripting expression
       on the recursively generated expressions.
       The type is the array's element type.")
     (xdoc::p
      "If the term is a call of @(tsee c::sint-from-boolean),
       we call the mutually recursive ACL2 function
       that translates the argument
       (which must be an expression term returning a boolean)
       to an expression, which we return.
       The type of this expression is always @('int').")
     (xdoc::p
      "If the term is an @(tsee if) call,
       we call the mutually recursive ACL2 function on the test,
       we call this ACL2 function on the branches,
       and we construct a conditional expression.
       We ensure that the two branches have the same type.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not a pure expression term returning a C value.
       We could extend this code to provide
       more information to the user at some point.")
     (xdoc::p
      "As we generate the code, we ensure that the ACL2 terms
       are well-typed according to the C types.
       This is subsumed by guard verification for all the code,
       except for any code that is dead (i.e. unreachable) under the guard:
       the dead code passes guard verification
       (under a hypothesis of @('nil'), i.e. false, essentially),
       but the resulting C code may not compile.
       The additional type checking we do here should ensure that
       all the code satisfies the C static semantics."))
    (b* (((acl2::fun (irr)) (list (irr-expr) (irr-type)))
         ((when (pseudo-term-case term :var))
          (b* ((var (pseudo-term-var->name term))
               (type (atc-get-var var inscope))
               ((when (not type))
                (raise "Internal error: the variable ~x0 in function ~x1 ~
                        has no associated type." var fn)
                (acl2::value (irr))))
            (acl2::value
             (list (expr-ident (make-ident :name (symbol-name var)))
                   (type-fix type)))))
         ((mv erp (list okp const out-type) state)
          (atc-check-iconst term ctx state))
         ((when erp) (mv erp (irr) state))
         ((when okp)
          (acl2::value
           (list (expr-const (const-int const))
                 out-type)))
         ((mv okp op arg in-type out-type) (atc-check-unop term))
         ((when okp)
          (b* (((er (list arg-expr type)) (atc-gen-expr-cval-pure arg
                                                                  inscope
                                                                  fn
                                                                  ctx
                                                                  state))
               ((unless (equal type in-type))
                (er-soft+ ctx t (irr)
                          "The unary operator ~x0 ~
                           is applied to a term ~x1 returning ~x2, ~
                           but a ~x3 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          op arg type in-type)))
            (acl2::value (list (make-expr-unary :op op
                                                :arg arg-expr)
                               out-type))))
         ((mv okp op arg1 arg2 in-type1 in-type2 out-type)
          (atc-check-binop term))
         ((when okp)
          (b* (((er (list arg1-expr type1)) (atc-gen-expr-cval-pure arg1
                                                                    inscope
                                                                    fn
                                                                    ctx
                                                                    state))
               ((er (list arg2-expr type2)) (atc-gen-expr-cval-pure arg2
                                                                    inscope
                                                                    fn
                                                                    ctx
                                                                    state))
               ((unless (and (equal type1 in-type1)
                             (equal type2 in-type2)))
                (er-soft+ ctx t (irr)
                          "The binary operator ~x0 ~
                           is applied to a term ~x1 returning ~x2
                           and to a term ~x3 returning ~x4,
                           but a ~x5 and a ~x6 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          op arg1 type1 arg2 type2 in-type1 in-type2)))
            (acl2::value (list (make-expr-binary :op op
                                                 :arg1 arg1-expr
                                                 :arg2 arg2-expr)
                               out-type))))
         ((mv okp tyname arg in-type out-type) (atc-check-conv term))
         ((when okp)
          (b* (((er (list arg-expr type)) (atc-gen-expr-cval-pure arg
                                                                  inscope
                                                                  fn
                                                                  ctx
                                                                  state))
               ((unless (equal type in-type))
                (er-soft+ ctx t (irr)
                          "The conversion from ~x0 to ~x1 ~
                           is applied to a term ~x2 returning ~x3, ~
                           but a ~x0 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          in-type out-type arg type)))
            (acl2::value (list (make-expr-cast :type tyname
                                               :arg arg-expr)
                               out-type))))
         ((mv okp arr sub in-type1 in-type2 out-type)
          (atc-check-array-read term))
         ((when okp)
          (b* (((er (list arr-expr type1)) (atc-gen-expr-cval-pure arr
                                                                   inscope
                                                                   fn
                                                                   ctx
                                                                   state))
               ((er (list sub-expr type2)) (atc-gen-expr-cval-pure sub
                                                                   inscope
                                                                   fn
                                                                   ctx
                                                                   state))
               ((unless (and (equal type1 in-type1)
                             (equal type2 in-type2)))
                (er-soft+ ctx t (irr)
                          "The reading of a ~x0 array with a ~x1 index ~
                           is applied to a term ~x2 returning ~x3 ~
                           and to a term ~x4 returning ~x5, ~
                           but a ~x0 and a ~x1 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          in-type1 in-type2 arg1 type1 arg2 type2)))
            (acl2::value (list (make-expr-arrsub :arr arr-expr
                                                 :sub sub-expr)
                               out-type))))
         ((mv okp arg) (atc-check-sint-from-boolean term))
         ((when okp)
          (b* (((mv erp expr state)
                (atc-gen-expr-bool arg inscope fn ctx state))
               ((when erp) (mv erp (irr) state)))
            (mv nil (list expr (type-sint)) state)))
         ((mv okp test then else) (atc-check-condexpr term))
         ((when okp)
          (b* (((mv erp test-expr state) (atc-gen-expr-bool test
                                                            inscope
                                                            fn
                                                            ctx
                                                            state))
               ((when erp) (mv erp (irr) state))
               ((er (list then-expr then-type)) (atc-gen-expr-cval-pure
                                                 then
                                                 inscope
                                                 fn
                                                 ctx
                                                 state))
               ((er (list else-expr else-type)) (atc-gen-expr-cval-pure
                                                 else
                                                 inscope
                                                 fn
                                                 ctx
                                                 state))
               ((unless (equal then-type else-type))
                (er-soft+ ctx t (irr)
                          "When generating C code for the function ~x0, ~
                           two branches ~x1 and ~x2 of a conditional term ~
                           have different types ~x3 and ~x4; ~
                           use conversion operations, if needed, ~
                           to make the branches of the same type."
                          fn then else then-type else-type)))
            (acl2::value
             (list
              (make-expr-cond :test test-expr :then then-expr :else else-expr)
              then-type)))))
      (er-soft+ ctx t (list (irr-expr) (irr-type))
                "When generating C code for the function ~x0, ~
                 at a point where ~
                 an expression term returning a C value is expected, ~
                 the term ~x1 is encountered instead."
                fn term))
    :measure (pseudo-term-count term))

  (define atc-gen-expr-bool ((term pseudo-termp)
                             (inscope atc-symbol-type-alist-listp)
                             (fn symbolp)
                             (ctx ctxp)
                             state)
    :returns (mv erp (expr exprp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-pure)
    :short "Generate a C expression from an ACL2 term
            that must be an expression term returning a boolean."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is
       an expression term returning a boolean,
       as described in the user documentation.")
     (xdoc::p
      "If the term is a call of @(tsee not), @(tsee and), or @(tsee or),
       we recursively translate the arguments,
       which must be an expression term returning a boolean,
       and we construct a logical expression
       with the corresponding C operators.")
     (xdoc::p
      "If the term is a call of @('boolean-from-<type>'),
       we call the mutually recursive function
       that translates the argument,
       which must be an expression term returning a C value,
       to an expression, which we return.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an expression term returning a C value.
       We could extend this code to provide
       more information to the user at some point.")
     (xdoc::p
      "As in @(tsee atc-gen-expr-cval-pure),
       we perform C type checks on the ACL2 terms.
       See  @(tsee atc-gen-expr-cval-pure) for an explanation."))
    (b* (((mv okp arg) (fty-check-not-call term))
         ((when okp)
          (b* (((er arg-expr) (atc-gen-expr-bool arg
                                                 inscope
                                                 fn
                                                 ctx
                                                 state)))
            (acl2::value (make-expr-unary :op (unop-lognot)
                                          :arg arg-expr))))
         ((mv okp arg1 arg2) (fty-check-and-call term))
         ((when okp)
          (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                                  inscope
                                                  fn
                                                  ctx
                                                  state))
               ((er arg2-expr) (atc-gen-expr-bool arg2
                                                  inscope
                                                  fn
                                                  ctx
                                                  state)))
            (acl2::value (make-expr-binary :op (binop-logand)
                                           :arg1 arg1-expr
                                           :arg2 arg2-expr))))
         ((mv okp arg1 arg2) (fty-check-or-call term))
         ((when okp)
          (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                                  inscope
                                                  fn
                                                  ctx
                                                  state))
               ((er arg2-expr) (atc-gen-expr-bool arg2
                                                  inscope
                                                  fn
                                                  ctx
                                                  state)))
            (acl2::value (make-expr-binary :op (binop-logor)
                                           :arg1 arg1-expr
                                           :arg2 arg2-expr))))
         ((mv okp arg in-type) (atc-check-boolean-from-type term))
         ((when okp)
          (b* (((mv erp (list expr type) state)
                (atc-gen-expr-cval-pure arg inscope fn ctx state))
               ((when erp) (mv erp expr state))
               ((unless (equal type in-type))
                (er-soft+ ctx t (irr-expr)
                          "The conversion from ~x0 to boolean ~
                           is applied to a term ~x1 returning ~x2, ~
                           but a ~x0 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          in-type arg type)))
            (mv erp expr state))))
      (er-soft+ ctx t (irr-expr)
                "When generating C code for the function ~x0, ~
                 at a point where ~
                 a boolean ACL2 term is expected, ~
                 the term ~x1 is encountered instead."
                fn term))
    :measure (pseudo-term-count term))

  :prepwork ((set-state-ok t))

  :verify-guards nil ; done below

  ///

  (defret-mutual consp-of-atc-gen-expr-pure
    (defret typeset-of-atc-gen-expr-cval-pure
      (and (consp val)
           (true-listp val))
      :rule-classes :type-prescription
      :fn atc-gen-expr-cval-pure)
    (defret true-of-atc-gen-expr-bool
      t
      :rule-classes nil
      :fn atc-gen-expr-bool))

  (verify-guards atc-gen-expr-cval-pure))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-cval-pure-list ((terms pseudo-term-listp)
                                     (inscope atc-symbol-type-alist-listp)
                                     (fn symbolp)
                                     (ctx ctxp)
                                     state)
  :returns (mv erp
               (val (tuple (exprs expr-listp)
                           (types type-listp)
                           val))
               state)
  :short "Generate a list of C expressions from a list of ACL2 terms
          that must be pure expression terms returning C values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee atc-gen-expr-cval-pure) to lists.
     However, we do not return the C types of the expressions."))
  (b* (((when (endp terms)) (acl2::value (list nil nil)))
       ((mv erp (list expr type) state) (atc-gen-expr-cval-pure (car terms)
                                                                inscope
                                                                fn
                                                                ctx
                                                                state))
       ((when erp) (mv erp (list nil nil) state))
       ((er (list exprs types)) (atc-gen-expr-cval-pure-list (cdr terms)
                                                             inscope
                                                             fn
                                                             ctx
                                                             state)))
    (acl2::value (list (cons expr exprs)
                       (cons type types))))
  ///
  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name typeset-of-atc-gen-expr-cval-pure-list
        :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-cval ((term pseudo-termp)
                           (var-term-alist symbol-pseudoterm-alistp)
                           (inscope atc-symbol-type-alist-listp)
                           (fn symbolp)
                           (prec-fns atc-symbol-fninfo-alistp)
                           (ctx ctxp)
                           state)
  :returns (mv erp
               (val (tuple (expr exprp)
                           (type typep)
                           (affect symbol-listp)
                           (limit pseudo-termp)
                           val))
               state)
  :short "Generate a C expression from an ACL2 term
          that must be an expression term returning a C value."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time,
     we check that the term is an expression term returning a C value,
     as described in the user documentation.")
   (xdoc::p
    "We also return the C type of the expression,
     and the affected variables.")
   (xdoc::p
    "We also return a limit that suffices for @(tsee exec-expr-call-or-pure)
     to execute the expression completely.
     This is the limit (associated to the function)
     sufficient to run @(tsee exec-fun),
     plus 1 to get there from @(tsee exec-expr-call-or-pure).")
   (xdoc::p
    "If the term is a call of a function that precedes @('fn')
     in the list of target functions @('fn1'), ..., @('fnp'),
     we translate it to a C function call on the translated arguments.
     The type of the expression is the result type of the function,
     which is looked up in the function alist passed as input.
     A sufficient limit for @(tsee exec-fun) to execute the called function
     is retrieved from the called function's information;
     we add 1 to it, to take into account the decrementing of the limit
     done by @(tsee exec-expr-call-or-pure) when it calls @(tsee exec-fun).")
   (xdoc::p
    "Otherwise, we attempt to translate the term
     as a pure expression term returning a C value.
     The type is the one returned by that translation.
     As limit we return 1, which suffices for @(tsee exec-expr-call-or-pure)
     to not stop right away due to the limit being 0."))
  (b* (((mv okp called-fn args in-types out-type affect limit)
        (atc-check-cfun-call term var-term-alist prec-fns (w state)))
       ((when okp)
        (b* (((mv erp (list arg-exprs types) state)
              (atc-gen-expr-cval-pure-list args
                                           inscope
                                           fn
                                           ctx
                                           state))
             ((when erp) (mv erp (list (irr-expr) (irr-type) nil nil) state))
             ((unless (equal types in-types))
              (er-soft+ ctx t (list (irr-expr) (irr-type) nil nil)
                        "The function ~x0 with input types ~x1 ~
                         is applied to terms ~x2 returning ~x3. ~
                         This is indicative of provably dead code, ~
                         given that the code is guard-verified."
                        called-fn in-types args types)))
          (acl2::value (list
                        (make-expr-call :fun (make-ident
                                              :name (symbol-name called-fn))
                                        :args arg-exprs)
                        out-type
                        affect
                        `(binary-+ '1 ,limit))))))
    (b* (((mv erp (list expr type) state)
          (atc-gen-expr-cval-pure term inscope fn ctx state))
         ((when erp) (mv erp (list (irr-expr) (irr-type) nil nil) state)))
      (acl2::value (list expr type affect '(quote 1)))))
  ///
  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name typeset-of-atc-gen-expr-cval
        :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tyspecseq ((type typep))
  :guard (not (type-case type :pointer))
  :returns (tyspecseq tyspecseqp)
  :short "Generate a type specifier sequence for a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always called on a non-pointer type currently."))
  (type-case type
             :void (tyspecseq-void)
             :char (tyspecseq-char)
             :schar (tyspecseq-schar)
             :sshort (tyspecseq-sshort)
             :sint (tyspecseq-sint)
             :slong (tyspecseq-slong)
             :sllong (tyspecseq-sllong)
             :uchar (tyspecseq-uchar)
             :ushort (tyspecseq-ushort)
             :uint (tyspecseq-uint)
             :ulong (tyspecseq-ulong)
             :ullong (tyspecseq-ullong)
             :pointer (prog2$ (impossible) (irr-tyspecseq)))
  :hooks (:fix)
  ///

  (defrule type-name-to-type-of-tyname-of-atc-gen-tyspecseq
    (implies (not (type-case type :pointer))
             (equal (type-name-to-type (tyname (atc-gen-tyspecseq type) nil))
                    (type-fix type)))
    :enable type-name-to-type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-var-assignablep ((var symbolp)
                             (innermostp booleanp)
                             (affect symbol-listp))
  :returns (yes/no booleanp :hyp (booleanp innermostp))
  :short "Check if a variable is assignable,
          based on whether it is in the innermost scope
          and based on the variables being currently affected."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable may be destructively assigned to
     if any of the following conditions apply:
     (i) it is declared in the innermost scope,
     because in that case it cannot be accessed after exiting the scope;
     (ii) it is being affected,
     because in that case its modified value is returned
     and used in subsequent code;
     (iii) no variable is being affected,
     because in that case there is no subsequent code."))
  (or innermostp
      (and (member-eq var affect) t)
      (null affect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-vars-assignablep ((var-list symbol-listp)
                              (innermostp-list boolean-listp)
                              (affect symbol-listp))
  :guard (equal (len var-list) (len innermostp-list))
  :returns (yes/no booleanp :hyp (boolean-listp innermostp-list))
  :short "Lift @(tsee atc-var-assignablep) to lists."
  (or (endp var-list)
      (and
       (atc-var-assignablep (car var-list) (car innermostp-list) affect)
       (atc-vars-assignablep (cdr var-list) (cdr innermostp-list) affect))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-affecting-term-for-let-p ((term pseudo-termp)
                                      (prec-fns atc-symbol-fninfo-alistp))
  :returns (yes/no booleanp)
  :short "Check if a term @('term') has the basic structure
          required for representing code affecting variables
          in @('(let ((var term)) body)')
          or @('(mv-let (var1 ... varn) term body)')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is explained in the user documentation.
     Here we perform a shallow check,
     because we will examine the term in full detail
     when recursively generating C code from it.
     In essence, here we check that the term is either
     (i) an @(tsee if) whose test is not @(tsee mbt) or @(tsee mbt$) or
     (ii) a call of a (preceding) target function."))
  (case-match term
    (('if test . &) (and (case-match test
                           ((fn . &) (not (member-eq fn '(mbt mbt$))))
                           (& t))))
    ((fn . &) (and (symbolp fn)
                   (consp (assoc-eq fn prec-fns))))
    (& nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-make-mv-nth-terms ((indices nat-listp) (term pseudo-termp))
  :returns (terms pseudo-term-listp)
  :short "Create a list of @(tsee mv-nth)s applied to a term
          for a list of indices."
  (cond ((endp indices) nil)
        (t (cons `(mv-nth ',(car indices) ,(pseudo-term-fix term))
                 (atc-make-mv-nth-terms (cdr indices) term))))
  ///
  (defret len-of-atc-make-mv-nth-terms
    (equal (len terms)
           (len indices))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-update-var-term-alist ((vars symbol-listp)
                                   (terms pseudo-term-listp)
                                   (alist symbol-pseudoterm-alistp))
  :returns (new-alist symbol-pseudoterm-alistp)
  :short "Update an alist from symbols to terms."
  (append (pairlis$ (acl2::symbol-list-fix vars)
                    (pseudo-term-list-fix terms))
          (acl2::symbol-pseudoterm-alist-fix alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp)
                      (var-term-alist symbol-pseudoterm-alistp)
                      (inscope atc-symbol-type-alist-listp)
                      (loop-flag booleanp)
                      (affect symbol-listp)
                      (fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      (proofs booleanp)
                      (ctx ctxp)
                      state)
  :returns (mv erp
               (val (tuple (items block-item-listp)
                           (type typep)
                           (limit pseudo-termp)
                           val)
                    :hints nil)
               state)
  :short "Generate a C statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, we return a list of block items.
     These can be regarded as forming a compound statement,
     but lists of block items are compositional (via concatenation).")
   (xdoc::p
    "At the same time, we check that the term is a statement term,
     as described in the user documentation.")
   (xdoc::p
    "Along with the term, we pass an alist from symbols to terms
     that collects the @(tsee let) and @(tsee mv-let) bindings
     encountered along the way.
     These are eventually used to properly instantiate
     limits associated to function calls,
     because those limits apply to the functions' formals,
     which must therefore be replaced not just with the actuals of the call,
     but with those actuals with variables replaced with terms
     according to the bindings that lead to the call.")
   (xdoc::p
    "The @('loop-flag') parameter of this ACL2 function
     is the loop flag @('L') described in the user documentation.")
   (xdoc::p
    "The @('affect') parameter of this ACL2 function
     is the list of variables being affected by this statement.
     This is denoted @('vars') in the user documentation at @(tsee atc).")
   (xdoc::p
    "Besides the generated block items,
     we also return a C type, which is the one returned by the statement.")
   (xdoc::p
    "We also return a limit that suffices for @(tsee exec-block-item-list)
     to execute the returned block items completely.")
   (xdoc::p
    "If the term is a conditional, there are two cases.
     If the test is @(tsee mbt) or @(tsee mbt$),
     we discard test and `else' branch
     and recursively translate the `then' branch;
     the limit is the same as the `then' branch.
     Otherwise, we generate an @('if') statement
     (as a singleton block item list),
     with recursively generated compound statements as branches;
     the test expression is generated from the test term;
     we ensure that the two branches have the same type.
     When we process the branches,
     we extend the symbol table with a new empty scope for each branch.
     The calculation of the limit result is a bit more complicated in this case:
     we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from that to @(tsee exec-stmt),
     and another 1 to go to the @(':ifelse') case there;
     the test is pure and so it needs no addition to the limit;
     since either branch may be taken,
     we return the sum of the limits for the two branches.
     More precisely, the limit recursively returned for each branch
     pertains to the block item list in the branch,
     but those are put into a compound statement;
     thus, we need to increase the recursively calculated limit
     by 1 to go from @(tsee exec-block-item-list) to @(tsee exec-block-item),
     and another 1 to go from there to @(tsee exec-stmt).
     In principle we could return the maximum from the two branches
     instead of their sum,
     but we want the limits to be
     linear combinations of sub-limits,
     so that ACL2's linear arithmetic can handle the reasoning about limits
     during the generated proofs.")
   (xdoc::p
    "If the term is a @(tsee mv-let),
     we ensure that all its bound variables are in scope.
     We recursively treat the bound term as
     a statement term affecting the bound variables,
     generating block items for it;
     then we continue processing the body of the @(tsee mv-let)
     as a term affecting the variables in @('affect').
     We use the sum of the two limits as the overall limit:
     thus, after @(tsee exec-block-item-list) executes
     the block items for the bound term,
     it still has enough limit to executed the block items for the body term.")
   (xdoc::p
    "If the term is a @(tsee let), there are four cases.
     If the binding has the form of an array write,
     we generate an array assignment.
     Otherwise, if the term involves the @(tsee declar) wrapper,
     we ensure that a variable with the same symbol name is not already in scope
     (i.e. in the symbol table)
     and that the name is a portable ASCII identifier;
     we generate a declaration for the variable,
     initialized with the expression obtained
     from the term that the variable is bound to,
     which also determines the type of the variable,
     and which must affect no variables;
     the type must not be a pointer type (code generation fails if it is).
     Otherwise, if the term involves the @(tsee assign) wrapper,
     we ensure that the variable is assignable,
     which implies that it must be in scope,
     and we also ensure that it has the same type as the one in scope;
     we generate an assignment whose right-hand side is
     obtained from the unwrapped term,
     which must be an expression term returning a C value.
     Otherwise, if the term involves no wrapper,
     we also ensure that the variable is assignable,
     and that the non-wrapped term represents a conditional of loop in C;
     we generate code that affects the variable from that term.
     In all cases, we recursively generate the block items for the body
     and we put those just after the preceding code.")
   (xdoc::p
    "In the @(tsee let) case whose translation is explained above,
     the limit is calculated as follows.
     For the case of an array write, the limit is irrelevant for now;
     we do not generate proofs for array writes.
     For the case of the term representing code that affects variables,
     we add up the two limits,
     similarly to the @(tsee mv-let) case.
     For the other cases, we have one block item followed by block items.
     First, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item).
     Then we take the sum of the limit for the first block item
     and the limit for the remaining block items
     (in principle we could take the maximum,
     but see the discussion above for @(tsee if)
     for why we take the sum instead).
     The first block item is either a declaration or an assignment.
     If it is a declaration, we need 1 to go from @(tsee exec-block-item)
     to the @(':declon') case and to @(tsee exec-expr-call-or-pure).
     If it is an assignment, we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and to @(tsee exec-stmt),
     another 1 to go from there to the @(':expr') case
     and to @(tsee exec-expr-asg),
     and another 1 to go from there to @(tsee exec-expr-call-or-pure),
     for which we recursively get the limit.
     For the remaining block items, we need to add another 1
     to go from @(tsee exec-block-item-list) to its recursive call.")
   (xdoc::p
    "If the term is a single variable
     and @('affect') is a singleton list with that variable,
     there are two cases:
     if the loop flag is @('t'), it is an error;
     otherwise, we return nothing, because
     this is the end of a list of block items that affects that variable.")
   (xdoc::p
    "If the term is an @(tsee mv), there are three cases.
     If the loop flag is @('t'), it is an error.
     Otherwise, if the arguments of @(tsee mv) are the @('affect') variables,
     we return nothing, because
     this is the end of a list of block items that affects that variable.
     Otherwise, if the @(tsee cdr) of the arguments of @(tsee mv)
     are the @('affect') variables,
     we treat the @(tsee car) of the arguments of @(tsee mv)
     as an expression term that must affect no variables,
     and generate a return statement for it.")
   (xdoc::p
    "If the term is a call of a recursive target function on its formals,
     different from the current function @('fn'),
     then the term represents a loop.
     The loop flag must be @('nil') for this to be allowed.
     We retrieve the associated loop statement and return it.
     We also retrieve the associated limit term,
     which, as explained in @(tsee atc-fn-info),
     suffices to execute @(tsee exec-stmt-while).
     But here we are executing lists of block items,
     so we need to add 1 to go from @(tsee exec-block-item-list)
     to the call to @(tsee exec-block-item),
     another 1 to go from there to the call to @(tsee exec-stmt),
     and another 1 to go from there to the call to @(tsee exec-stmt-while).")
   (xdoc::p
    "If the term is a call of the current function @('fn') on its formals,
     we ensure that the loop flag is @('t'),
     and we generate no code.
     This represents the conclusion of a loop body (on some path).")
   (xdoc::p
    "If the term does not have any of the forms above,
     we treat it as an expression term returning a C value.
     We ensure that the loop flag is @('nil').
     We also ensure that the expression affects
     the same variables as the statement term.
     For the limit, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from there to the @(':stmt') case and @(tsee exec-stmt),
     another 1 to go from there to the @(':return') case
     and @(tsee exec-expr-call-or-pure),
     for which we use the recursively calculated limit."))
  (b* ((irr (list nil (irr-type) nil))
       ((mv okp test then else) (fty-check-if-call term))
       ((when okp)
        (b* (((mv mbtp &) (check-mbt-call test))
             ((when mbtp)
              (atc-gen-stmt then
                            var-term-alist
                            inscope
                            loop-flag
                            affect
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             ((mv mbt$p &) (check-mbt$-call test))
             ((when mbt$p)
              (atc-gen-stmt then
                            var-term-alist
                            inscope
                            loop-flag
                            affect
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             ((mv erp test-expr state) (atc-gen-expr-bool test
                                                          inscope
                                                          fn
                                                          ctx
                                                          state))
             ((when erp) (mv erp irr state))
             ((er (list then-items then-type then-limit))
              (atc-gen-stmt then
                            var-term-alist
                            (cons nil inscope)
                            loop-flag
                            affect
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             ((er (list else-items else-type else-limit))
              (atc-gen-stmt else
                            var-term-alist
                            (cons nil inscope)
                            loop-flag
                            affect
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             ((unless (equal then-type else-type))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         two branches ~x1 and ~x2 of a conditional term ~
                         have different types ~x3 and ~x4; ~
                         use conversion operations, if needed, ~
                         to make the branches of the same type."
                        fn then else then-type else-type))
             (type then-type)
             (limit (pseudo-term-fncall
                     'binary-+
                     (list
                      (pseudo-term-quote 5)
                      (pseudo-term-fncall
                       'binary-+
                       (list then-limit else-limit))))))
          (acl2::value
           (list
            (list
             (block-item-stmt
              (make-stmt-ifelse :test test-expr
                                :then (make-stmt-compound :items then-items)
                                :else (make-stmt-compound :items else-items))))
            type
            limit))))
       ((mv okp & vars indices & val body) (fty-check-mv-let-call term))
       ((when okp)
        (b* (((unless (> (len vars) 1))
              (mv (raise "Internal error: MV-LET ~x0 has less than 2 variables."
                         term)
                  irr
                  state))
             ((mv type?-list innermostp-list)
              (atc-get-vars-check-innermost vars inscope))
             ((when (member-eq nil type?-list))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         an attempt is made to modify the variables ~x1, ~
                         not all of which are in scope."
                        fn vars))
             ((unless (atc-vars-assignablep vars innermostp-list affect))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         an attempt is made to modify the variables ~x1, ~
                         not all of which are assignable."
                        fn vars))
             ((unless (atc-affecting-term-for-let-p val prec-fns))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         an MV-LET has been encountered ~
                         whose term ~x1 to which the variables are bound ~
                         does not have the required form."
                        fn val))
             ((er (list xform-items xform-type xform-limit))
              (atc-gen-stmt val
                            var-term-alist
                            inscope
                            nil
                            vars
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             ((unless (type-case xform-type :void))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         an MV-LET has been encountered ~
                         whose term ~x1 to which the variables are bound ~
                         has the non-void type ~x2, ~
                         which is disallowed."
                        fn val xform-type))
             (val-instance (fty-fsublis-var var-term-alist val))
             (vals (atc-make-mv-nth-terms indices val-instance))
             (var-term-alist-body
              (atc-update-var-term-alist vars vals var-term-alist))
             ((er (list body-items body-type body-limit))
              (atc-gen-stmt body
                            var-term-alist-body
                            inscope
                            loop-flag
                            affect
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             (items (append xform-items body-items))
             (type body-type)
             (limit (pseudo-term-fncall 'binary-+
                                        (list xform-limit body-limit))))
          (acl2::value (list items type limit))))
       ((mv okp var val body wrapper?) (atc-check-let term))
       ((when okp)
        (b* ((val-instance (fty-fsublis-var var-term-alist val))
             (var-term-alist-body
              (atc-update-var-term-alist (list var)
                                         (list val-instance)
                                         var-term-alist))
             ((mv okp sub elem sub-type elem-type)
              (atc-check-array-write var val))
             ((when okp)
              (b* (((when proofs)
                    (er-soft+ ctx t irr
                              "Proofs are not yet supported for array writes; ~
                               use :PROOFS NIL to generate ~
                               code without proofs."))
                   ((unless (member-eq var affect))
                    (er-soft+ ctx t irr
                              "The array ~x0 is being written to, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var affect))
                   ((mv erp (list arr-expr type1) state)
                    (atc-gen-expr-cval-pure var inscope fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp (list sub-expr type2) state)
                    (atc-gen-expr-cval-pure sub inscope fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp (list elem-expr type3) state)
                    (atc-gen-expr-cval-pure elem inscope fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal type1 (type-pointer elem-type)))
                    (er-soft+ ctx t irr
                              "The array ~x0 of type ~x1 ~
                               does not have the expected type ~x2. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var type1 (type-pointer elem-type)))
                   ((unless (equal type2 sub-type))
                    (er-soft+ ctx t irr
                              "The array ~x0 of type ~x1 ~
                               is being indexed with
                               a subscript ~x2 of type x3, ~
                               instead of type ~x4 as expected.
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var type1 sub type2 sub-type))
                   ((unless (equal type3 elem-type))
                    (er-soft+ ctx t irr
                              "The array ~x0 of type ~x1 ~
                               is being written to with ~
                               an element ~x2 of type x3, ~
                               instead of type ~x4 as expected.
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var type1 elem type3 elem-type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (make-expr-arrsub :arr arr-expr
                                                 :sub sub-expr)
                         :arg2 elem-expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (list body-items body-type body-limit))
                    (atc-gen-stmt body
                                  var-term-alist-body
                                  inscope
                                  loop-flag
                                  affect
                                  fn
                                  prec-fns
                                  proofs
                                  ctx
                                  state))
                   (limit (pseudo-term-fncall 'binary-+
                                              (list (pseudo-term-quote 4)
                                                    body-limit))))
                (acl2::value (list (cons item body-items)
                                   body-type
                                   limit))))
             ((mv type? innermostp errorp) (atc-check-var var inscope))
             ((when errorp)
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         a new variable ~x1 has been encountered ~
                         that has the same symbol name as, ~
                         but different package name from, ~
                         a variable already in scope. ~
                         This is disallowed."
                        fn var))
             ((when (eq wrapper? 'declar))
              (b* (((when type?)
                    (er-soft+ ctx t irr
                              "The variable ~x0 in the function ~x1 ~
                               is already in scope and cannot be re-declared."
                              var fn))
                   ((unless (atc-ident-stringp (symbol-name var)))
                    (er-soft+ ctx t irr
                              "The symbol name ~s0 of ~
                               the LET variable ~x1 of the function ~x2 ~
                               must be a portable ASCII C identifier, ~
                               but it is not."
                              (symbol-name var) var fn))
                   ((mv erp
                        (list init-expr init-type init-affect init-limit)
                        state)
                    (atc-gen-expr-cval val
                                       var-term-alist
                                       inscope
                                       fn
                                       prec-fns
                                       ctx
                                       state))
                   ((when erp) (mv erp irr state))
                   ((when (consp init-affect))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not affect any variables, ~
                               but it affects ~x2 instead."
                              val var init-affect))
                   ((when (type-case init-type :pointer))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not have a C pointer type, ~
                               but it has type ~x2 instead."
                              val var init-type))
                   (declon (make-declon-var :type (atc-gen-tyspecseq init-type)
                                            :declor (make-declor
                                                     :ident
                                                     (make-ident
                                                      :name (symbol-name var)))
                                            :init init-expr))
                   (item (block-item-declon declon))
                   (inscope (atc-add-var var init-type inscope))
                   ((er (list body-items body-type body-limit))
                    (atc-gen-stmt body
                                  var-term-alist-body
                                  inscope
                                  loop-flag
                                  affect
                                  fn
                                  prec-fns
                                  proofs
                                  ctx
                                  state))
                   (type body-type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list init-limit body-limit))))
                (acl2::value (list (cons item body-items)
                                   type
                                   limit))))
             ((unless (atc-var-assignablep var innermostp affect))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         an attempt is being made ~
                         to modify a non-assignable variable ~x1."
                        fn var))
             ((when (eq wrapper? 'assign))
              (b* ((prev-type type?)
                   ((mv erp
                        (list rhs-expr rhs-type rhs-affect rhs-limit)
                        state)
                    (atc-gen-expr-cval val
                                       var-term-alist
                                       inscope
                                       fn
                                       prec-fns
                                       ctx
                                       state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal prev-type rhs-type))
                    (er-soft+ ctx t irr
                              "The type ~x0 of the term ~x1 ~
                               assigned to the LET variable ~x2 ~
                               of the function ~x3 ~
                               differs from the type ~x4 ~
                               of a variable with the same symbol in scope."
                              rhs-type val var fn prev-type))
                   ((when (consp rhs-affect))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not affect any variables, ~
                               but it affects ~x2 instead."
                              val var rhs-affect))
                   ((when (type-case rhs-type :pointer))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not have a C pointer type, ~
                               but it has type ~x2 instead."
                              val var rhs-type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (expr-ident (make-ident :name (symbol-name var)))
                         :arg2 rhs-expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (list body-items body-type body-limit))
                    (atc-gen-stmt body
                                  var-term-alist
                                  inscope
                                  loop-flag
                                  affect
                                  fn
                                  prec-fns
                                  proofs
                                  ctx
                                  state))
                   (type body-type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 4)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list rhs-limit body-limit))))))
                (acl2::value (list (cons item body-items)
                                   type
                                   limit))))
             ((unless (eq wrapper? nil))
              (prog2$ (raise "Internal error: LET wrapper is ~x0." wrapper?)
                      (acl2::value irr)))
             ((unless (atc-affecting-term-for-let-p val prec-fns))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         we encountered an unwrapped term ~x1 ~
                         to which a LET variable is bound ~
                         that is neither an IF or a loop function call. ~
                         This is disallowed."
                        fn val))
             ((er (list xform-items xform-type xform-limit))
              (atc-gen-stmt val
                            var-term-alist
                            inscope
                            nil
                            (list var)
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             ((unless (type-case xform-type :void))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         a LET has been encountered ~
                         whose unwrapped term ~x1 ~
                         to which the variable is bound ~
                         has the non-void type ~x2, ~
                         which is disallowed."
                        fn val xform-type))
             ((er (list body-items body-type body-limit))
              (atc-gen-stmt body
                            var-term-alist-body
                            inscope
                            loop-flag
                            affect
                            fn
                            prec-fns
                            proofs
                            ctx
                            state))
             (items (append xform-items body-items))
             (type body-type)
             (limit (pseudo-term-fncall
                     'binary-+
                     (list xform-limit body-limit))))
          (acl2::value (list items type limit))))
       ((when (and (pseudo-term-case term :var)
                   (equal affect (list (pseudo-term-var->name term)))))
        (if loop-flag
            (er-soft+ ctx t irr
                      "A loop body must end with ~
                       a recursive call on every path, ~
                       but in the fucntion ~x0 it ends with ~x1 instead."
                      fn term)
          (acl2::value (list nil (type-void) (pseudo-term-quote 0)))))
       ((mv okp terms) (fty-check-list-call term))
       ((when okp)
        (b* (((unless (>= (len terms) 2))
              (raise "Internal error: MV applied to ~x0." terms)
              (acl2::value irr))
             ((when loop-flag)
              (er-soft+ ctx t irr
                        "A loop body must end with ~
                         a recursive call on every path, ~
                         but in the fucntion ~x0 ~
                         it ends with ~x1 instead."
                        fn term)))
          (cond
           ((equal terms affect)
            (acl2::value (list nil (type-void) (pseudo-term-quote 0))))
           ((equal (cdr terms) affect)
            (b* (((mv erp (list expr type eaffect limit) state)
                  (atc-gen-expr-cval
                   (car terms) var-term-alist inscope fn prec-fns ctx state))
                 ((when erp) (mv erp irr state))
                 ((when (consp eaffect))
                  (er-soft+ ctx t irr
                            "The first argument ~x0 of the term ~x1 ~
                             in the function ~x2 ~
                             affects the variables ~x3, which is disallowed."
                            (car terms) term fn eaffect))
                 (limit (pseudo-term-fncall
                         'binary-+
                         (list (pseudo-term-quote 3)
                               limit))))
              (acl2::value (list
                            (list
                             (block-item-stmt (make-stmt-return :value expr)))
                            type
                            limit))))
           (t (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         a term ~x0 has been encountered, ~
                         which is disallowed."
                        fn term)))))
       ((mv okp loop-fn loop-args in-types loop-affect loop-stmt loop-limit)
        (atc-check-loop-call term var-term-alist prec-fns))
       ((when okp)
        (b* (((when loop-flag)
              (er-soft+ ctx t irr
                        "A loop body must end with ~
                         a recursive call on every path, ~
                         but in the fucntion ~x0 it ends with ~x1 instead."
                        fn term))
             (formals (formals+ loop-fn (w state)))
             ((unless (equal formals loop-args))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         a call of the recursive function ~x1 ~
                         has been encountered ~
                         that is not on its formals, ~
                         but instead on the arguments ~x2.
                         This is disallowed; see the ATC user documentation."
                        fn loop-fn loop-args))
             ((unless (equal affect loop-affect))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         a call of the recursive function ~x1 ~
                         has been encountered
                         that represents a loop affecting ~x2, ~
                         which differs from the variables ~x3 ~
                         being affected here."
                        fn loop-fn loop-affect affect))
             (types (atc-get-vars formals inscope))
             ((when (member-eq nil types))
              (raise "Internal error: not all formals ~x0 have types ~x1."
                     formals types)
              (acl2::value irr))
             ((unless (equal types in-types))
              (er-soft+ ctx t irr
                        "The loop function ~x0 with input types ~x1 ~
                         is applied to terms ~x2 returning ~x3. ~
                         This is indicative of dead code under the guards, ~
                         given that the code is guard-verified."
                        loop-fn in-types formals types))
             (limit (pseudo-term-fncall
                     'binary-+
                     (list (pseudo-term-quote 3)
                           loop-limit))))
          (acl2::value (list (list (block-item-stmt loop-stmt))
                             (type-void)
                             limit))))
       ((when (equal term `(,fn ,@(formals+ fn (w state)))))
        (if loop-flag
            (acl2::value (list nil (type-void) (pseudo-term-quote 0)))
          (er-soft+ ctx t irr
                    "When generating code for the recursive function ~x0, ~
                     a recursive call to the loop function occurs ~
                     not at the end of the computation on some path."
                    fn)))
       ((mv erp (list expr type eaffect limit) state)
        (atc-gen-expr-cval term var-term-alist inscope fn prec-fns ctx state))
       ((when erp) (mv erp irr state))
       ((when loop-flag)
        (er-soft+ ctx t irr
                  "A loop body must end with ~
                   a recursive call on every path, ~
                   but in the fucntion ~x0 it ends with ~x1 instead."
                  fn term))
       ((unless (equal affect eaffect))
        (er-soft+ ctx t irr
                  "When generating code for the non-recursive function ~x0, ~
                   a term ~x1 was encountered at the end of the computation, ~
                   that affects the variables ~x2, ~
                   but ~x0 affects the variables ~x3 instead."
                  fn term eaffect affect))
       ((when (type-case type :void))
        (raise "Internal error: return term ~x0 has type void." term)
        (acl2::value irr))
       ((when (type-case type :pointer))
        (er-soft+ ctx t irr
                  "When generating a return statement for function ~x0, ~
                   the term ~x1 that represents th return expression ~
                   has pointer type ~x2, which is disallowed."
                  fn term type))
       (limit (pseudo-term-fncall
               'binary-+
               (list (pseudo-term-quote 3)
                     limit))))
    (acl2::value (list (list (block-item-stmt (make-stmt-return :value expr)))
                       type
                       limit)))

  :measure (pseudo-term-count term)

  :prepwork ((local
              (in-theory
               ;; for speed:
               (disable
                pseudo-termp ; treat terms abstractly
                w ; treat worlds abstractly
                ;; useless according to accumulated persistence:
                acl2::pseudo-term-listp-when-symbol-listp
                acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
                assoc-equal
                default-car
                default-cdr
                acl2::symbol-listp-when-not-consp
                nth
                acl2::consp-when-member-equal-of-symbol-pseudoterm-alistp
                consp-when-member-equal-of-atc-symbol-fninfo-alistp
                acl2::consp-when-member-equal-of-symbol-symbol-alistp
                acl2::consp-when-member-equal-of-keyword-truelist-alistp
                acl2::consp-when-member-equal-of-keyword-symbol-alistp
                consp-when-member-equal-of-atc-symbol-type-alistp
                consp-when-member-equal-of-atc-symbol-fninfo-alistp
                acl2::consp-when-member-equal-of-symbol-symbol-alistp
                acl2::consp-when-member-equal-of-keyword-truelist-alistp
                acl2::consp-when-member-equal-of-keyword-symbol-alistp
                consp-when-member-equal-of-atc-symbol-type-alistp
                consp-when-member-equal-of-atc-symbol-fninfo-alistp
                member-equal
                acl2::member-when-atom
                acl2::pseudo-term-listp-when-not-consp
                acl2::symbolp-of-car-when-member-equal-of-symbol-pseudoterm-alistp
                symbolp-of-car-when-member-equal-of-atc-symbol-fninfo-alistp
                type-optionp-of-car-when-type-option-listp
                typep-of-car-when-type-listp
                acl2::symbolp-of-car-when-member-equal-of-symbol-symbol-alistp
                symbolp-of-car-when-member-equal-of-atc-symbol-type-alistp
                type-listp-when-not-consp
                type-option-listp-of-cdr-when-type-option-listp
                acl2::pseudo-term-listp-cdr-when-pseudo-term-listp
                type-listp-of-cdr-when-type-listp
                block-item-listp-when-not-consp
                acl2::pseudo-term-listp-when-subsetp-equal
                acl2::pseudo-termp-car-when-pseudo-term-listp
                acl2::append-when-not-consp
                default-<-1
                acl2::pseudo-termp-when-member-equal-of-pseudo-term-listp
                acl2::pseudo-term-list-fix-under-pseudo-term-list-equiv
                acl2::pseudo-fnsym-fix-under-pseudo-fnsym-equiv
                type-optionp-when-in-type-option-setp-binds-free-x
                default-<-2
                default-+-1
                typep-when-in-type-setp-binds-free-x
                default-symbol-name
                acl2::subsetp-when-atom-right
                acl2::subsetp-when-atom-left))))

  :verify-guards nil ; done below

  ///

  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name cons-true-listp-of-atc-gen-stmt-val
        :rule-classes :type-prescription
        :hints (("Goal"
                 :in-theory (e/d (std::tuplep)
                                 (atc-gen-stmt
                                  return-type-of-atc-gen-stmt.val))
                 :use return-type-of-atc-gen-stmt.val))))

  (defret true-listp-of-atc-gen-stmt.items
    (true-listp (car val))
    :rule-classes :type-prescription
    :hints (("Goal"
             :in-theory (e/d (std::tuplep)
                             (atc-gen-stmt
                              return-type-of-atc-gen-stmt.val))
             :use return-type-of-atc-gen-stmt.val)))

  (defrulel true-listp-when-keyword-listp
    (implies (keyword-listp x)
             (true-listp x)))

  (defrulel pseudo-termp-when-symbolp
    (implies (symbolp x)
             (pseudo-termp x))
    :enable pseudo-termp)

  (verify-guards atc-gen-stmt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-stmt ((term pseudo-termp)
                           (inscope atc-symbol-type-alist-listp)
                           (fn symbolp)
                           (measure-for-fn symbolp)
                           (measure-formals symbol-listp)
                           (prec-fns atc-symbol-fninfo-alistp)
                           (proofs booleanp)
                           (ctx ctxp)
                           state)
  :returns (mv erp
               (val (tuple (stmt stmtp)
                           (test-term pseudo-termp)
                           (body-term pseudo-termp)
                           (affect symbol-listp)
                           (limit-body pseudo-termp)
                           (limit-all pseudo-termp)
                           val)
                    :hints (("Goal" :in-theory (disable member-equal))))
               state)
  :short "Generate a C loop statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on loop terms (see user documentation).")
   (xdoc::p
    "The term must be an @(tsee if).
     If the test is an @(tsee mbt) or @(tsee mbt$),
     test and `else' branch are ignored,
     while the `then' branch is recursively processed.
     Otherwise, the test must be an expression term returning a boolean
     from which we generate the loop test;
     the `then' branch must be a statement term,
     from which we generate the loop body;
     and the `else' branch must be either a single variable
     or an @(tsee mv) call on variables,
     which must be a subset of the function's formals,
     and from those variables we determine
     the variables affected by the loop.
     The statement term in the `then' branch
     must affect the variables found in the `else' branch.
     We return
     the term that represents the loop test,
     the term that represent the loop body
     and the variables affected by the loop.
     The loop test and body are used to generate more modular theorems.")
   (xdoc::p
    "Note that we push a new scope before processing the loop body.
     This is because the loop body is a block, which opens a new scope in C.")
   (xdoc::p
    "We return a limit that suffices
     to execute @(tsee exec-stmt-while) on (the test and body of)
     the loop statement, as follows.
     We need 1 to get to executing the test,
     which is pure and so does not contribute to the overall limit.
     If the test is true, we need to add the limit to execute the body.
     After that, @(tsee exec-stmt-while) is called recursively,
     decrementing the limit:
     given that we know that the loop function terminates,
     its measure must suffice as the limit.
     The loop function decreases the measure by at least 1 (maybe more)
     at every recursive call, so the limit does not decrease any faster,
     and we will never run out of the limit before the measure runs out.
     Thus the measure is an over-approximation for the limit, which is sound.
     We also note that the measure refers to the initial call of the function,
     while here it would suffice
     to take the measure at the first recursive call,
     but taking the whole measure is simpler,
     and again it is sound to over-appoximate.
     Note that we use the measure function for @('fn')
     that is generated by ATC,
     for the reasons explained in @(tsee atc-gen-loop-measure-fn).
     Besides the @('limit-all') result,
     which is the limit for the whole loop,
     we also return @('limit-body'), which is just for the loop body;
     this is in support for more modular proofs. "))
  (b* (((acl2::fun (irr)) (list (irr-stmt) nil nil nil nil nil))
       ((mv okp test then else) (fty-check-if-call term))
       ((unless okp)
        (er-soft+ ctx t (irr)
                  "When generating C loop code for the recursive function ~x0, ~
                   a term ~x1 that is not an IF has been encountered."
                  fn term))
       ((mv mbtp &) (check-mbt-call test))
       ((when mbtp)
        (atc-gen-loop-stmt then
                           inscope
                           fn
                           measure-for-fn
                           measure-formals
                           prec-fns
                           proofs
                           ctx
                           state))
       ((mv mbt$p &) (check-mbt$-call test))
       ((when mbt$p)
        (atc-gen-loop-stmt then
                           inscope
                           fn
                           measure-for-fn
                           measure-formals
                           prec-fns
                           proofs
                           ctx
                           state))
       ((mv erp test-expr state) (atc-gen-expr-bool test
                                                    inscope
                                                    fn
                                                    ctx
                                                    state))
       ((when erp) (mv erp (irr) state))
       (wrld (w state))
       ((unless (plist-worldp wrld))
        (prog2$ (raise "Internal error: world does not satisfy PLIST-WORLDP.")
                (acl2::value (irr))))
       (formals (formals+ fn wrld))
       ((mv okp affect)
        (b* (((when (member-equal else formals)) (mv t (list else)))
             ((mv okp terms) (fty-check-list-call else))
             ((when (and okp
                         (subsetp-eq terms formals)))
              (mv t terms)))
          (mv nil nil)))
       ((unless okp)
        (er-soft+ ctx t (irr)
                  "The non-recursive branch ~x0 of the function ~x1 ~
                   does not have the required form. ~
                   See the user documentation."
                  else fn))
       ((mv erp (list body-items body-type body-limit) state)
        (atc-gen-stmt then
                      nil
                      (cons nil inscope)
                      t
                      affect
                      fn
                      prec-fns
                      proofs
                      ctx
                      state))
       ((when erp) (mv erp (irr) state))
       ((unless (type-case body-type :void))
        (raise "Internal error: ~
                the loop body ~x0 of ~x1 ~ returns type ~x2."
               then fn body-type)
        (acl2::value (irr)))
       (body-stmt (make-stmt-compound :items body-items))
       (stmt (make-stmt-while :test test-expr :body body-stmt))
       ((unless (symbol-listp affect))
        (raise "Internal error: ~x0 is not a list of symbols." affect)
        (acl2::value (irr)))
       (wrld (w state))
       ((unless (plist-worldp wrld))
        (raise "Internal error: malformed world.")
        (acl2::value (irr)))
       (measure-call `(,measure-for-fn ,@measure-formals))
       ((unless (pseudo-termp measure-call))
        (raise "Internal error.")
        (acl2::value (irr)))
       (limit `(binary-+ '1 (binary-+ ,body-limit ,measure-call))))
    (acl2::value (list stmt test then affect body-limit limit)))
  :measure (pseudo-term-count term)
  :prepwork
  ((local (include-book "std/typed-lists/symbol-listp" :dir :system)))
  ///

  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name cons-true-listp-of-atc-gen-loop-stmt-val
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (disable member-equal))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-typed-formals ((fn symbolp) (ctx ctxp) state)
  :returns (mv erp
               (typed-formals atc-symbol-type-alistp)
               state)
  :short "Calculate the C types of the formal parameters of a target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look for a term of the form @('(<type> <formal>)')
     among the conjuncts of the function's guard,
     for each formal @('<formal>') of @('fn'),
     where @('<type>') is a predicate corresponding to a C type.
     For now we only accept certain types,
     namely the supported integer types and pointer types to them;
     note that the array predicates correspond to pointer types.")
   (xdoc::p
    "We ensure that there is exactly one such term for each formal.
     If this is successful,
     we return an alist from the formals to the types.
     The alist has unique keys, in the order of the formals.")
   (xdoc::p
    "We first extract the guard's conjuncts,
     then we go through the conjuncts, looking for the pattern,
     and we expand an alist from formals to types as we find patterns;
     this preliminary alist may not have the keys in order,
     because it goes according to the order of the guard's conjuncts.
     As we construct this preliminary alist,
     we check for multiple terms for the same formal,
     rejecting them even if they are identical.
     Then we construct the final alist by going through the formals in order,
     and looking up their types in the preliminary alist;
     here we detect when a formal has no corresponding conjunct in the guard."))
  (b* ((wrld (w state))
       (formals (formals+ fn wrld))
       (guard (uguard+ fn wrld))
       (guard-conjuncts (flatten-ands-in-lit guard))
       ((er prelim-alist) (atc-typed-formals-prelim-alist fn
                                                          formals
                                                          guard
                                                          guard-conjuncts
                                                          nil
                                                          ctx
                                                          state)))
    (atc-typed-formals-final-alist fn formals guard prelim-alist ctx state))

  :prepwork

  ((define atc-typed-formals-prelim-alist ((fn symbolp)
                                           (formals symbol-listp)
                                           (guard pseudo-termp)
                                           (guard-conjuncts pseudo-term-listp)
                                           (prelim-alist atc-symbol-type-alistp)
                                           (ctx ctxp)
                                           state)
     :returns (mv erp
                  (prelim-alist-final atc-symbol-type-alistp)
                  state)
     :parents nil
     (b* (((when (endp guard-conjuncts))
           (acl2::value (atc-symbol-type-alist-fix prelim-alist)))
          (conjunct (car guard-conjuncts))
          ((unless (and (nvariablep conjunct)
                        (not (fquotep conjunct))
                        (not (flambda-applicationp conjunct))))
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           ctx
                                           state))
          (type-fn (ffn-symb conjunct))
          (type (case type-fn
                  (scharp (type-schar))
                  (ucharp (type-uchar))
                  (sshortp (type-sshort))
                  (ushortp (type-ushort))
                  (sintp (type-sint))
                  (uintp (type-uint))
                  (slongp (type-slong))
                  (ulongp (type-ulong))
                  (sllongp (type-sllong))
                  (ullongp (type-ullong))
                  (schar-arrayp (type-pointer (type-schar)))
                  (uchar-arrayp (type-pointer (type-uchar)))
                  (sshort-arrayp (type-pointer (type-sshort)))
                  (ushort-arrayp (type-pointer (type-ushort)))
                  (sint-arrayp (type-pointer (type-sint)))
                  (uint-arrayp (type-pointer (type-uint)))
                  (slong-arrayp (type-pointer (type-slong)))
                  (ulong-arrayp (type-pointer (type-ulong)))
                  (sllong-arrayp (type-pointer (type-sllong)))
                  (ullong-arrayp (type-pointer (type-ullong)))
                  (t nil)))
          ((when (not type))
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           ctx
                                           state))
          (arg (fargn conjunct 1))
          ((unless (member-eq arg formals))
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           ctx
                                           state))
          ((when (consp (assoc-eq arg prelim-alist)))
           (er-soft+ ctx t nil
                     "The guard ~x0 of the target function ~x1 ~
                      includes multiple type predicates ~
                      for the formal parameter ~x2. ~
                      This is disallowed: every formal paramter ~
                      must have exactly one type predicate in the guard, ~
                      even when the multiple predicates are the same."
                     guard fn arg))
          (prelim-alist (acons arg type prelim-alist)))
       (atc-typed-formals-prelim-alist fn
                                       formals
                                       guard
                                       (cdr guard-conjuncts)
                                       prelim-alist
                                       ctx
                                       state))
     :prepwork
     ((local (include-book "std/typed-lists/symbol-listp" :dir :system))))

   (define atc-typed-formals-final-alist ((fn symbolp)
                                          (formals symbol-listp)
                                          (guard pseudo-termp)
                                          (prelim-alist atc-symbol-type-alistp)
                                          (ctx ctxp)
                                          state)
     :returns (mv erp
                  (typed-formals atc-symbol-type-alistp)
                  state)
     :parents nil
     (b* (((when (endp formals)) (acl2::value nil))
          (formal (symbol-fix (car formals)))
          (formal+type (assoc-eq formal
                                 (atc-symbol-type-alist-fix prelim-alist)))
          ((when (not (consp formal+type)))
           (er-soft+ ctx t nil
                     "The guard ~x0 of the target function ~x1 ~
                      has no type predicate for the formal parameter ~x2. ~
                      Every formal parameter must have a type predicate."
                     guard fn formal))
          (type (cdr formal+type))
          ((er typed-formals) (atc-typed-formals-final-alist fn
                                                             (cdr formals)
                                                             guard
                                                             prelim-alist
                                                             ctx
                                                             state)))
       (acl2::value (acons formal type typed-formals)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-declon-list ((typed-formals atc-symbol-type-alistp)
                                   (fn symbolp)
                                   (ctx ctxp)
                                   state)
  :returns (mv erp
               (val (tuple (params param-declon-listp)
                           (pointers atc-symbol-type-alistp)
                           val))
               state)
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 formal parameters are actually passed as an alist,
     from the formals to their C types,
     as calculated by @(tsee atc-typed-formals).")
   (xdoc::p
    "We also return an alist whose keys are
     the formal parameters that are pointers in C
     and whose values are the types referenced by the pointers.
     These get a special treatment
     in the formulation of the generated correctness theorems.
     This is a sub-alist of @('typed-formals');
     we may actually abolish it in the future,
     suitably using @('typed-formals') instead.")
   (xdoc::p
    "We check that the name of the parameter is a portable C identifier,
     and distinct from the names of the other parameters.")
   (xdoc::p
    "If the type is a pointer type,
     we put the pointer indication into the declarator.
     Only pointers to non-pointer types are allowed
     (i.e. not pointers to pointers),
     so we stop with an internal error if we encounter a pointer to pointer."))
  (b* (((when (endp typed-formals)) (acl2::value (list nil nil)))
       ((cons formal type) (car typed-formals))
       (name (symbol-name formal))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (list nil nil)
                  "The symbol name ~s0 of ~
                   the formal parameter ~x1 of the function ~x2 ~
                   must be a portable ASCII C identifier, but it is not."
                  name formal fn))
       (cdr-formals (strip-cars (cdr typed-formals)))
       ((when (member-equal name (symbol-name-lst cdr-formals)))
        (er-soft+ ctx t (list nil nil)
                  "The formal parameter ~x0 of the function ~x1 ~
                   has the same symbol name as ~
                   another formal parameter among ~x2; ~
                   this is disallowed, even if the package names differ."
                  formal fn cdr-formals))
       ((mv pointerp ref-type)
        (if (type-case type :pointer)
            (mv t (type-pointer->referenced type))
          (mv nil type)))
       ((when (type-case ref-type :pointer))
        (raise "Internal error: pointer type to pointer type ~x0." ref-type)
        (acl2::value (list nil nil)))
       (param (make-param-declon
               :declor (make-declor :ident (make-ident :name name)
                                    :pointerp pointerp)
               :type (atc-gen-tyspecseq ref-type)))
       ((er (list params pointers))
        (atc-gen-param-declon-list (cdr typed-formals) fn ctx state)))
    (acl2::value (list (cons param params)
                       (if pointerp
                           (acons formal (type-fix type) pointers)
                         pointers))))

  :verify-guards nil ; done below

  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)) ; for guard proofs

  (verify-guards atc-gen-param-declon-list
    :hints
    (("Goal" :in-theory (enable
                         symbol-listp-of-strip-cars-when-atc-symbol-type-alistp
                         alistp-when-atc-symbol-type-alistp-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-fun-env-thm ((fn symbolp)
                                  (proofs booleanp)
                                  (prog-const symbolp)
                                  (finfo? fun-info-optionp)
                                  (init-fun-env-thm symbolp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem saying that
          looking up a certain C function in the function environment
          yields the information for that function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to speed up the proofs
     when there is a large number of functions involved.
     A previous version of ATC was generating proofs
     that were executing function lookups,
     which worked fine for small programs,
     but not for larger programs."))
  (b* (((when (not proofs)) (mv nil nil names-to-avoid))
       ((unless (fun-infop finfo?)) (mv nil nil names-to-avoid))
       (thm-name (add-suffix fn "-FUN-ENV"))
       ((mv thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-name nil names-to-avoid wrld))
       (fn-name (symbol-name fn))
       (formula `(equal (fun-env-lookup (ident ,fn-name)
                                        (init-fun-env ,prog-const))
                        ',finfo?))
       (hints `(("Goal" :in-theory '((:e fun-env-lookup)
                                     (:e ident)
                                     ,init-fun-env-thm))))
       ((mv event &)
        (evmac-generate-defthm thm-name
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list event) thm-name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-type-predicate ((type typep))
  :returns (pred symbolp)
  :short "ACL2 predicate corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a supported integer type,
     the predicate is the recognizer of values of that type.
     For a pointer to integer type,
     the predicate is the recognizer of arrays with that element type.
     (So for a pointer type it is not a recognizer of pointer values.)
     We return @('nil') for other types."))
  (type-case
   type
   :void nil
   :char nil
   :schar 'scharp
   :uchar 'ucharp
   :sshort 'sshortp
   :ushort 'ushortp
   :sint 'sintp
   :uint 'uintp
   :slong 'slongp
   :ulong 'ulongp
   :sllong 'sllongp
   :ullong 'ullongp
   :pointer (type-case
             type.referenced
             :void nil
             :char nil
             :schar 'schar-arrayp
             :uchar 'uchar-arrayp
             :sshort 'sshort-arrayp
             :ushort 'ushort-arrayp
             :sint 'sint-arrayp
             :uint 'uint-arrayp
             :slong 'slong-arrayp
             :ulong 'ulong-arrayp
             :sllong 'sllong-arrayp
             :ullong 'ullong-arrayp
             :pointer nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-result-thm ((fn symbolp)
                               (type? type-optionp)
                               (affect symbol-listp)
                               (typed-formals atc-symbol-type-alistp)
                               (prec-fns atc-symbol-fninfo-alistp)
                               (proofs booleanp)
                               (names-to-avoid symbol-listp)
                               (wrld plist-worldp))
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem saying that
          @('fn') returns one or more results of certain C types,
          under the guard."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a local theorem for now.")
   (xdoc::p
    "The restrictions on the form of the functions that ATC translates to C
     ensures that, under the guard, these functions always return C values.
     This is fairly easy to see,
     thinking of the different allowed forms of these functions' bodies:")
   (xdoc::ul
    (xdoc::li
     "A formal parameter is constrained to be a value by the guard.")
    (xdoc::li
     "Calls of @(tsee sint-dec-const), @(tsee add-sint-sint), etc.
      are known to return values.")
    (xdoc::li
     "A @(tsee let) or @(tsee mv-let) variable is equal to a term that,
      recursively, always returns a value.")
    (xdoc::li
     "A call of a preceding function returns (a) C value(s),
      as proved by the same theorems for the preceding functions.")
    (xdoc::li
     "An @(tsee if) returns the same as its branches,
      when the test is not @(tsee mbt) or @(tsee mbt$).")
    (xdoc::li
     "An @(tsee if) return the same as its `then' branch,
      when the test is @(tsee mbt) or @(tsee mbt$),
      because the guard excludes the `else' branch from consideration.")
    (xdoc::li
     "An @(tsee mv) returns C values,
      because either they are parameters or bound variables,
      or terms that recursively return C values
      (the latter case is for non-recursive functions
      that return a non-@('void') result and also affect arrays)."))
   (xdoc::p
    "This suggests a coarse but adequate proof strategy:
     We use the theory consisting of
     the definition of @('fn'),
     the return type theorems of @(tsee sint-dec-const) and related functions,
     and the theorems about the preceding functions;
     we also add a @(':use') hint for the guard theorem of @('fn').")
   (xdoc::p
    "In the absence of @(tsee mbt) or @(tsee mbt$),
     we would not need all of the guard as hypothesis,
     but only the part that constrains the formal parameters to be C values.
     These hypotheses are needed when the function returns them;
     when instead the function returns a representation of some operation,
     e.g. a call of @(tsee sint-dec-const) or @(tsee add-sint-sint),
     these return C values unconditionally, so no hypotheses are needed.
     This is because ATC, when generating C code,
     ensures that the ACL2 terms follow the C typing rules,
     whether the terms are reachable under the guards or not.
     However, in the presence of @(tsee mbt) or @(tsee mbt$),
     we need the guard to exclude the `else' branches,
     which are otherwise unconstrained.")
   (xdoc::p
    "As explained in the user documentation,
     an ACL2 function may return a combination of
     an optional C result and zero or more affected variables or arrays.
     We collect all of them.
     The C result is determined from the optional C type of the function,
     which is @('nil') for recursive functions,
     and may or may not be @('void') for non-recursive functions.
     The affected variables are also considered as results.
     We concatenate zero or one type from @('type?')
     with zero or more types from @('affect') and @('typed-formals').
     Then we operate on the resulting list,
     which forms all the results of the function:
     the list is never empty (and ACL2 function must always return something);
     if the list is a singleton, we generate,
     as the conclusion of the theorem,
     a single type assertion for the whole function;
     if the list has multiple elements, we generate,
     as the conclusion of the theorem,
     a conjunction of type assertions
     for the @(tsee mv-nth)s of the function.")
   (xdoc::p
    "If @('fn') is recursive, we generate a hint to induct on the function.
     Since ACL2 disallows @(':use') and @(':induct') hints on the goal,
     we make the @(':use') hint a computed hint;
     we do that whether @('fn') is recursive or not, for simplicity.")
   (xdoc::p
    "Terms may appear during the proof of this theorem, where
     @(tsee mv-nth)s are applied to @(tsee list)s (i.e. @(tsee cons) nests).
     So we add the rule" (xdoc::@def "mv-nth-of-cons") " to the theory,
     in order to simplify those terms.
     We also enable the executable counterpart of @(tsee zp)
     to simplify the test in the right-hand side of that rule.")
   (xdoc::p
    "We also generate conjuncts saying that the results are not @('nil').
     Without this, some proofs fail with a subgoal saying that
     a function result is @('nil'), which is false.
     This seems to happen only with functions returning multiple results,
     where the results in question have the form @('(mv-nth ...)');
     perhaps single results are taken care by ACL2's tau system.
     So we generate these non-@('nil') theorems only for multiple results.
     These theorems have to be rewrite rules:
     with type prescription rules,
     the example theorems mentioned above still fail.
     To prove these non-@('nil') theorems,
     it seems sufficient to enable
     the executable counterparts of the integer value recognizers;
     the subgoals that arise without them have the form
     @('(<recognizer> nil)')."))
  (b* (((when (not proofs)) (mv nil nil names-to-avoid))
       (types1 (and type?
                    (not (type-case type? :void))
                    (list type?)))
       (types2 (atc-gen-fn-result-thm-aux1 affect typed-formals))
       (types (append types1 types2))
       ((unless (consp types))
        (raise "Internal error: the function ~x0 has no return types." fn)
        (mv nil nil names-to-avoid))
       (formals (formals+ fn wrld))
       (fn-call `(,fn ,@formals))
       (conclusion
        (if (consp (cdr types))
            `(and ,@(atc-gen-fn-result-thm-aux2 types 0 fn-call))
          `(,(atc-type-predicate (car types)) ,fn-call)))
       (name (add-suffix fn
                         (if (consp (cdr types))
                             "-RESULTS"
                           "-RESULT")))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (guard (untranslate (uguard+ fn wrld) t wrld))
       (formula `(implies ,guard ,conclusion))
       (hints `(("Goal"
                 ,@(and (irecursivep+ fn wrld)
                        `(:induct ,fn-call))
                 :in-theory
                 (append
                  *atc-integer-ops-1-return-rewrite-rules*
                  *atc-integer-ops-2-return-rewrite-rules*
                  *atc-integer-convs-return-rewrite-rules*
                  *atc-array-read-return-rewrite-rules*
                  '(,fn
                    ,@(atc-symbol-fninfo-alist-to-result-thms
                       prec-fns (acl2::all-fnnames (ubody+ fn wrld)))
                    sintp-of-sint-dec-const
                    sintp-of-sint-oct-const
                    sintp-of-sint-hex-const
                    uintp-of-uint-dec-const
                    uintp-of-uint-oct-const
                    uintp-of-uint-hex-const
                    slongp-of-slong-dec-const
                    slongp-of-slong-oct-const
                    slongp-of-slong-hex-const
                    ulongp-of-ulong-dec-const
                    ulongp-of-ulong-oct-const
                    ulongp-of-ulong-hex-const
                    sllongp-of-sllong-dec-const
                    sllongp-of-sllong-oct-const
                    sllongp-of-sllong-hex-const
                    ullongp-of-ullong-dec-const
                    ullongp-of-ullong-oct-const
                    ullongp-of-ullong-hex-const
                    sintp-of-sint-from-boolean
                    declar
                    assign
                    mv-nth-of-cons
                    (:e zp)
                    (:e ucharp)
                    (:e scharp)
                    (:e ushortp)
                    (:e sshortp)
                    (:e uintp)
                    (:e sintp)
                    (:e ulongp)
                    (:e slongp)
                    (:e ullongp)
                    (:e sllongp))))
                '(:use (:guard-theorem ,fn))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv (list event) name names-to-avoid))

  :prepwork

  ((define atc-gen-fn-result-thm-aux1
     ((affect symbol-listp)
      (typed-formals atc-symbol-type-alistp))
     :returns (types type-listp)
     :parents nil
     (cond ((endp affect) nil)
           (t (b* ((type (cdr (assoc-eq (car affect)
                                        typed-formals))))
                (if (typep type)
                    (cons type
                          (atc-gen-fn-result-thm-aux1 (cdr affect)
                                                      typed-formals))
                  (raise "Internal error: variable ~x0 not found in ~x1."
                         (car affect) typed-formals))))))

   (define atc-gen-fn-result-thm-aux2 ((types type-listp)
                                       (index natp)
                                       (fn-call pseudo-termp))
     :returns conjuncts
     :parents nil
     (cond ((endp types) nil)
           (t (list*
               `(,(atc-type-predicate (car types)) (mv-nth ',index ,fn-call))
               `(mv-nth ',index ,fn-call)
               (atc-gen-fn-result-thm-aux2 (cdr types)
                                           (1+ index)
                                           fn-call)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-bindings-for-cfun-formals ((formals symbol-listp)
                                           (pointers atc-symbol-type-alistp)
                                           (compst-var symbolp))
  :returns (mv (doublets doublet-listp)
               (pointer-vars symbol-symbol-alistp
                             :hyp (symbol-listp formals))
               (pointer-hyps true-listp))
  :short "Generate bindings for the formals of an ACL2 function
          that represents a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "These bindings are used in generated theorems about the C function.
     A non-recursive ACL2 target function may take arrays as parameters.
     However, the corresponding C function takes pointers
     as the corresponding parameters.
     In the correctness theorem for the function,
     we use fresh variables for the pointers,
     and bind the array variables to the arrays referenced by the pointers.
     The array variables are passed to the ACL2 functions,
     while the pointer variables are passed to @(tsee exec-fun).")
   (xdoc::p
    "As names of the pointer variables,
     we use the formal parameters that are arrays in the ACL2 function,
     and add a suffix with a dash,
     which therefore cannot conflict with other formal parameter names,
     which have portable C identifiers as names.
     We return an alist from the array formal parameters
     to the corresponding pointer variables,
     which are used for generating a part of the correctness theorem.")
   (xdoc::p
    "We also generate formulas, used as hypotheses in the generated theorems,
     about the pointer variables.
     These hypotheses say that the variables are pointers
     with the expected types."))
  (b* (((when (endp formals)) (mv nil nil nil))
       (formal (car formals))
       (type (cdr (assoc-eq formal pointers)))
       ((when (not type))
        (atc-gen-bindings-for-cfun-formals (cdr formals) pointers compst-var))
       ((unless (type-case type :pointer))
        (raise "Internal error: formal ~x0 has type ~x1." formal type)
        (mv nil nil nil))
       (var (add-suffix formal "-PTR"))
       (term `(read-array ,var ,compst-var))
       (doublet (list formal term))
       (hyps (list `(pointerp ,var)
                   `(equal (pointer->reftype ,var)
                           ',(type-pointer->referenced type))))
       ((mv more-doublets more-vars more-hyps)
        (atc-gen-bindings-for-cfun-formals (cdr formals) pointers compst-var)))
    (mv (cons doublet more-doublets)
        (acons formal var more-vars)
        (append hyps more-hyps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-final-compustate ((mod-arrs symbol-listp)
                                       (pointer-vars symbol-symbol-alistp)
                                       (compst-var symbolp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C function says that
     executing the fucntion on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     and on generic arguments
     yields an optional result (absent if the function is @('void'))
     and a computation state obtained by modifying
     one or more arrays in the computation state.
     These are the arrays affected by the loop,
     which the correctness theorem binds to the results of
     the ACL2 function that represents the C function.
     The modified computation state is expressed as
     a nest of @(tsee write-array) calls.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "The parameter @('mod-arrs') passed to this code
     consists of the formals of @('fn') that represent arrays
     affected by the body of @('fn').
     The parameter @('pointer-vars') is
     the result of @(tsee atc-gen-bindings-for-cfun-formals)
     that maps array formals of @('fn')
     to the corresponding pointer variables used by the correctness theorems.
     Thus, we go through @('mod-arrs'),
     looking up the corresponding pointer variables in @('pointer-vars'),
     and we construct each nested @(tsee write-array) call,
     which needs both a pointer and an array.
     Note that, in the correctness theorem,
     the array variables are bound to
     the possibly modified arrays returned by @('fn')."))
  (cond ((endp mod-arrs) compst-var)
        (t `(write-array ,(cdr (assoc-eq (car mod-arrs) pointer-vars))
                         ,(car mod-arrs)
                         ,(atc-gen-cfun-final-compustate (cdr mod-arrs)
                                                         pointer-vars
                                                         compst-var)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-correct-thm ((fn symbolp)
                                  (type typep)
                                  (pointers atc-symbol-type-alistp)
                                  (affect symbol-listp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (proofs booleanp)
                                  (prog-const symbolp)
                                  (fn-thms symbol-symbol-alistp)
                                  (fn-fun-env-thm symbolp)
                                  (limit pseudo-termp)
                                  (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (exported-events "A @(tsee pseudo-event-form-listp).")
               (name "A @(tsee symbolp)."))
  :mode :program
  :short "Generate the correctness theorem for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "In a computation state @('compst'),
     the execution of the C function is expressed by calling @(tsee exec-fun)
     on the name of @('fn'),
     the formals of @('fn'),
     the computation state @('compst'),
     the function environment for the translation unit,
     and a suitably large limit (more on this below).
     In this generated theorem,
     the first result of @(tsee exec-fun) is equated to
     either (i) the first (possibly only) result of
     a call of @('fn') when it represents a non-@('void') C function,
     or (ii) @('nil') when @('fn') represents a @('void') C function.
     The second result of @(tsee exec-fun) is equated to
     the computation state
     calculated by @(tsee atc-gen-cfun-final-compustate).")
   (xdoc::p
    "The function @('fn') returns
     an optional C result and zero or more modified arrays.
     If it returns a C result (i.e. if the C function is not @('void')),
     we bind a result variable to it;
     this is @('nil') if the C function is @('void').
     We also bind the formals that are arrays
     to the (other or only) results of @('fn') (if any).")
   (xdoc::p
    "The guard of @('fn') is used as hypothesis,
     along with the fact that @('compst') is a computation state.")
   (xdoc::p
    "We use a variable for the function environment,
     which we equate to the translation unit's function environment
     in a hypothesis.
     Note that, when we execute the ACL2 code in this function,
     we do not have the function environment
     of the generated translation unit yet,
     because we generate these correctness theorems
     along with the function definitions that form the translation unit
     (currently we could generate these theorems after the translation unit,
     but we prefer to do them at the same time for easier future extensions,
     in which we may generate ``smaller'' theorems,
     possibly for subterms/subexpressions/substatements).
     Thus, we cannot use a quoted constant for the function environment here.
     The reason why we introduce a variable and equate it in the hypothesis,
     as opposed to using @('(init-fun-env <program>)')
     directly as argument of @(tsee exec-fun),
     is that we want to use this theorem as a rewrite rule,
     and using a variable makes the rule easier to match with,
     in particular since the @(tsee init-fun-env) call gets rewritten
     via the theorem about @(tsee init-fun-env).")
   (xdoc::p
    "The limit passed to @(tsee exec-fun) is a variable,
     which is assumed (in a hypothesis of the generated theorem)
     to be no smaller than a value
     that is calculated by the code generation code
     as sufficient to run @(tsee exec-fun) to completion.")
   (xdoc::p
    "The proof is a symbolic execution of the generated translation unit,
     which is a constant: see @(see atc-proof-support).
     The proof is carried out in the theory that consists of
     exactly the general rules listed there,
     plus the definition of @('fn') (clearly),
     plus the theorems about the results of the functions called by @('fn'),
     plust the type prescriptions of the functions called by @('fn'),
     plus the correctness theorems of the functions called by @('fn');
     here `called' means `directly called'.
     During symbolic execution, the initial limit for @('fn')
     is progressively decremented,
     so by the time we get to functions called by @('fn')
     it will have different symbolic values from the initial variable;
     thus, we need to match that to the variable @('limit')
     in the correctness theorems for the callees,
     which are used as rewrite rules to turn calls of @(tsee exec-fun)
     into calls of the corresponding ACL2 functions.
     These will thus match the calls in the definition of @('fn'),
     and the called functions can stay disabled in the proof.
     The theorems about the called functions' results
     are needed to exclude, in the proof, the case that
     these functions return errors.
     The type prescriptions of the callable functions
     are needed to discharge some proof subgoal that arise.
     We also enable @(tsee not),
     because without it we have found at least one case
     in which some ACL2 heuristic defeats
     what should be a propositional inference;
     the issue is related to clausification,
     and enabling @(tsee not) seems to overcome the issue,
     at least in that case we found.")
   (xdoc::p
    "Furthermore, we generate a @(':use') hint
     to augment the theorem's formula with the guard theorem of @('fn'),
     with the pointer arguments replaced by the dereferenced arrays.
     This is critical to ensure that the symbolic execution of the C operators
     does not split on the error cases:
     the fact that @('fn') is guard-verified
     ensures that @(tsee add-sint-sint) and similar functions are always called
     on values such that the exact result fit into the type,
     which is the same condition under which the dynamic semantics
     does not error on the corresponding operators.")
   (xdoc::p
    "We also generate a hint to expand all lambdas (i.e. beta reduction).
     We found at least one instance in which ACL2's heuristics
     were preventing a lambda expansion that was preventing a proof.")
   (xdoc::p
    "Given that we pass correctness theorems for the called functions,
     we expect that the opener rule for @(tsee exec-fun)
     only applies to the call of the function that this theorem refers to,
     because the correctness theorems come later in the ACL2 history
     and thus are tried first.")
   (xdoc::p
    "We use @(tsee b*) bindings in parts of the theorem
     to make certain variable substitution.
     Using bindings results in more readable formulas, in general,
     than generating terms with the substitutions applied,
     particularly if the same substituted variable occurs more than once.
     With the bindings, we let ACL2 perform the substitution at proof time.")
   (xdoc::p
    "This theorem is not generated if @(':proofs') is @('nil')."))
  (b* (((when (or (not proofs)
                  (irecursivep+ fn wrld))) ; generated elsewhere
        (mv nil nil nil))
       (name (cdr (assoc-eq fn fn-thms)))
       (formals (formals+ fn wrld))
       (compst-var (genvar 'atc "COMPST" nil formals))
       (fenv-var (genvar 'atc "FENV" nil formals))
       (limit-var (genvar 'atc "LIMIT" nil formals))
       (result-var (if (type-case type :void)
                       nil
                     (genvar 'atc "RESULT" nil formals)))
       ((mv formals-binding pointer-vars pointer-hyps)
        (atc-gen-bindings-for-cfun-formals formals pointers compst-var))
       (hyps `(and (compustatep ,compst-var)
                   (equal ,fenv-var (init-fun-env ,prog-const))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   (and ,@pointer-hyps)
                   ,(untranslate (uguard+ fn wrld) nil wrld)))
       (exec-fun-args (fsublis-var-lst pointer-vars formals))
       (fn-results (append (if (type-case type :void)
                               nil
                             (list result-var))
                           affect))
       (fn-binder (if (endp (cdr fn-results))
                      (car fn-results)
                    `(mv ,@fn-results)))
       (final-compst
        (atc-gen-cfun-final-compustate affect pointer-vars compst-var))
       (concl `(equal (exec-fun (ident ,(symbol-name fn))
                                (list ,@exec-fun-args)
                                ,compst-var
                                ,fenv-var
                                ,limit-var)
                      (b* ((,fn-binder (,fn ,@formals)))
                        (mv ,result-var ,final-compst))))
       (formula `(b* (,@formals-binding) (implies ,hyps ,concl)))
       (called-fns (acl2::all-fnnames (ubody+ fn wrld)))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions
        (loop$ for called in (strip-cars prec-fns)
               collect `(:t ,called)))
       (hints `(("Goal"
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not
                               ,fn
                               ,@type-prescriptions
                               ,@result-thms
                               ,@correct-thms
                               ,@measure-thms
                               ,fn-fun-env-thm))
                 :use (:instance (:guard-theorem ,fn)
                       :extra-bindings-ok ,@formals-binding)
                 :expand (:lambdas))))
       ((mv local-event exported-event)
        (evmac-generate-defthm name
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list local-event) (list exported-event) name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-new-function-name ((fn-name stringp)
                                     (prec-fns atc-symbol-fninfo-alistp))
  :returns (mv (okp booleanp)
               (conflicting-fn symbolp))
  :short "Check that a C function name is new."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, ensure that the symbol name of @('fn')
     differs from the ones in @('prec-fns').
     It is not enough that the symbols are different:
     the symbol names must be different,
     because package names are ignored when translating to C.
     We return a boolean saying whether the check succeeds or not.
     If it does not, we return the function that causes the conflict,
     i.e. that has the same symbol name as @('fn')."))
  (atc-check-new-function-name-aux
   fn-name
   (strip-cars (atc-symbol-fninfo-alist-fix prec-fns)))

  :prepwork
  ((define atc-check-new-function-name-aux ((fn-name stringp)
                                            (fns symbol-listp))
     :returns (mv (okp booleanp)
                  (conflicting-fn symbolp))
     :parents nil
     (cond ((endp fns) (mv t nil))
           ((equal (symbol-fix fn-name)
                   (symbol-name (symbol-fix (car fns))))
            (mv nil (car fns)))
           (t (atc-check-new-function-name-aux fn-name (cdr fns)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-formal-pointerp ((formal symbolp)
                             (typed-formals atc-symbol-type-alistp))
  :returns (yes/no booleanp)
  :short "Check if a formal parameter has a C pointer type."
  (b* ((pair (assoc-eq (symbol-fix formal)
                       (atc-symbol-type-alist-fix typed-formals))))
    (and (consp pair)
         (type-case (cdr pair) :pointer)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atc-formal-pointer-listp (x typed-formals)
  :guard (and (symbol-listp x)
              (atc-symbol-type-alistp typed-formals))
  (atc-formal-pointerp x typed-formals)
  :true-listp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-find-affected ((fn symbolp)
                           (term pseudo-termp)
                           (typed-formals atc-symbol-type-alistp)
                           (ctx ctxp)
                           state)
  :returns (mv erp
               (affected symbol-listp
                         :hyp (atc-symbol-type-alistp typed-formals))
               state)
  :short "Find the variables affected by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on the body of each non-recursive target function,
     in order to determine the variables affected by it,
     according to the nomenclature in the user documentation.
     We visit the leaves of the term
     according to the @(tsee if) and @(tsee let) structure,
     and ensure that they all have the same form,
     which must be one of the following forms:")
   (xdoc::ul
    (xdoc::li
     "A formal parameter @('var') of the function that has pointer type.
      In this case, @('term') affects the list of variables @('(var)').")
    (xdoc::li
     "A term @('ret') that is not a formal parameter of pointer type.
      In this case, @('term') affects no variables.")
    (xdoc::li
     "A term @('(mv var1 ... varn)') where each @('vari') is
      a formal parameter of the function that has pointer type.
      In this case, @('term') affects
      the list of variables @('(var1 ... varn)').")
    (xdoc::li
     "A term @('(mv ret var1 ... varn)') where each @('vari') is
      a formal parameter of the function that has pointer type
      and @('ret') is not.
      In this case, @('term') affects
      the list of variables @('(var1 ... varn)')."))
   (xdoc::p
    "In checking that the terms at the leaves have the same form,
     we allow @('ret') to vary, but the other parts must coincide.")
   (xdoc::p
    "When we encounter @(tsee if)s with @(tsee mbt) or @(tsee mbt$) tests,
     we recursively process the `then' branch, skipping the `else' branch.
     This is because only the `then' branch represents C code."))
  (b* (((mv okp test then else) (fty-check-if-call term))
       ((when okp)
        (b* (((mv mbtp &) (check-mbt-call test))
             ((when mbtp) (atc-find-affected fn then typed-formals ctx state))
             ((mv mbt$p &) (check-mbt$-call test))
             ((when mbt$p) (atc-find-affected fn then typed-formals ctx state))
             ((er then-affected) (atc-find-affected fn then typed-formals
                                                    ctx state))
             ((er else-affected) (atc-find-affected fn else typed-formals
                                                    ctx state)))
          (if (equal then-affected else-affected)
              (acl2::value then-affected)
            (er-soft+ ctx t nil
                      "When generating code for function ~x0, ~
                       an IF branch affects variables ~x1, ~
                       while the other branch affects variables ~x2: ~
                       this is disallowed."
                      fn then-affected else-affected))))
       ((mv okp & body &) (fty-check-lambda-call term))
       ((when okp)
        (atc-find-affected fn body typed-formals ctx state))
       ((when (pseudo-term-case term :var))
        (b* ((var (pseudo-term-var->name term)))
          (if (atc-formal-pointerp var typed-formals)
              (acl2::value (list var))
            (acl2::value nil))))
       ((mv okp terms) (fty-check-list-call term))
       ((when okp)
        (cond ((and (symbol-listp terms)
                    (atc-formal-pointer-listp terms typed-formals))
               (acl2::value terms))
              ((and (symbol-listp (cdr terms))
                    (atc-formal-pointer-listp (cdr terms) typed-formals))
               (acl2::value (cdr terms)))
              (t (er-soft+ ctx t nil
                           "When generating code for function ~x0, ~
                            a term ~x1 was encountered that ~
                            returns multiple values but they, ~
                            or at least all of them except the first one, ~
                            are not all formal parameters of ~x0 ~
                            of pointer type."
                           fn term)))))
    (acl2::value nil))
  :measure (pseudo-term-count term)
  :prepwork
  ((local (in-theory
           (enable symbol-listp-of-strip-cars-when-atc-symbol-type-alistp)))
   (local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-declon ((fn symbolp)
                            (prec-fns atc-symbol-fninfo-alistp)
                            (proofs booleanp)
                            (prog-const symbolp)
                            (init-fun-env-thm symbolp)
                            (fn-thms symbol-symbol-alistp)
                            (print evmac-input-print-p)
                            (names-to-avoid symbol-listp)
                            (ctx ctxp)
                            state)
  :returns (mv erp
               (val "A @('(tuple (ext ext-declonp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-prec-fns atc-symbol-fninfo-alistp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C external declaration (a function definition)
          from a non-recursive ACL2 function, with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return local and exported events for the theorems about
     the correctness of the C function definition.")
   (xdoc::p
    "We extend the alist @('prec-fns') with information about the function.")
   (xdoc::p
    "We use the type of the value returned by the statement for the body
     as the result type of the C function.")
   (xdoc::p
    "For the limit, we need 1 to go from @(tsee exec-fun) to @(tsee exec-stmt),
     another 1 from there to @(tsee exec-block-item-list)
     in the @(':compound') case,
     and then we use the limit for the block."))
  (b* ((name (symbol-name fn))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t nil
                  "The symbol name ~s0 of the function ~x1 ~
                   must be a portable ASCII C identifier, but it is not."
                  name fn))
       ((mv okp conflicting-fn) (atc-check-new-function-name name prec-fns))
       ((when (not okp))
        (er-soft+ ctx t nil
                  "The symbol name ~s0 of the function ~x1 ~
                   must be distinct from the symbol names of ~
                   the oher ACL2 functions translated to C functions, ~
                   but the function ~x2 has the same symbol name."
                  name fn conflicting-fn))
       (wrld (w state))
       ((er typed-formals) (atc-typed-formals fn ctx state))
       ((er (list params pointers)) (atc-gen-param-declon-list typed-formals
                                                               fn
                                                               ctx
                                                               state))
       (body (ubody+ fn wrld))
       ((er affect) (atc-find-affected fn body typed-formals ctx state))
       ((unless (subsetp-eq affect (strip-cars pointers)))
        (er-soft+ ctx t nil
                  "The variables ~x0 affected by the body of ~x1 ~
                   must all have pointer types, ~
                   but some of them are not among ~
                   the formals ~x2 with pointer types."
                  affect fn (strip-cars pointers)))
       ((er (list items type limit)) (atc-gen-stmt body
                                                   nil
                                                   (list typed-formals)
                                                   nil
                                                   affect
                                                   fn
                                                   prec-fns
                                                   proofs
                                                   ctx
                                                   state))
       ((when (and (type-case type :void)
                   (not affect)))
        (acl2::value
         (raise "Internal error: ~
                 the function ~x0 returns void and affects no variables."
                fn)))
       ((unless (or (type-integerp type)
                    (type-case type :void)))
        (acl2::value
         (raise "Internal error: ~
                 the function ~x0 has return type ~x1."
                fn type)))
       (fundef (make-fundef :result (atc-gen-tyspecseq type)
                            :name (make-ident :name name)
                            :params params
                            :body (stmt-compound items)))
       (ext (ext-declon-fundef fundef))
       (finfo (fun-info-from-fundef fundef))
       (limit `(binary-+ '2 ,limit))
       ((mv fn-fun-env-events
            fn-fun-env-thm
            names-to-avoid)
        (atc-gen-cfun-fun-env-thm
         fn proofs prog-const finfo init-fun-env-thm names-to-avoid wrld))
       ((mv fn-result-events
            fn-result-thm
            names-to-avoid)
        (atc-gen-fn-result-thm fn type affect typed-formals prec-fns
                               proofs names-to-avoid wrld))
       ((mv fn-correct-local-events
            fn-correct-exported-events
            fn-correct-thm)
        (atc-gen-cfun-correct-thm fn type pointers affect prec-fns proofs
                                  prog-const fn-thms fn-fun-env-thm
                                  limit wrld))
       (progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the proofs for ~x0..." ',fn))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (local-events (append progress-start?
                             fn-fun-env-events
                             fn-result-events
                             fn-correct-local-events
                             progress-end?))
       (exported-events fn-correct-exported-events)
       (info (make-atc-fn-info
              :out-type type
              :in-types (strip-cdrs typed-formals)
              :loop? nil
              :affect affect
              :result-thm fn-result-thm
              :correct-thm fn-correct-thm
              :measure-nat-thm nil
              :fun-env-thm fn-fun-env-thm
              :limit limit)))
    (acl2::value (list ext
                       local-events
                       exported-events
                       (acons fn info prec-fns)
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-measure-fn ((fn symbolp)
                                 (names-to-avoid symbol-listp)
                                 (wrld plist-worldp))
  :guard (irecursivep+ fn wrld)
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (formals "A @(tsee symbol-listp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a measure function for a recursive target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem for a loop involves
     the measure of the loop function.
     The measure may be a complex term.
     An early version of ATC was using the measure terms
     directly in the generated theorems,
     but that caused proof failures sometimes,
     due to ACL2 sometimes modifying those measure terms during a proof
     (e.g. due to equalities involving measure subterms
     arising from case analyses):
     after the terms were modified,
     some of the generated theorems about the measure terms
     no longer apply, making the proof fail.
     Thus, we ``protect'' the measure terms from modifications
     by generating functions for them,
     and using those functions in the generated theorems.")
   (xdoc::p
    "The code of this ACL2 function generates a measure function
     for the recursive target function @('fn').
     The funcion is not guard-verified,
     because its is only logical.
     It is important that we take,
     as formal parameters of the generated measure function,
     only the variables that occur in the measure term.
     This facilitates the generation of
     the loop function's termination theorem
     expressed over the  generated measure function."))
  (b* ((name (packn-pos (list 'measure-of- fn) fn))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name 'function names-to-avoid wrld))
       (measure-term (measure+ fn wrld))
       (measure-vars (all-vars measure-term))
       ((mv & event)
        (evmac-generate-defun
         name
         :formals measure-vars
         :body (untranslate measure-term nil wrld)
         :verify-guards nil
         :enable nil)))
    (mv event name measure-vars names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-loop-tthm-formula
  :short "Generate the formula for the loop termination theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained from the loop function's termination theorem,
     transformed as follows.")
   (xdoc::p
    "The @(tsee o<) relation is replaced with @(tsee <).
     This is justified by the fact that the measure yields a natural number,
     as guaranteed by the applicability condition.")
   (xdoc::p
    "Furthermore, the measure term is replaced
     with a call of the generated measure function.
     More precisely, this is done in every term of the form @('(o< A B)')
     (at the same replacing @(tsee o<) with @(tsee <) as mentioned above),
     where we expect @('B') to be the measure term,
     and @('A') to be the instantiation of the measure term
     to one of the recursive calls of the loop function.
     We replace @('B') with a generic call of the measure function,
     and @('A') with an instantiated call of the measure function;
     we obtain the instantiation by matching @('B') to @('A').
     It is not yet clear whether this approach will work in all cases."))
  :mode :program

  (define atc-gen-loop-tthm-formula ((term pseudo-termp)
                                     (fn symbolp)
                                     (measure-of-fn symbolp)
                                     (measure-formals symbol-listp)
                                     (ctx ctxp)
                                     state)
    :returns (mv erp
                 (new-term "A @(tsee pseudo-termp).")
                 state)
    (b* (((when (variablep term)) (acl2::value term))
         ((when (fquotep term)) (acl2::value term))
         (term-fn (ffn-symb term))
         ((when (eq term-fn 'o<))
          (b* ((meas-gen (fargn term 2))
               (meas-inst (fargn term 1))
               ((mv okp subst) (acl2::one-way-unify meas-gen meas-inst))
               ((when (not okp))
                (er-soft+ ctx t nil
                          "Failed to match istantiated measure ~x0 ~
                           to general measure ~x1 of function ~x2."
                          meas-inst meas-gen fn))
               (measure-args (fty-fsublis-var-lst subst measure-formals)))
            (acl2::value
             `(< (,measure-of-fn ,@measure-args)
                 (,measure-of-fn ,@measure-formals)))))
         ((er new-args) (atc-gen-loop-tthm-formula-lst (fargs term)
                                                       fn
                                                       measure-of-fn
                                                       measure-formals
                                                       ctx
                                                       state)))
      (acl2::value (fcons-term term-fn new-args))))

  (define atc-gen-loop-tthm-formula-lst ((terms pseudo-term-listp)
                                         (fn symbolp)
                                         (measure-of-fn symbolp)
                                         (measure-formals symbol-listp)
                                         (ctx ctxp)
                                         state)
    :returns (mv erp
                 (new-terms "A @(tsee pseudo-term-listp).")
                 state)
    (b* (((when (endp terms)) (acl2::value nil))
         ((er new-term) (atc-gen-loop-tthm-formula (car terms)
                                                   fn
                                                   measure-of-fn
                                                   measure-formals
                                                   ctx
                                                   state))
         ((er new-terms) (atc-gen-loop-tthm-formula-lst (cdr terms)
                                                        fn
                                                        measure-of-fn
                                                        measure-formals
                                                        ctx
                                                        state)))
      (acl2::value (cons new-term new-terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-exec-stmt-while-for-loop ((fn symbolp)
                                          (loop-stmt stmtp)
                                          (prog-const symbolp)
                                          (names-to-avoid symbol-listp)
                                          (wrld plist-worldp))
  :guard (irecursivep+ fn wrld)
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (exec-stmt-while-for-fn "A @(tsee symbolp).")
               (exec-stmt-while-for-fn-thm "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a version of @(tsee exec-stmt-while)
          specialized to the loop represented by @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem for a loop says that
     the execution of the loop (via @(tsee exec-stmt-while))
     is suitably equivalent to
     the corresponding ACL2 recursive function @('fn').
     The theorem is proved by induction, unsurprisingly.
     However, due to the form in which the function appears in the theorem,
     namely that the function is not applied to ACL2 variables,
     we cannot use the function's induction scheme.
     But we cannot readily use
     the induction scheme of the execution functions
     of the C dynamic semantics,
     or at least it looks cumbersome to do so,
     because there are several of them, mutually recursive.")
   (xdoc::p
    "What we really need is an induction scheme related to the loop.
     Thus we introduce a local function that is like @(tsee exec-stmt-while)
     but specialized to the loop generated from @('fn');
     this function is singly recursive, providing the needed induction scheme.
     The function does not need to be guard-verified,
     because it is only used for logic.
     We also generate a theorem saying that this new function
     is equivalent to @(tsee exec-stmt-while) applied to the loop;
     this is critical, because eventually the proof must be
     about the execution functions of the C dynamic semantics.
     For robustness, the termination proof for this new function,
     and the proof of the associated theorem,
     are carried out in exactly specified theories
     that should always work."))
  (b* ((loop-test (stmt-while->test loop-stmt))
       (loop-body (stmt-while->body loop-stmt))
       (exec-stmt-while-for-fn
        (packn-pos (list 'exec-stmt-while-for- fn) fn))
       ((mv exec-stmt-while-for-fn names-to-avoid)
        (fresh-logical-name-with-$s-suffix exec-stmt-while-for-fn
                                           'function
                                           names-to-avoid
                                           wrld))
       (exec-stmt-while-for-fn-body
        `(b* ((fenv (init-fun-env ,prog-const))
              ((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
              (continuep (exec-test (exec-expr-pure ',loop-test compst)))
              ((when (errorp continuep)) (mv continuep (compustate-fix compst)))
              ((when (not continuep)) (mv nil (compustate-fix compst)))
              ((mv val? compst) (exec-stmt ',loop-body compst fenv (1- limit)))
              ((when (errorp val?)) (mv val? compst))
              ((when (valuep val?)) (mv val? compst)))
           (,exec-stmt-while-for-fn compst (1- limit))))
       (exec-stmt-while-for-fn-hints
        '(("Goal" :in-theory '(acl2::zp-compound-recognizer
                               nfix
                               natp
                               o-p
                               o-finp
                               o<))))
       ((mv exec-stmt-while-for-fn-event &)
        (evmac-generate-defun
         exec-stmt-while-for-fn
         :formals (list 'compst 'limit)
         :body exec-stmt-while-for-fn-body
         :measure '(nfix limit)
         :well-founded-relation 'o<
         :hints exec-stmt-while-for-fn-hints
         :verify-guards nil
         :enable nil))
       (exec-stmt-while-for-fn-thm
        (add-suffix exec-stmt-while-for-fn "-TO-EXEC-STMT-WHILE"))
       ((mv exec-stmt-while-for-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix exec-stmt-while-for-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((mv exec-stmt-while-for-fn-thm-event &)
        (evmac-generate-defthm
         exec-stmt-while-for-fn-thm
         :formula `(equal (,exec-stmt-while-for-fn compst limit)
                          (exec-stmt-while ',loop-test
                                           ',loop-body
                                           compst
                                           (init-fun-env ,prog-const)
                                           limit))
         :rule-classes nil
         :hints `(("Goal" :in-theory '(,exec-stmt-while-for-fn
                                       exec-stmt-while))))))
    (mv (list exec-stmt-while-for-fn-event
              exec-stmt-while-for-fn-thm-event)
        exec-stmt-while-for-fn
        exec-stmt-while-for-fn-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-measure-thm ((fn symbolp)
                                  (fn-appconds symbol-symbol-alistp)
                                  (appcond-thms keyword-symbol-alistp)
                                  (measure-of-fn symbolp)
                                  (measure-formals symbol-listp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :guard (irecursivep+ fn wrld)
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate type prescription theorem asserting that
          the measure of the recursive function @('fn')
          yields a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like the applicability condition,
     except that it uses the generated measure function
     (to treat the measure as a black box,
     as discussed in @(tsee atc-gen-loop-measure-fn)),
     and that it is a type prescription rule
     (which seems needed, as opposed a rewrite rule,
     based on proof experiments)."))
  (b* ((appcond-thm
        (cdr (assoc-eq (cdr (assoc-eq fn fn-appconds)) appcond-thms)))
       (natp-of-measure-of-fn-thm
        (packn-pos (list 'natp-of-measure-of- fn) fn))
       ((mv natp-of-measure-of-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix natp-of-measure-of-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((mv natp-of-measure-of-fn-thm-event &)
        (evmac-generate-defthm
         natp-of-measure-of-fn-thm
         :formula `(natp (,measure-of-fn ,@measure-formals))
         :rule-classes :type-prescription
         :enable nil
         :hints `(("Goal"
                   :in-theory '(,measure-of-fn)
                   :use ,appcond-thm)))))
    (mv natp-of-measure-of-fn-thm-event
        natp-of-measure-of-fn-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-termination-thm ((fn symbolp)
                                      (measure-of-fn symbolp)
                                      (measure-formals symbol-listp)
                                      (natp-of-measure-of-fn-thm symbolp)
                                      (names-to-avoid symbol-listp)
                                      (ctx ctxp)
                                      state)
  :guard (irecursivep+ fn (w state))
  :returns (mv erp
               (val "A @('(tuple (event pseudo-event-formp)
                                 (name symbolp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate the version of the termination theorem
          tailored to the limits and measure function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a local theorem that is
     just like the termination theorem of the function
     except that @(tsee o<) is replaced with @(tsee <),
     and that the measure terms are abstracted to
     calls of the generated measure functions.
     The theorem is proved using the fact that
     the measure yields a natural number,
     which means that @(tsee o<) reduces to @(tsee <) (see above).
     The purpose of this variant of the termination theorem
     is to help establish the induction hypothesis
     in the loop correctness theorem, as explained below."))
  (b* ((wrld (w state))
       (termination-of-fn-thm
        (packn-pos (list 'termination-of- fn) fn))
       ((mv termination-of-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix termination-of-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((er tthm-formula)
        (atc-gen-loop-tthm-formula (termination-theorem fn wrld)
                                   fn
                                   measure-of-fn
                                   measure-formals
                                   ctx
                                   state))
       ((mv termination-of-fn-thm-event &)
        (evmac-generate-defthm
         termination-of-fn-thm
         :formula tthm-formula
         :rule-classes nil
         :hints `(("Goal"
                   :use ((:termination-theorem ,fn)
                         ,natp-of-measure-of-fn-thm)
                   :in-theory '(,measure-of-fn
                                acl2::natp-compound-recognizer
                                o-p
                                o-finp
                                o<))))))
    (acl2::value
     (list termination-of-fn-thm-event
           termination-of-fn-thm
           names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-loop-body-term-subst
  :short "In a term that represents the body of a loop,
          replace each recursive call with
          a term that returns the affected variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is needed to express the correctness theorem for the loop body.
     The theorem needs to relate the execution of the loop body statement
     to the ACL2 term that represents it.
     However, the latter has recursive calls in it,
     which we therefore replace with terms
     that just return the affected variables.
     This ACL2 function does that.
     This gives us the appropriate ACL2 term
     to relate to the execution of the loop body statement,
     because the execution of the loop body statement
     just ends with the affected variables,
     i.e. it does not go back to the loop,
     which would be the equivalent of making the recursive call.")
   (xdoc::p
    "Note that we apply the substitution without regard to lambda variables,
     because we only use this ACL2 function on terms
     that satisfy the restrictions for loop body terms
     described in the user documentation.
     In particular, this means that the recursive calls
     are always on the formals of the loop function,
     and the affected variables also always have the same meaning."))

  (define atc-loop-body-term-subst ((term pseudo-termp)
                                    (fn symbolp)
                                    (affect symbol-listp))
    :returns (new-term pseudo-termp)
    :parents nil
    (b* (((when (member-eq (pseudo-term-kind term) '(:null :quote :var)))
          (pseudo-term-fix term))
         (fn/lam (pseudo-term-call->fn term))
         ((when (eq fn/lam fn))
          (if (consp (cdr affect))
              `(mv ,@(acl2::symbol-list-fix affect))
            (symbol-fix (car affect))))
         (args (pseudo-term-call->args term))
         (new-args (atc-loop-body-term-subst-lst args fn affect))
         (new-fn/lam (if (pseudo-lambda-p fn/lam)
                         (pseudo-lambda (pseudo-lambda->formals fn/lam)
                                        (atc-loop-body-term-subst
                                         (pseudo-lambda->body fn/lam)
                                         fn affect))
                       fn/lam)))
      (pseudo-term-call new-fn/lam new-args))
    :measure (pseudo-term-count term))

  (define atc-loop-body-term-subst-lst ((terms pseudo-term-listp)
                                        (fn symbolp)
                                        (affect symbol-listp))
    :returns (new-terms pseudo-term-listp)
    :parents nil
    (cond ((endp terms) nil)
          (t (cons (atc-loop-body-term-subst (car terms) fn affect)
                   (atc-loop-body-term-subst-lst (cdr terms) fn affect))))
    :measure (pseudo-term-list-count terms)
    ///
    (defret len-of-atc-loop-body-term-subst-lst
      (equal (len new-terms)
             (len terms))))

  :ruler-extenders :all

  :returns-hints nil ; for speed

  :verify-guards nil ; done below
  ///
  (verify-guards atc-loop-body-term-subst
    :hints (("Goal" :in-theory (enable pseudo-fn-args-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-bindings-for-loop-formals ((formals symbol-listp)
                                           (pointers atc-symbol-type-alistp)
                                           (compst-var symbolp))
  :returns (mv (doublets doublet-listp)
               (pointer-hyps true-listp))
  :short "Generate bindings for the formals of an ACL2 function
          that represents a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "These bindings are used in generated theorems about the loop.
     The formals of a loop function correspond to
     variables in the computation state
     or arrays referenced by variables in the computation state.
     The two cases are distinguished by whether
     the formal is a pointer or not.")
   (xdoc::p
    "We also generate formulas, used as hypotheses in the generated theorems,
     about the pointers that appear in the bindings.
     These hypotheses say that the variables are pointers
     with the expected types."))
  (b* (((when (endp formals)) (mv nil nil))
       (formal (car formals))
       (type (cdr (assoc-eq formal pointers)))
       ((when (and type
                   (not (type-case type :pointer))))
        (raise "Internal error: pointer ~x0 has type ~x1." formal type)
        (mv nil nil))
       (term `(read-var (ident ,(symbol-name formal)) ,compst-var))
       ((mv term hyps)
        (if (assoc-eq formal pointers)
            (mv `(read-array ,term ,compst-var)
                (list `(pointerp ,term)
                      `(equal (pointer->reftype ,term)
                              ',(type-pointer->referenced type))))
          (mv term nil)))
       (doublet (list formal term))
       ((mv more-doublets more-hyps)
        (atc-gen-bindings-for-loop-formals (cdr formals) pointers compst-var)))
    (mv (cons doublet more-doublets)
        (append hyps more-hyps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-test-correct-thm ((fn symbolp)
                                       (pointers atc-symbol-type-alistp)
                                       (loop-test exprp)
                                       (test-term pseudo-termp)
                                       (fn-thms symbol-symbol-alistp)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (correct-test-thm "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the correctness theorem for the test of a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a step towards generating more modular and controlled loop proofs.
     The hints are more than needed for now,
     as they include rules about statement execution,
     which does not apply here.
     We will make the hints more nuanced later."))
  (b* ((correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-test-thm (add-suffix correct-thm "-TEST"))
       ((mv correct-test-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-test-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar 'atc "COMPST" nil formals))
       ((mv formals-binding pointer-hyps)
        (atc-gen-bindings-for-loop-formals formals pointers compst-var))
       (hyps `(and (compustatep ,compst-var)
                   (not (equal (compustate-frames-number ,compst-var) 0))
                   (and ,@pointer-hyps)
                   ,(untranslate (uguard+ fn wrld) nil wrld)))
       (concl `(equal (exec-test (exec-expr-pure ',loop-test ,compst-var))
                      ,test-term))
       (formula `(b* (,@formals-binding) (implies ,hyps ,concl)))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not))
                 :use ((:instance (:guard-theorem ,fn)
                        :extra-bindings-ok ,@formals-binding))
                 :expand :lambdas)))
       ((mv correct-test-thm-event &)
        (evmac-generate-defthm correct-test-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list correct-test-thm-event)
        correct-test-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-final-compustate ((mod-vars symbol-listp)
                                       (compst-var symbolp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C loop says that
     executing the loop on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     yields a computation state obtained by modifying
     one or more variables in the computation state.
     These are the variables affected by the loop,
     which the correctness theorem binds to the results of the loop function,
     and which have corresponding named variables in the computation state.
     The modified computation state is expressed as
     a nest of @(tsee write-var) calls.
     This ACL2 code here generates that nest."))
  (cond ((endp mod-vars) compst-var)
        (t `(write-var (ident ,(symbol-name (car mod-vars)))
                       ,(car mod-vars)
                       ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                       compst-var)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-body-correct-thm ((fn symbolp)
                                       (pointers atc-symbol-type-alistp)
                                       (affect symbol-listp)
                                       (loop-body stmtp)
                                       (test-term pseudo-termp)
                                       (body-term pseudo-termp)
                                       (prec-fns atc-symbol-fninfo-alistp)
                                       (prog-const symbolp)
                                       (fn-thms symbol-symbol-alistp)
                                       (limit pseudo-termp)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (correct-body-thm "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the correctness theorem for the body of a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the purpose of making the proofs generated by ATC more modular,
     we generate a separate local theorem for
     the correctness of each generated loop body;
     we plan to change the loop correctness theorem
     to make use of this theorem,
     instead of proving the whole loop, including its body."))
  (b* ((correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-body-thm (add-suffix correct-thm "-BODY"))
       ((mv correct-body-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-body-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar 'atc "COMPST" nil formals))
       (fenv-var (genvar 'atc "FENV" nil formals))
       (limit-var (genvar 'atc "LIMIT" nil formals))
       ((mv formals-binding pointer-hyps)
        (atc-gen-bindings-for-loop-formals formals pointers compst-var))
       (hyps `(and (compustatep ,compst-var)
                   (not (equal (compustate-frames-number ,compst-var) 0))
                   (equal ,fenv-var (init-fun-env ,prog-const))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   (and ,@pointer-hyps)
                   ,(untranslate (uguard+ fn wrld) nil wrld)
                   ,(untranslate test-term nil wrld)))
       (affect-binder (if (endp (cdr affect))
                          (car affect)
                        `(mv ,@affect)))
       (final-compst (atc-gen-loop-final-compustate affect compst-var))
       (body-term (atc-loop-body-term-subst body-term fn affect))
       (concl `(equal (exec-stmt ',loop-body ,compst-var ,fenv-var ,limit-var)
                      (b* ((,affect-binder ,body-term))
                        (mv nil ,final-compst))))
       (formula `(b* (,@formals-binding) (implies ,hyps ,concl)))
       (called-fns (acl2::all-fnnames (ubody+ fn wrld)))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not
                               ,@type-prescriptions
                               ,@result-thms
                               ,@correct-thms
                               ,@measure-thms))
                 :use ((:instance (:guard-theorem ,fn)
                        :extra-bindings-ok ,@formals-binding))
                 :expand :lambdas)))
       ((mv correct-body-thm-event &)
        (evmac-generate-defthm correct-body-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list correct-body-thm-event)
        correct-body-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-correct-thm ((fn symbolp)
                                  (pointers atc-symbol-type-alistp)
                                  (affect symbol-listp)
                                  (loop-test exprp)
                                  (loop-body stmtp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prog-const symbolp)
                                  (fn-thms symbol-symbol-alistp)
                                  (fn-result-thm symbolp)
                                  (exec-stmt-while-for-fn symbolp)
                                  (exec-stmt-while-for-fn-thm symbolp)
                                  (termination-of-fn-thm symbolp)
                                  (natp-of-measure-of-fn-thm symbolp)
                                  (correct-test-thm symbolp)
                                  (correct-body-thm symbolp)
                                  (limit pseudo-termp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :guard (irecursivep+ fn wrld)
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (exported-events "A @(tsee pseudo-event-form-listp).")
               (natp-of-measure-of-fn-thm "A @(tsee symbolp).")
               (fn-correct-thm "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the correctness theorem for a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate the correctness theorem as a lemma first,
     then the actual theorem.
     The only difference between the two is that
     the lemma uses the specialization of @(tsee exec-stmt-while)
     that is generated as discussed above,
     while the theorem uses the general @(tsee exec-stmt-while);
     the reason is so we can have the right induction, as discussed above.
     As explained shortly,
     the formula involves (some of) the loop function's formals,
     so we take those into account to generate variables for
     the computation state, the function environment, and the limit.
     The hypotheses include the guard of the loop function,
     but we need to replace any pointers with their dereferenced arrays,
     and in addition we need to replace the parameters of the loop function
     with @(tsee read-var) calls that read the corresponding variables.
     The other hypotheses are the same as in @(tsee atc-gen-cfun-correct-thm),
     with the addition of a hypothesis that
     the number of frames in the computation state is not zero;
     this is always the case when executing a loop.
     The arguments of the loop function call are obtained by
     replacing its formals with the corresponding @(tsee read-var) calls.
     The lemma is proved via proof builder instructions,
     by first applying induction
     and then calling the prover on all the induction subgoals.
     For robustness, first we set the theory to contain
     just the specialized @(tsee exec-stmt-while),
     then we apply induction, which therefore must be on that function.
     The hints for the subgoals are for the symbolic execution,
     similar to the ones in @(tsee atc-gen-cfun-correct-thm),
     where the @(':expand') hint applies to the loop function,
     for robustness (as ACL2's heuristics sometimes prevent
     the opening of recursive function definitions,
     but here we know that we always want to open it).
     The hints also include:
     (i) the return value theorem of the loop function,
     which is reasonable since the function is recursive,
     and so it is called inside its body;
     (ii) the definition of the specialized @(tsee exec-stmt-while);
     (iii) the rule saying that the measure yields a natural number; and
     (iv) the termination theorem of the loop function, suitably instantiated.
     We also pass the theorem asserting the correctness of the loop body:
     this is expected to be used as a rewrite rule for the body,
     making its symbolic execution unnecessary here;
     this is a step towards more modular and controlled proofs.
     Given the correctness lemma, the correctness theorem is easily proved,
     via the lemma and the generate theorem that equates
     the specialized @(tsee exec-stmt-while) to the general one."))
  (b* ((correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-lemma (add-suffix correct-thm "-LEMMA"))
       ((mv correct-lemma names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-lemma
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar 'atc "COMPST" nil formals))
       (fenv-var (genvar 'atc "FENV" nil formals))
       (limit-var (genvar 'atc "LIMIT" nil formals))
       ((mv formals-binding pointer-hyps)
        (atc-gen-bindings-for-loop-formals formals pointers compst-var))
       (hyps `(and (compustatep ,compst-var)
                   (not (equal (compustate-frames-number ,compst-var) 0))
                   (equal ,fenv-var (init-fun-env ,prog-const))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   (and ,@pointer-hyps)
                   ,(untranslate (uguard+ fn wrld) nil wrld)))
       (affect-binder (if (endp (cdr affect))
                          (car affect)
                        `(mv ,@affect)))
       (final-compst (atc-gen-loop-final-compustate affect compst-var))
       (concl-lemma `(equal (,exec-stmt-while-for-fn ,compst-var ,limit-var)
                            (b* ((,affect-binder (,fn ,@formals)))
                              (mv nil ,final-compst))))
       (concl-thm `(equal (exec-stmt-while ',loop-test
                                           ',loop-body
                                           ,compst-var
                                           ,fenv-var
                                           ,limit-var)
                          (b* ((,affect-binder (,fn ,@formals)))
                            (mv nil ,final-compst))))
       (formula-lemma `(b* (,@formals-binding) (implies ,hyps ,concl-lemma)))
       (formula-thm `(b* (,@formals-binding) (implies ,hyps ,concl-thm)))
       (called-fns (acl2::all-fnnames (ubody+ fn wrld)))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (result-thms (cons fn-result-thm result-thms))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (lemma-hints `(("Goal"
                       :do-not-induct t
                       :in-theory (union-theories
                                   (theory 'atc-all-rules)
                                   '(not
                                     ,exec-stmt-while-for-fn
                                     ,@type-prescriptions
                                     ,@result-thms
                                     ,@correct-thms
                                     ,@measure-thms
                                     ,natp-of-measure-of-fn-thm
                                     ,correct-test-thm
                                     ,correct-body-thm))
                       :use ((:instance (:guard-theorem ,fn)
                              :extra-bindings-ok ,@formals-binding)
                             (:instance ,termination-of-fn-thm
                              :extra-bindings-ok ,@formals-binding))
                       :expand (:lambdas
                                (,fn ,@(fsublis-var-lst
                                        (acl2::doublets-to-alist
                                         formals-binding)
                                        formals))))))
       (lemma-instructions
        `((:in-theory '(,exec-stmt-while-for-fn))
          (:induct (,exec-stmt-while-for-fn ,compst-var ,limit-var))
          (:repeat (:prove :hints ,lemma-hints))))
       (thm-hints `(("Goal"
                     :in-theory nil
                     :use (,correct-lemma ,exec-stmt-while-for-fn-thm))))
       ((mv correct-lemma-event &)
        (evmac-generate-defthm correct-lemma
                               :formula formula-lemma
                               :instructions lemma-instructions
                               :enable nil))
       ((mv correct-thm-local-event correct-thm-exported-event)
        (evmac-generate-defthm correct-thm
                               :formula formula-thm
                               :hints thm-hints
                               :enable nil))
       (local-events (list correct-lemma-event
                           correct-thm-local-event))
       (exported-events (list correct-thm-exported-event)))
    (mv local-events
        exported-events
        natp-of-measure-of-fn-thm
        correct-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop ((fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      (proofs booleanp)
                      (prog-const symbolp)
                      (fn-thms symbol-symbol-alistp)
                      (fn-appconds symbol-symbol-alistp)
                      (appcond-thms keyword-symbol-alistp)
                      (print evmac-input-print-p)
                      (names-to-avoid symbol-listp)
                      (ctx ctxp)
                      state)
  :guard (irecursivep+ fn (w state))
  :returns (mv erp
               (val "A @('(tuple (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-prec-fns atc-symbol-fninfo-alistp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C loop from a recursive ACL2 function,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called if @('fn') is a recursive target function.
     We process the function body as a loop term,
     and update the @('prec-fns') alist with information about the function.")
   (xdoc::p
    "We also generate the measure function for @('fn') here.
     See @(tsee atc-gen-loop-measure-fn).")
   (xdoc::p
    "No C external declaration is generated for this function,
     because this function just represents a loop used in oher functions."))
  (b* ((wrld (w state))
       ((mv measure-of-fn-event measure-of-fn measure-formals names-to-avoid)
        (atc-gen-loop-measure-fn fn names-to-avoid wrld))
       ((er typed-formals) (atc-typed-formals fn ctx state))
       ((er (list & pointers)) (atc-gen-param-declon-list typed-formals
                                                          fn
                                                          ctx
                                                          state))
       (body (ubody+ fn wrld))
       ((er (list loop-stmt
                  test-term
                  body-term
                  loop-affect
                  body-limit
                  loop-limit))
        (atc-gen-loop-stmt body
                           (list typed-formals)
                           fn
                           measure-of-fn
                           measure-formals
                           prec-fns
                           proofs
                           ctx
                           state))
       ((mv fn-result-events
            fn-result-thm
            names-to-avoid)
        (atc-gen-fn-result-thm fn nil loop-affect typed-formals prec-fns
                               proofs names-to-avoid wrld))
       (loop-test (stmt-while->test loop-stmt))
       (loop-body (stmt-while->body loop-stmt))
       ((mv exec-stmt-while-events
            exec-stmt-while-for-fn
            exec-stmt-while-for-fn-thm
            names-to-avoid)
        (atc-gen-exec-stmt-while-for-loop fn
                                          loop-stmt
                                          prog-const
                                          names-to-avoid
                                          wrld))
       ((mv natp-of-measure-of-fn-thm-event
            natp-of-measure-of-fn-thm
            names-to-avoid)
        (atc-gen-loop-measure-thm fn
                                  fn-appconds
                                  appcond-thms
                                  measure-of-fn
                                  measure-formals
                                  names-to-avoid
                                  wrld))
       ((er (list termination-of-fn-thm-event
                  termination-of-fn-thm))
        (atc-gen-loop-termination-thm fn
                                      measure-of-fn
                                      measure-formals
                                      natp-of-measure-of-fn-thm
                                      names-to-avoid
                                      ctx
                                      state))
       ((mv test-local-events
            correct-test-thm
            names-to-avoid)
        (atc-gen-loop-test-correct-thm fn
                                       pointers
                                       loop-test
                                       test-term
                                       fn-thms
                                       names-to-avoid
                                       wrld))
       ((mv body-local-events
            correct-body-thm
            names-to-avoid)
        (atc-gen-loop-body-correct-thm fn
                                       pointers
                                       loop-affect
                                       loop-body
                                       test-term
                                       body-term
                                       prec-fns
                                       prog-const
                                       fn-thms
                                       body-limit
                                       names-to-avoid
                                       wrld))
       ((mv correct-local-events
            correct-exported-events
            natp-of-measure-of-fn-thm
            fn-correct-thm
            names-to-avoid)
        (atc-gen-loop-correct-thm fn
                                  pointers
                                  loop-affect
                                  loop-test
                                  loop-body
                                  prec-fns
                                  prog-const
                                  fn-thms
                                  fn-result-thm
                                  exec-stmt-while-for-fn
                                  exec-stmt-while-for-fn-thm
                                  termination-of-fn-thm
                                  natp-of-measure-of-fn-thm
                                  correct-test-thm
                                  correct-body-thm
                                  loop-limit
                                  names-to-avoid
                                  wrld))
       (progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the proofs for ~x0..." ',fn))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (local-events (and proofs
                          (append progress-start?
                                  (list measure-of-fn-event)
                                  fn-result-events
                                  exec-stmt-while-events
                                  (list natp-of-measure-of-fn-thm-event)
                                  (list termination-of-fn-thm-event)
                                  test-local-events
                                  body-local-events
                                  correct-local-events
                                  progress-end?)))
       (exported-events (and proofs
                             (append correct-exported-events)))
       (info (make-atc-fn-info :out-type nil
                               :in-types (strip-cdrs typed-formals)
                               :loop? loop-stmt
                               :affect loop-affect
                               :result-thm fn-result-thm
                               :correct-thm fn-correct-thm
                               :measure-nat-thm natp-of-measure-of-fn-thm
                               :fun-env-thm nil
                               :limit loop-limit)))
    (acl2::value (list local-events
                       exported-events
                       (acons fn info prec-fns)
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-declon-list ((fns symbol-listp)
                                 (prec-fns atc-symbol-fninfo-alistp)
                                 (proofs booleanp)
                                 (prog-const symbolp)
                                 (init-fun-env-thm symbolp)
                                 (fn-thms symbol-symbol-alistp)
                                 (fn-appconds symbol-symbol-alistp)
                                 (appcond-thms keyword-symbol-alistp)
                                 (print evmac-input-print-p)
                                 (names-to-avoid symbol-listp)
                                 (ctx ctxp)
                                 state)
  :returns (mv erp
               (val "A @('(tuple (exts ext-declon-listp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a list of C external declarations (function definitions)
          from non-recursive ACL2 functions,
          including generating C loops from recursive ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After we process the first function @('fn') in @('fns'),
     we use the extended @('prec-fns') for the subsequent functions.")
   (xdoc::p
    "We treat recursive and non-recursive functions differently."))
  (b* (((when (endp fns)) (acl2::value (list nil nil nil names-to-avoid)))
       ((cons fn rest-fns) fns)
       ((er (list exts local-events exported-events prec-fns names-to-avoid))
        (if (irecursivep+ fn (w state))
            (b* (((mv erp
                      (list local-events
                            exported-events
                            prec-fns
                            names-to-avoid)
                      state)
                  (atc-gen-loop fn prec-fns proofs prog-const
                                fn-thms fn-appconds appcond-thms
                                print names-to-avoid ctx state))
                 ((when erp) (mv erp (list nil nil nil nil) state)))
              (acl2::value (list nil
                                 local-events
                                 exported-events
                                 prec-fns
                                 names-to-avoid)))
          (b* (((mv erp
                    (list
                     ext local-events exported-events prec-fns names-to-avoid)
                    state)
                (atc-gen-ext-declon fn prec-fns proofs
                                    prog-const init-fun-env-thm fn-thms
                                    print names-to-avoid ctx state))
               ((when erp) (mv erp (list nil nil nil nil) state)))
            (acl2::value (list (list ext)
                               local-events
                               exported-events
                               prec-fns
                               names-to-avoid)))))
       ((er
         (list more-exts more-local-events more-exported-events names-to-avoid))
        (atc-gen-ext-declon-list rest-fns prec-fns proofs
                                 prog-const init-fun-env-thm fn-thms
                                 fn-appconds appcond-thms
                                 print names-to-avoid ctx state)))
    (acl2::value (list (append exts more-exts)
                       (append local-events more-local-events)
                       (append exported-events more-exported-events)
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-prog-const ((prog-const symbolp)
                            (tunit transunitp)
                            (print evmac-input-print-p))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the named constant for the abstract syntax tree
          of the generated C code (i.e. translation unit)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is not generated if @(':proofs') is @('nil')."))
  (b* ((progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the named constant..."))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (defconst-event `(defconst ,prog-const ',tunit))
       (local-event `(progn ,@progress-start?
                            (local ,defconst-event)
                            ,@progress-end?)))
    (mv local-event defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-wf-thm ((proofs booleanp)
                        (prog-const symbolp)
                        (wf-thm symbolp)
                        (print evmac-input-print-p))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (exported-events "A @(tsee pseudo-event-form-listp)."))
  :mode :program
  :short "Generate the theorem asserting
          the static well-formedness of the generated C code
          (referenced as the named constant)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this is a ground theorem,
     we expect that it should be easily provable
     using just the executable counterpart of @(tsee check-transunit),
     which is an executable function.")
   (xdoc::p
    "We generate singleton lists of events if @(':proofs') is @('t'),
     empty lists otherwise."))
  (b* (((unless proofs) (mv nil nil))
       ((mv local-event exported-event)
        (evmac-generate-defthm
         wf-thm
         :formula `(equal (check-transunit ,prog-const) :wellformed)
         :hints '(("Goal" :in-theory '((:e check-transunit))))
         :enable nil))
       (progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the well-formedness theorem..."))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (local-event `(progn ,@progress-start?
                            ,local-event
                            ,@progress-end?)))
    (mv (list local-event)
        (list exported-event))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-init-fun-env-thm ((init-fun-env-thm symbolp)
                                  (proofs booleanp)
                                  (prog-const symbolp)
                                  (tunit transunitp))
  :returns (local-events pseudo-event-form-listp)
  :short "Generate the theorem asserting that
          applying @(tsee init-fun-env) to the translation unit
          gives the corresponding function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rationale for generating this theorem
     is explained in @(tsee atc-gen-transunit)."))
  (b* (((unless proofs) nil)
       (fenv (init-fun-env tunit))
       (formula `(equal (init-fun-env ,prog-const)
                        ',fenv))
       (hints '(("Goal" :in-theory '((:e init-fun-env)))))
       ((mv event &)
        (evmac-generate-defthm init-fun-env-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (list event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-transunit ((fn1...fnp symbol-listp)
                           (proofs booleanp)
                           (prog-const symbolp)
                           (wf-thm symbolp)
                           (fn-thms symbol-symbol-alistp)
                           (print evmac-input-print-p)
                           (names-to-avoid symbol-listp)
                           (ctx ctxp)
                           state)
  :returns (mv erp
               (val "A @('(tuple (tunit transunitp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C translation unit from the ACL2 target functions,
          and accompanying event."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to speed up the proofs of
     the generated theorems for the function environment
     for relatively large C programs,
     we generate a theorem to ``cache''
     the result of calling @(tsee init-fun-env)
     on the generated translation unit,
     to avoid recomputing that for every function environment theorem.
     We need to generate the name of this (local) theorem
     before generating the function environment theorems,
     so that those theorems can use the name of this theorem in the hints;
     but we can only generate the theorem
     after generating the translation unit.
     So first we generate the name,
     then we generate the translation unit,
     and then we generate the theorem;
     however, in the generated events,
     we put that theorem before the ones for the functions."))
  (b* (((mv appcond-local-events fn-appconds appcond-thms names-to-avoid)
        (if proofs
            (b* (((mv appconds fn-appconds)
                  (atc-gen-appconds fn1...fnp (w state)))
                 ((mv appcond-events appcond-thms & names-to-avoid)
                  (evmac-appcond-theorem-list appconds nil names-to-avoid
                                              print ctx state)))
              (mv appcond-events fn-appconds appcond-thms names-to-avoid))
          (mv nil nil nil nil)))
       ((mv wf-thm-local-events wf-thm-exported-events)
        (atc-gen-wf-thm proofs prog-const wf-thm print))
       (init-fun-env-thm (add-suffix prog-const "-FUN-ENV"))
       ((mv init-fun-env-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix init-fun-env-thm
                                           nil
                                           names-to-avoid
                                           (w state)))
       ((er
         (list exts fn-thm-local-events fn-thm-exported-events names-to-avoid))
        (atc-gen-ext-declon-list fn1...fnp nil proofs
                                 prog-const init-fun-env-thm
                                 fn-thms fn-appconds appcond-thms
                                 print names-to-avoid ctx state))
       (tunit (make-transunit :declons exts))
       (local-init-fun-env-events (atc-gen-init-fun-env-thm init-fun-env-thm
                                                            proofs
                                                            prog-const
                                                            tunit))
       ((mv local-const-event exported-const-event)
        (if proofs
            (atc-gen-prog-const prog-const tunit print)
          (mv nil nil)))
       (local-events (append appcond-local-events
                             (and proofs (list local-const-event))
                             wf-thm-local-events
                             local-init-fun-env-events
                             fn-thm-local-events))
       (exported-events (append (and proofs (list exported-const-event))
                                wf-thm-exported-events
                                fn-thm-exported-events)))
    (acl2::value (list tunit
                       local-events
                       exported-events
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file ((tunit transunitp) (output-file stringp) state)
  :returns (mv erp val state)
  :mode :program
  :short "Pretty-print the generated C code (i.e. translation unit)
          to the output file."
  (b* ((lines (pprint-transunit tunit)))
    (pprinted-lines-to-file lines output-file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file-event ((tunit transunitp)
                            (output-file stringp)
                            (print evmac-input-print-p)
                            state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :short "Event to pretty-print the generated C code to the output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to run @(tsee atc-gen-file)
     after the constant and theorem events have been submitted.
     This function generates an event form
     that is put (by @(tsee atc-gen-everything))
     after the constant and theorem events.
     When the events are submitted to and processed by ACL2,
     we get to this file generation event
     only if the previous events are successful.
     This is a sort of safety/security constraint:
     do not even generate the file, unless it is correct.")
   (xdoc::p
    "If @(':print') is at @(':info') or @(':all'),
     we also generate events to print progress messages,
     as done with the constant and theorem events.")
   (xdoc::p
    "In order to generate an embedded event form for file generation,
     we generate a @(tsee make-event) whose argument generates the file.
     The argument must also return an embedded event form,
     so we use @(tsee value-triple) with @(':invisible'),
     so there is no extra screen output.
     This is a ``dummy'' event, it is not supposed to do anything:
     it is the execution of the @(tsee make-event) argument
     that matters, because it generates the file.
     In essence, we use @(tsee make-event) to turn a computation
     (the one that generates the file)
     into an event.
     But we cannot use just @(tsee value-triple)
     because our computation returns an error triple."))
  (b* ((progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the file..." ',output-file))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (file-gen-event
        `(make-event
          (b* (((er &) (atc-gen-file ',tunit ,output-file state)))
            (acl2::value '(value-triple :invisible))))))
    (acl2::value `(progn ,@progress-start?
                         ,file-gen-event
                         ,@progress-end?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-print-result ((events pseudo-event-form-listp)
                              (output-file stringp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the events to print the results of ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only if @(':print') is at least @(':result')."))
  (append (atc-gen-print-result-aux events)
          (list `(cw-event "~%File ~s0.~%" ,output-file)))
  :prepwork
  ((define atc-gen-print-result-aux ((events pseudo-event-form-listp))
     :returns (events pseudo-event-form-listp)
     (cond ((endp events) nil)
           (t (cons `(cw-event "~%~x0~|" ',(car events))
                    (atc-gen-print-result-aux (cdr events))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-everything ((fn1...fnp symbol-listp)
                            (output-file stringp)
                            (proofs booleanp)
                            (prog-const symbolp)
                            (wf-thm symbolp)
                            (fn-thms symbol-symbol-alistp)
                            (print evmac-input-print-p)
                            (call pseudo-event-formp)
                            (ctx ctxp)
                            state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Generate the file and the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We locally install the ``trivial ancestor check'' from the library.
     We found at least a case in which ACL2's default heuristic ancestor check
     prevented a valid functional correctness theorem from being proved.
     Since by construction the symbolic execution shoud always terminate,
     it does not seem like ACL2's heuristic ancestor check
     would ever be helpful (if this turns out to be wrong, we will re-evaluate).
     Thus, we locally install the simpler ancestor check.")
   (xdoc::p
    "We also (locally, implicitly) allow variables to be ignored.
     Ignored variables may arise in the correctness theorems for loop bodies:
     @(tsee atc-loop-body-term-subst) replaces recursive calls,
     which include all the formals of the loop function,
     with just the affected variables, which may be a subset of the formals;
     if the call is the body of a @(tsee let),
     the formals that are not affected then become ignored."))
  (b* ((names-to-avoid (list* prog-const wf-thm (strip-cdrs fn-thms)))
       ((er (list tunit local-events exported-events &))
        (atc-gen-transunit fn1...fnp proofs prog-const wf-thm fn-thms
                           print names-to-avoid ctx state))
       ((er file-gen-event) (atc-gen-file-event tunit output-file print state))
       (print-events (and (evmac-input-print->= print :result)
                          (atc-gen-print-result exported-events output-file)))
       (encapsulate
         `(encapsulate ()
            (evmac-prepare-proofs)
            (local (acl2::use-trivial-ancestors-check))
            (set-ignore-ok t)
            ,@local-events
            ,@exported-events
            ,file-gen-event))
       (encapsulate+ (restore-output? (eq print :all) encapsulate))
       (info (make-atc-call-info :encapsulate encapsulate))
       (table-event (atc-table-record-event call info)))
    (acl2::value `(progn ,encapsulate+
                         ,table-event
                         ,@print-events
                         (value-triple :invisible)))))
