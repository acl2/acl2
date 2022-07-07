; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "pretty-printer" :ttags ((:open-output-channel!)))
(include-book "dynamic-semantics")
(include-book "shallow-embedding")
(include-book "proof-support")
(include-book "table")
(include-book "term-checkers")

(include-book "fty-pseudo-terms")

(include-book "../language/static-semantics")

(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/std/strings/strtok-bang" :dir :system)
(include-book "kestrel/std/system/add-suffix-to-fn-lst" :dir :system)
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
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "projects/apply/loop" :dir :system))
(local (in-theory (disable acl2::loop-book-theory)))

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
     the translation is relatively straightforward, by design.")
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

(define atc-gen-appconds ((targets symbol-listp) (wrld plist-worldp))
  :returns (mv (appconds "A @(tsee evmac-appcond-listp).")
               (fn-appconds "A @(tsee symbol-symbol-alistp)."))
  :mode :program
  :short "Generate the applicability conditions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also return an alist from the recursive target functions
     to the corresponding applicability condition names.")
   (xdoc::p
    "We skip over @(tsee defstruct) names and non-recursive function names."))
  (b* (((when (endp targets)) (mv nil nil))
       (target (car targets))
       ((when (not (function-symbolp target wrld)))
        (atc-gen-appconds (cdr targets) wrld))
       ((when (not (irecursivep+ target wrld)))
        (atc-gen-appconds (cdr targets) wrld))
       (meas (measure+ target wrld))
       (name (packn-pos (list 'natp-of-measure-of- target) :keyword))
       (formula (untranslate `(natp ,meas) nil wrld))
       (appcond (make-evmac-appcond :name name :formula formula))
       ((mv appconds fn-appconds) (atc-gen-appconds (cdr targets) wrld)))
    (mv (cons appcond appconds)
        (acons target name fn-appconds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-symbol-type-alist
  :short "Fixtype of alists from symbols to types."
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
     the name of the locally generated theorem about the function result(s);
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
  :short "Project the function environment theorems
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

(fty::defprod atc-tag-info
  :short "Fixtype of information associated to
          an ACL2 @(tsee defstruct) symbol translated to a C structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the information in the @(tsee defstruct) table
     plus some additional information that is more specific to ATC
     than to @(tsee defstruct), which is part of the shallow embedding.
     This additional information consists of:")
   (xdoc::ul
    (xdoc::li
     "The names of the theorems generated by ATC
      for rewriting calls of @(tsee exec-memberp)
      to calls of @(tsee defstruct) readers;
      see @(tsee atc-gen-tag-member-read-all-thms).")
    (xdoc::li
     "The names of the theorems generated by ATC
      for rewriting calls of @(tsee exec-expr-asg)
      with a @(':memberp') left expression
      to calls of @(tsee defstruct) writers;
      see @(tsee atc-gen-tag-member-write-all-thms)."))
   (xdoc::p
    "The latter theorems depend on
     @(tsee exec-memberp) and @(tsee exec-expr-asg),
     so they are not generated by @(tsee defstruct)
     to avoid having @(tsee defstruct) depend on
     those functions from the dynamic semantics."))
  ((defstruct defstruct-info)
   (member-read-thms symbol-list)
   (member-write-thms symbol-listp))
  :pred atc-tag-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-string-taginfo-alist
  :short "Fixtype of alists from symbols to tag information."
  :key-type string
  :val-type atc-tag-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred atc-string-taginfo-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-recognizers
  ((prec-tags atc-string-taginfo-alistp))
  :returns (recognizers symbol-listp)
  :short "Project the recognizers out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (recog (defstruct-info->recognizer (atc-tag-info->defstruct info)))
       (recogs (atc-string-taginfo-alist-to-recognizers (cdr prec-tags))))
    (cons recog recogs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-readers
  ((prec-tags atc-string-taginfo-alistp))
  :returns (readers symbol-listp)
  :short "Project the readers out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (readers (atc-string-taginfo-alist-to-readers-aux
                 (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-readers (atc-string-taginfo-alist-to-readers (cdr prec-tags))))
    (append readers more-readers))
  :prepwork
  ((define atc-string-taginfo-alist-to-readers-aux
     ((members defstruct-member-info-listp))
     :returns (readers symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (readers (defstruct-member-info->readers (car members)))
          (more-readers (atc-string-taginfo-alist-to-readers-aux
                         (cdr members))))
       (append readers more-readers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-reader-return-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the return type theorems
          for structure readers
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-string-taginfo-alist-to-reader-return-thms-aux
              (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-thms
        (atc-string-taginfo-alist-to-reader-return-thms (cdr prec-tags))))
    (append thms more-thms))
  :prepwork
  ((define atc-string-taginfo-alist-to-reader-return-thms-aux
     ((members defstruct-member-info-listp))
     :returns (reader-return-thms symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (thms (defstruct-member-info->reader-return-thms (car members)))
          (more-thms
           (atc-string-taginfo-alist-to-reader-return-thms-aux (cdr members))))
       (append thms more-thms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-writer-return-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the return type theorems
          for structure writers
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-string-taginfo-alist-to-writer-return-thms-aux
              (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-thms
        (atc-string-taginfo-alist-to-writer-return-thms (cdr prec-tags))))
    (append thms more-thms))
  :prepwork
  ((define atc-string-taginfo-alist-to-writer-return-thms-aux
     ((members defstruct-member-info-listp))
     :returns (writer-return-thms symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (thms (defstruct-member-info->writer-return-thms (car members)))
          (more-thms
           (atc-string-taginfo-alist-to-writer-return-thms-aux (cdr members))))
       (append thms more-thms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-not-error-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the non-error theorems out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->not-error-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-not-error-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-valuep-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee valuep) theorems out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->valuep-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-valuep-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-value-kind-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee value-kind) theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->value-kind-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-value-kind-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-type-of-value-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee type-of-value) theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->type-of-value-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-type-of-value-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-member-read-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee exec-memberp) theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-tag-info->member-read-thms info))
       (more-thms
        (atc-string-taginfo-alist-to-member-read-thms (cdr prec-tags))))
    (append thms more-thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-member-write-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee exec-expr-asg) with @(':memberp') theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-tag-info->member-write-thms info))
       (more-thms
        (atc-string-taginfo-alist-to-member-write-thms (cdr prec-tags))))
    (append thms more-thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-type-to-recognizer ((type typep) (wrld plist-worldp))
  :returns (recognizer symbolp)
  :short "ACL2 recognizer corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a supported integer type,
     the predicate is the recognizer of values of that type.
     For a pointer to integer type,
     the predicate is the recognizer of arrays with that element type.
     For a pointer to structure type,
     the predicate is the recognizer of structures of that type.
     This is based on our current ACL2 representation of C types,
     which may be extended in the future;
     note that, in the current representation,
     the predicate corresponding to each type
     is never a recognizer of pointer values.
     We return @('nil') for other types."))
  (type-case
   type
   :void (raise "Internal error: type ~x0." type)
   :char (raise "Internal error: type ~x0." type)
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
   :struct (raise "Internal error: type ~x0." type)
   :pointer (type-case
             type.to
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
             :struct (b* ((info (defstruct-table-lookup
                                  (ident->name type.to.tag)
                                  wrld))
                          ((unless info)
                           (raise "Internal error: no recognizer for ~x0."
                                  type)))
                       (defstruct-info->recognizer info))
             :pointer (raise "Internal error: type ~x0." type)
             :array (raise "Internal error: type ~x0." type))
   :array (raise "Internal error: type ~x0." type))
  :hooks (:fix))

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
       (in-type (fixtype-to-integer-type type))
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
       (out-type (fixtype-to-integer-type etype))
       ((when (not out-type)) (no))
       (in-type1 (type-pointer out-type))
       (in-type2 (fixtype-to-integer-type itype))
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
    "where @('<arr>') is a variable of pointer type to an integer type,
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
       (sub-type (fixtype-to-integer-type itype))
       ((unless sub-type) (no))
       (elem-type (fixtype-to-integer-type etype))
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

(define atc-check-struct-read-scalar ((term pseudo-termp)
                                      (prec-tags atc-string-taginfo-alistp))
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp)
               (tag identp)
               (member identp)
               (mem-type typep))
  :short "Check if a term may represent a structure read
          of a scalar member."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C structure read operations for scalar members,
     we return the argument term, the tag name, and the name of the member.
     The C structure type of the reader must be in the preceding tags;
     we consult the alist to retrieve the relevant information.")
   (xdoc::p
    "We also return the type of the member.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((acl2::fun (no))
        (mv nil nil (irr-ident) (irr-ident) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp struct tag read member) (atc-check-symbol-4part term.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name read) "READ")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq term.fn (defstruct-info->readers info))) (no))
       (tag (defstruct-info->tag info))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (member (symbol-name member))
       ((unless (ident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (list-lenp 1 term.args)) (no))
       (arg (car term.args)))
    (mv t arg tag member mem-type))
  ///

  (defret pseudo-term-count-of-atc-check-struct-read-scalar
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-read-array ((term pseudo-termp)
                                     (prec-tags atc-string-taginfo-alistp))
  :returns (mv (yes/no booleanp)
               (index pseudo-termp)
               (struct pseudo-termp)
               (tag identp)
               (member identp)
               (index-type typep)
               (elem-type typep))
  :short "Check if a term may represent a structure read
          of an element of an array member."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C structure read operations for array members,
     we return the argument terms (index and structure),
     the tag name, and the name of the member.
     The C structure type of the reader must be in the preceding tags;
     we consult the alist to retrieve the relevant information.")
   (xdoc::p
    "We also return the types of the index and the array element.")
   (xdoc::p
    "If the term does not have the right form,
     we return an indication of failure."))
  (b* (((acl2::fun (no))
        (mv nil nil nil (irr-ident) (irr-ident) (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp struct tag read member type) (atc-check-symbol-5part term.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name read) "READ")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq term.fn (defstruct-info->readers info))) (no))
       (tag (defstruct-info->tag info))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (member (symbol-name member))
       ((unless (ident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (type-case mem-type :array)) (no))
       (elem-type (type-array->of mem-type))
       (type (pack type))
       (index-type (fixtype-to-integer-type type))
       ((unless index-type) (no))
       ((unless (list-lenp 2 term.args)) (no))
       (index (first term.args))
       (struct (second term.args)))
    (mv t index struct tag member index-type elem-type))
  ///

  (defret pseudo-term-count-of-atc-check-struct-read-array-index
    (implies yes/no
             (< (pseudo-term-count index)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-struct-read-array-struct
    (implies yes/no
             (< (pseudo-term-count struct)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-write-scalar ((var symbolp)
                                       (val pseudo-termp)
                                       (prec-tags atc-string-taginfo-alistp))
  :returns (mv (yes/no booleanp)
               (mem pseudo-termp)
               (tag identp)
               (member identp)
               (mem-type typep))
  :short "Check if a @(tsee let) binding may represent a structure write
          of a scalar member."
  :long
  (xdoc::topstring
   (xdoc::p
    "A structure write of a scalar member,
     i.e. an assignment to a scalar structure member
     via a pointer to the structure,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<struct> (struct-<tag>-write-<member> <mem> <struct>))) ...)")
   (xdoc::p
    "where @('<struct>') is a variable of pointer type to a structure type,
     which must occur identically as
     both the @(tsee let) variable
     and as the last argument of @('struct-<tag>-write-<member>'),
     @('<mem>') is an expression that yields the member value to write,
     and @('...') represents the code that follows the assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the member argument is returned for further processing.
     We also return the tag, the member name, and the member type.")
   (xdoc::p
    "Similarly to @(tsee atc-check-struct-read-scalar),
     we consult the @('prec-tags') alist,
     which must contain the C structure type associated to the writer."))
  (b* (((acl2::fun (no)) (mv nil nil (irr-ident) (irr-ident) (irr-type)))
       ((unless (pseudo-term-case val :fncall)) (no))
       ((pseudo-term-fncall val) val)
       ((mv okp struct tag write member) (atc-check-symbol-4part val.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name write) "WRITE")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq val.fn (defstruct-info->writers info))) (no))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (tag (defstruct-info->tag info))
       (member (symbol-name member))
       ((unless (ident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (list-lenp 2 val.args)) (no))
       (mem (first val.args))
       (struct (second val.args)))
    (if (equal struct var)
        (mv t mem tag member mem-type)
      (no)))
  ///

  (defret pseudo-term-count-of-atc-check-struct-write-scalar
    (implies yes/no
             (< (pseudo-term-count mem)
                (pseudo-term-count val)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-write-array ((var symbolp)
                                      (val pseudo-termp)
                                      (prec-tags atc-string-taginfo-alistp))
  :returns (mv (yes/no booleanp)
               (index pseudo-termp)
               (elem pseudo-termp)
               (tag identp)
               (member identp)
               (index-type typep)
               (elem-type typep))
  :short "Check if a @(tsee let) binding may represent a structure write
          of an element of an array member."
  :long
  (xdoc::topstring
   (xdoc::p
    "A structure write of an element of an array member,
     i.e. an assignment to an element of an array structure member
     via a pointer to the structure,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<struct>
            (struct-<tag>-write-<member>-<type> <index> <elem> <struct>)))
       ...)")
   (xdoc::p
    "where @('<struct>') is a variable of pointer type to a structure type,
     which must occur identically as
     both the @(tsee let) variable
     and as the last argument of @('struct-<tag>-write-<member>'),
     @('<index>') is an expression that yields an integer used as array index,
     @('<elem>') is an expression that yields the member element value to write,
     and @('...') represents the code that follows the assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the index and member argument
     are returned for further processing.
     We also return
     the tag, the member name, the index type, and the member type.")
   (xdoc::p
    "Similarly to @(tsee atc-check-struct-read-array),
     we consult the @('prec-tags') alist,
     which must contain the C structure type associated to the writer."))
  (b* (((acl2::fun (no))
        (mv nil nil nil (irr-ident) (irr-ident) (irr-type) (irr-type)))
       ((unless (pseudo-term-case val :fncall)) (no))
       ((pseudo-term-fncall val) val)
       ((mv okp struct tag write member type) (atc-check-symbol-5part val.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name write) "WRITE")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq val.fn (defstruct-info->writers info))) (no))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (tag (defstruct-info->tag info))
       (member (symbol-name member))
       ((unless (ident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (type-case mem-type :array)) (no))
       (elem-type (type-array->of mem-type))
       (type (pack type))
       (index-type (fixtype-to-integer-type type))
       ((unless index-type) (no))
       ((unless (list-lenp 3 val.args)) (no))
       (index (first val.args))
       (mem (second val.args))
       (struct (third val.args)))
    (if (equal struct var)
        (mv t index mem tag member index-type elem-type)
      (no)))
  ///

  (defret pseudo-term-count-of-atc-check-struct-write-array-index
    (implies yes/no
             (< (pseudo-term-count index)
                (pseudo-term-count val)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-struct-write-array-elem
    (implies yes/no
             (< (pseudo-term-count elem)
                (pseudo-term-count val)))
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
     where this call term occurs."))
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

(define atc-check-cfun-call-args ((formals symbol-listp)
                                  (in-types type-listp)
                                  (args pseudo-term-listp))
  :returns (yes/no booleanp)
  :short "Check the arguments of a call to a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after @(tsee atc-check-cfun-call),
     if the latter is successful.
     As stated in the user documentation of ATC,
     calls of non-recursive target functions must satisfy the property that
     the argument for a formal of pointer type must be identical to the formal.
     This is because these arguments and formals
     represent (pointers to) arrays and structures,
     and thus they must be passed around exactly by their name,
     similarly to stobjs in ACL2.
     This code checks the condition."))
  (b* (((when (endp formals))
        (cond ((consp in-types)
               (raise "Internal error: extra types ~x0." in-types))
              ((consp args)
               (raise "Internal error: extra arguments ~x0." args))
              (t t)))
       ((when (or (endp in-types)
                  (endp args)))
        (raise "Internal error: extra formals ~x0." formals))
       (formal (car formals))
       (in-type (car in-types))
       (arg (car args))
       ((unless (type-case in-type :pointer))
        (atc-check-cfun-call-args (cdr formals) (cdr in-types) (cdr args)))
       ((unless (eq formal arg)) nil))
    (atc-check-cfun-call-args (cdr formals) (cdr in-types) (cdr args))))

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
     the argument types,
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

(define atc-check-let ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (var symbolp)
               (val pseudo-termp)
               (body pseudo-termp)
               (wrapper? symbolp))
  :short "Check if a term may be a @(tsee let) statement term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The forms of these terms are described in the user documentation.")
   (xdoc::p
    "Here we recognize and decompose statement terms that are @(tsee let)s.
     In translated form, @('(let ((var val)) body)')
     is @('((lambda (var) body) val)').
     However, if @('body') has other free variables in addition to @('var'),
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

(define atc-check-declar/assign-n ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (wrapper symbolp)
               (n natp)
               (wrapped pseudo-termp))
  :short "Check if a term is a call of @('declar<n>') or @('assign<n>')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the macros described in @(see atc-let-designations).
     These macros expand to")
   (xdoc::codeblock
    "(mv-let (*1 *2 ... *<n>)"
    "  <wrapped>"
    "  (mv (<wrapper> *1) *2 ... *<n>))")
   (xdoc::p
    "which in translated terms looks like")
   (xdoc::codeblock
    "((lambda (mv)"
    "         ((lambda (*1 *2 ... *<n>)"
    "                  (cons ((<wrapper> *1) (cons *2 ... (cons *<n> 'nil)))))"
    "          (mv-nth '0 mv)"
    "          (mv-nth '1 mv)"
    "          ..."
    "          (mv-nth '<n-1> mv)))"
    " <wrapped>)")
   (xdoc::p
    "So here we attempt to recognize this for of translated terms.
     If successful, we return @('<wrapper>'), @('<n>'), and @('<wrapped>')."))
  (b* (((mv okp mv-var vars indices hides wrapped body)
        (fty-check-mv-let-call term))
       ((unless okp) (mv nil nil 0 nil))
       ((unless (eq mv-var 'mv)) (mv nil nil 0 nil))
       (n (len vars))
       ((unless (>= n 2)) (mv nil nil 0 nil))
       ((unless (equal vars
                       (loop$ for i of-type integer from 1 to n
                              collect (pack '* i))))
        (mv nil nil 0 nil))
       ((unless (equal indices
                       (loop$ for i of-type integer from 0 to (1- n)
                              collect i)))
        (mv nil nil 0 nil))
       ((unless (equal hides (repeat n nil)))
        (mv nil nil 0 nil))
       ((mv okp terms) (fty-check-list-call body))
       ((unless okp) (mv nil nil 0 nil))
       ((unless (equal (len terms) n)) (mv nil nil 0 nil))
       ((cons term terms) terms)
       ((unless (pseudo-term-case term :fncall)) (mv nil nil 0 nil))
       (wrapper (pseudo-term-fncall->fn term))
       ((unless (member-eq wrapper '(declar assign))) (mv nil nil 0 nil))
       ((unless (equal (pseudo-term-fncall->args term) (list '*1)))
        (mv nil nil 0 nil))
       ((unless (equal terms
                       (loop$ for i of-type integer from 2 to n
                              collect (pack '* i))))
        (mv nil nil 0 nil)))
    (mv t wrapper n wrapped))
  :prepwork ((local (in-theory (enable acl2::loop-book-theory))))
  ///

  (defret pseudo-term-count-of-atc-check-declar/assign-n-wrapped
    (implies yes/no
             (< (pseudo-term-count wrapped)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-mv-let ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (var? symbolp)
               (vars symbol-listp)
               (indices nat-listp)
               (val pseudo-termp)
               (body pseudo-termp)
               (wrapper? symbolp))
  :short "Check if a term may be an @(tsee mv-let) statement term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The forms of these terms are described in the user documentation.")
   (xdoc::p
    "First, we check if the term is an @(tsee mv-let),
     obtaining variables, indices, value term, and body term.
     Then we check whether the value term is
     a @('declar<n>') or an @('assign<n>'):
     in this case, we return the first variable
     separately from the other variables,
     and we also return
     the corresponding @(tsee declar) or @(tsee assign) wrapper.
     Otherwise, we return all the variables together,
     with @('nil') as the @('var?') and @('wrapper?') results."))
  (b* (((mv okp & vars indices & val body) (fty-check-mv-let-call term))
       ((when (not okp)) (mv nil nil nil nil nil nil nil))
       ((mv okp wrapper & wrapped) (atc-check-declar/assign-n val))
       ((when (not okp)) (mv t nil vars indices val body nil)))
    (mv t (car vars) (cdr vars) indices wrapped body wrapper))

  :prepwork
  ((defrulel verify-guards-lemma
     (implies (symbol-listp x)
              (iff (consp x) x))))

  ///

  (defret pseudo-term-count-of-atc-check-mv-let-val
    (implies yes/no
             (< (pseudo-term-count val)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-mv-let-body
    (implies yes/no
             (< (pseudo-term-count body)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-pure/bool
  :short "Mutually recursive ACL2 functions to
          generate pure C expressions from ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for pure expression terms
     and for expression terms returning booleans (which are always pure)."))

  (define atc-gen-expr-pure ((term pseudo-termp)
                             (inscope atc-symbol-type-alist-listp)
                             (prec-tags atc-string-taginfo-alistp)
                             (fn symbolp)
                             (ctx ctxp)
                             state)
    :returns (mv erp
                 (val (tuple (expr exprp)
                             (type typep)
                             val))
                 state)
    :parents (atc-event-and-code-generation atc-gen-expr-pure/bool)
    :short "Generate a C expression from an ACL2 term
            that must be a pure expression term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time,
       we check that the term is a pure expression term,
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
      "If the term fits the pattern of an array read,
       we translate it to an array subscripting expression
       on the recursively generated expressions.
       The type is the array's element type.")
     (xdoc::p
      "If the term fits the pattern of a structure scalar read,
       we translate it to a structure pointer member expression
       on the recursively generated expression.
       The type is the member's type.")
     (xdoc::p
      "If the term fits the pattern of a structure array element read,
       we translate it to an array subscripting expression
       on the recursively generated index expression
       and on a structure pointer member expression
       on the recursively generated structure expression.
       The type is the member element's type.")
     (xdoc::p
      "If the term is a call of @(tsee c::sint-from-boolean),
       we call the mutually recursive ACL2 function
       that translates the argument
       (which must be an expression term returning a boolean)
       to an expression, which we return.
       The type of this expression is always @('int').")
     (xdoc::p
      "If the term is a @(tsee condexpr) call on an @(tsee if) call,
       we call the mutually recursive ACL2 function on the test,
       we call this ACL2 function on the branches,
       and we construct a conditional expression.
       We ensure that the two branches have the same type.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not a pure expression term.
       We could extend this code to provide
       more information to the user at some point.")
     (xdoc::p
      "As we generate the code, we ensure that the ACL2 terms
       are well-typed according to the C types.
       This is subsumed by guard verification for all the code,
       except for any code that is dead (i.e. unreachable) under the guard:
       the dead code passes guard verification
       (under a hypothesis of @('nil'), i.e. false),
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
          (b* (((er (list arg-expr type)) (atc-gen-expr-pure arg
                                                             inscope
                                                             prec-tags
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
          (b* (((er (list arg1-expr type1)) (atc-gen-expr-pure arg1
                                                               inscope
                                                               prec-tags
                                                               fn
                                                               ctx
                                                               state))
               ((er (list arg2-expr type2)) (atc-gen-expr-pure arg2
                                                               inscope
                                                               prec-tags
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
          (b* (((er (list arg-expr type)) (atc-gen-expr-pure arg
                                                             inscope
                                                             prec-tags
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
          (b* (((er (list arr-expr type1)) (atc-gen-expr-pure arr
                                                              inscope
                                                              prec-tags
                                                              fn
                                                              ctx
                                                              state))
               ((er (list sub-expr type2)) (atc-gen-expr-pure sub
                                                              inscope
                                                              prec-tags
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
         ((mv okp arg tag member mem-type)
          (atc-check-struct-read-scalar term prec-tags))
         ((when okp)
          (b* (((er (list arg-expr type)) (atc-gen-expr-pure arg
                                                             inscope
                                                             prec-tags
                                                             fn
                                                             ctx
                                                             state))
               ((unless (equal type (type-pointer (type-struct tag))))
                (er-soft+ ctx t (irr)
                          "The reading of a ~x0 structure with member ~x1 ~
                           is applied to a term ~x2 returning ~x3, ~
                           but a ~x0 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          (type-struct tag) member arg type)))
            (acl2::value (list (make-expr-memberp :target arg-expr
                                                  :name member)
                               mem-type))))
         ((mv okp index struct tag member index-type elem-type)
          (atc-check-struct-read-array term prec-tags))
         ((when okp)
          (b* (((er (list index-expr index-type1))
                (atc-gen-expr-pure index inscope prec-tags fn ctx state))
               ((unless (equal index-type1 index-type))
                (er-soft+ ctx t (irr)
                          "The reading of ~x0 structure with member ~x1 ~
                           is applied to a term ~x2 returning ~x3, ~
                           but a ~x4 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          (type-struct tag)
                          member
                          index
                          index-type1
                          index-type))
               ((er (list struct-expr struct-type))
                (atc-gen-expr-pure struct inscope prec-tags fn ctx state))
               ((unless (equal struct-type (type-pointer (type-struct tag))))
                (er-soft+ ctx t (irr)
                          "The reading of ~x0 structure with member ~x1 ~
                           is applied to a term ~x2 returning ~x3, ~
                           but a ~x0 operand is expected. ~
                           This is indicative of provably dead code, ~
                           given that the code is guard-verified."
                          (type-struct tag)
                          member
                          struct
                          struct-type)))
            (acl2::value (list (make-expr-arrsub
                                :arr (make-expr-memberp
                                      :target struct-expr
                                      :name member)
                                :sub index-expr)
                               elem-type))))
         ((mv okp arg) (atc-check-sint-from-boolean term))
         ((when okp)
          (b* (((mv erp expr state)
                (atc-gen-expr-bool arg inscope prec-tags fn ctx state))
               ((when erp) (mv erp (irr) state)))
            (mv nil (list expr (type-sint)) state)))
         ((mv okp test then else) (atc-check-condexpr term))
         ((when okp)
          (b* (((mv erp test-expr state) (atc-gen-expr-bool test
                                                            inscope
                                                            prec-tags
                                                            fn
                                                            ctx
                                                            state))
               ((when erp) (mv erp (irr) state))
               ((er (list then-expr then-type)) (atc-gen-expr-pure
                                                 then
                                                 inscope
                                                 prec-tags
                                                 fn
                                                 ctx
                                                 state))
               ((er (list else-expr else-type)) (atc-gen-expr-pure
                                                 else
                                                 inscope
                                                 prec-tags
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
                             (prec-tags atc-string-taginfo-alistp)
                             (fn symbolp)
                             (ctx ctxp)
                             state)
    :returns (mv erp (expr exprp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-pure/bool)
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
      "As in @(tsee atc-gen-expr-pure),
       we perform C type checks on the ACL2 terms.
       See  @(tsee atc-gen-expr-pure) for an explanation."))
    (b* (((mv okp arg) (fty-check-not-call term))
         ((when okp)
          (b* (((er arg-expr) (atc-gen-expr-bool arg
                                                 inscope
                                                 prec-tags
                                                 fn
                                                 ctx
                                                 state)))
            (acl2::value (make-expr-unary :op (unop-lognot)
                                          :arg arg-expr))))
         ((mv okp arg1 arg2) (fty-check-and-call term))
         ((when okp)
          (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                                  inscope
                                                  prec-tags
                                                  fn
                                                  ctx
                                                  state))
               ((er arg2-expr) (atc-gen-expr-bool arg2
                                                  inscope
                                                  prec-tags
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
                                                  prec-tags
                                                  fn
                                                  ctx
                                                  state))
               ((er arg2-expr) (atc-gen-expr-bool arg2
                                                  inscope
                                                  prec-tags
                                                  fn
                                                  ctx
                                                  state)))
            (acl2::value (make-expr-binary :op (binop-logor)
                                           :arg1 arg1-expr
                                           :arg2 arg2-expr))))
         ((mv okp arg in-type) (atc-check-boolean-from-type term))
         ((when okp)
          (b* (((mv erp (list expr type) state)
                (atc-gen-expr-pure arg inscope prec-tags fn ctx state))
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

  :prepwork ((set-state-ok t)
             ;; for speed:
             (local
              (in-theory (disable default-car
                                  default-cdr
                                  acl2::apply$-badgep-properties
                                  type-optionp-of-car-when-type-option-listp
                                  typep-of-car-when-type-listp
                                  symbol-listp
                                  type-listp-when-not-consp))))

  :verify-guards nil ; done below

  ///

  (defret-mutual consp-of-atc-gen-expr-pure
    (defret typeset-of-atc-gen-expr-pure
      (and (consp val)
           (true-listp val))
      :rule-classes :type-prescription
      :fn atc-gen-expr-pure)
    (defret true-of-atc-gen-expr-bool
      t
      :rule-classes nil
      :fn atc-gen-expr-bool))

  (verify-guards atc-gen-expr-pure))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-list ((terms pseudo-term-listp)
                                (inscope atc-symbol-type-alist-listp)
                                (prec-tags atc-string-taginfo-alistp)
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
    "This lifts @(tsee atc-gen-expr-pure) to lists.
     However, we do not return the C types of the expressions."))
  (b* (((when (endp terms)) (acl2::value (list nil nil)))
       ((mv erp (list expr type) state) (atc-gen-expr-pure (car terms)
                                                           inscope
                                                           prec-tags
                                                           fn
                                                           ctx
                                                           state))
       ((when erp) (mv erp (list nil nil) state))
       ((er (list exprs types)) (atc-gen-expr-pure-list (cdr terms)
                                                        inscope
                                                        prec-tags
                                                        fn
                                                        ctx
                                                        state)))
    (acl2::value (list (cons expr exprs)
                       (cons type types))))
  :verify-guards nil ; done below
  ///
  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name typeset-of-atc-gen-expr-pure-list
        :rule-classes :type-prescription))
  (verify-guards atc-gen-expr-pure-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr ((term pseudo-termp)
                      (var-term-alist symbol-pseudoterm-alistp)
                      (inscope atc-symbol-type-alist-listp)
                      (fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      (prec-tags atc-string-taginfo-alistp)
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
          that must be an expression term."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time,
     we check that the term is an expression term,
     as described in the user documentation.")
   (xdoc::p
    "We also return the C type of the expression,
     the affected variables,
     and a limit that suffices for @(tsee exec-expr-call-or-pure)
     to execute the expression completely.")
   (xdoc::p
    "If the term is a call of a function that precedes @('fn')
     in the list of target functions @('fn1'), ..., @('fnp'),
     we translate it to a C function call on the translated arguments.
     The type of the expression is the result type of the function,
     which is looked up in the function alist passed as input:
     we ensure that this type is not @('void').
     A sufficient limit for @(tsee exec-fun) to execute the called function
     is retrieved from the called function's information;
     we add 2 to it, to take into account the decrementing of the limit
     to go from @(tsee exec-expr-call-or-pure) to @(tsee exec-expr-call)
     and from there to @(tsee exec-fun).")
   (xdoc::p
    "Otherwise, we attempt to translate the term as a pure expression term.
     The type is the one returned by that translation.
     As limit we return 1, which suffices for @(tsee exec-expr-call-or-pure)
     to not stop right away due to the limit being 0."))
  (b* (((mv okp called-fn args in-types out-type affect limit)
        (atc-check-cfun-call term var-term-alist prec-fns (w state)))
       ((when okp)
        (b* (((when (type-case out-type :void))
              (er-soft+ ctx t (list (irr-expr) (irr-type) nil nil)
                        "A call ~x0 of the function ~x1, which returns void, ~
                         is being used where ~
                         an ACL2 term is expected to return a C value."
                        term called-fn))
             ((unless (atc-check-cfun-call-args (formals+ called-fn (w state))
                                                in-types
                                                args))
              (er-soft+ ctx t (list (irr-expr) (irr-type) nil nil)
                        "The call ~x0 does not satisfy the restrictions ~
                         on array arguments being identical to the formals."
                        term))
             ((mv erp (list arg-exprs types) state)
              (atc-gen-expr-pure-list args
                                      inscope
                                      prec-tags
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
                        `(binary-+ '2 ,limit))))))
    (b* (((mv erp (list expr type) state)
          (atc-gen-expr-pure term inscope prec-tags fn ctx state))
         ((when erp) (mv erp (list (irr-expr) (irr-type) nil nil) state)))
      (acl2::value (list expr type affect '(quote 1)))))
  ///
  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name typeset-of-atc-gen-expr
        :rule-classes :type-prescription)))

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
  (append (pairlis$ (symbol-list-fix vars)
                    (pseudo-term-list-fix terms))
          (symbol-pseudoterm-alist-fix alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-ensure-formals-not-lost ((bind-affect symbol-listp)
                                     (fn-affect symbol-listp)
                                     (fn-typed-formals atc-symbol-type-alistp)
                                     (fn symbolp)
                                     (ctx ctxp)
                                     state)
  :returns (mv erp
               (nothing null)
               state)
  :short "Ensure that no affected formals are lost."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the body of a non-recursive function @('fn')
     includes an @(tsee mv-let)s or a @(tsee let)
     that affect a formal of @('fn') of pointer type,
     that formal must be among the variables affected by ('fn').
     If the body of a recursive function @('fn')
     includes an @(tsee mv-let)s or a @(tsee let)
     that affect a formal of @('fn') of any type,
     that formal must be among the variables affected by ('fn').
     In other words, no modification of formals must be ``lost''.
     The case of formals of pointer types is clear,
     because it means that objects in the heap are affected.
     The case of formals of non-pointer types
     applies to recursive functions
     because they represent loops,
     which may affect local variables in the function where they appear.")
   (xdoc::p
    "This ACL2 function ensures that no formals are lost in the sense above.
     The parameter @('bind-affect') consists of
     the variable affected by the @(tsee mv-let) or @(tsee let).
     The parameter @('fn-affect') consists of
     the variables purported to be affected by @('fn').
     We go through the elements of @('bind-affect')
     and check each one against the formals of @('fn'),
     taking into account the types and whether @('fn') is recursive."))
  (b* (((when (endp bind-affect)) (acl2::value nil))
       (var (car bind-affect))
       (type (cdr (assoc-eq var fn-typed-formals)))
       ((when (and type
                   (or (irecursivep+ fn (w state))
                       (type-case type :pointer))
                   (not (member-eq var fn-affect))))
        (er-soft+ ctx t nil
                  "When generating C code for the function ~x0, ~
                   the formal parameter ~x1 is being affected ~
                   in an MV-LET or LET term, ~
                   but it is not being returned by ~x0."
                  fn var)))
    (atc-ensure-formals-not-lost
     (cdr bind-affect) fn-affect fn-typed-formals fn ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-recognizer-to-type ((recognizer symbolp)
                                (prec-tags atc-string-taginfo-alistp))
  :returns (type type-optionp)
  :short "C type corresponding to a recognizer name, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to determine the types of the formal parameters of functions
     from the recognizers used in the guard,
     as explained in the user documentation.
     Note that the structure recognizers represent pointer types."))
  (case recognizer
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
    (t (b* (((mv okp struct tag p) (atc-check-symbol-3part recognizer))
            ((unless (and okp
                          (equal (symbol-name struct) "STRUCT")
                          (equal (symbol-name p) "P")))
             nil)
            (tag (symbol-name tag))
            (info (cdr (assoc-equal tag prec-tags)))
            ((unless info) nil)
            ((unless (atc-tag-infop info))
             (raise "Internal error: malformed DEFSTRUCT info ~x0." info))
            (info (atc-tag-info->defstruct info))
            ((unless (eq recognizer (defstruct-info->recognizer info))) nil)
            ((unless (ident-stringp tag))
             (raise "Internal error: tag ~x0 not valid identifier." tag)))
         (type-pointer (type-struct (ident tag)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-typed-formals ((fn symbolp)
                           (prec-tags atc-string-taginfo-alistp)
                           (ctx ctxp)
                           state)
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
     where @('<type>') is a predicate corresponding to a C type.")
   (xdoc::p
    "We ensure that there is exactly one such term for each formal.
     If this is successful,
     we return an alist from the formals to the types.
     The alist has unique keys, in the order of the formals.")
   (xdoc::p
    "We first extract the guard's conjuncts,
     then we go through the conjuncts, looking for the pattern,
     and we extend an alist from formals to types as we find patterns;
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
                                                          prec-tags
                                                          ctx
                                                          state)))
    (atc-typed-formals-final-alist
     fn formals guard prelim-alist prec-tags ctx state))

  :prepwork

  ((define atc-typed-formals-prelim-alist ((fn symbolp)
                                           (formals symbol-listp)
                                           (guard pseudo-termp)
                                           (guard-conjuncts pseudo-term-listp)
                                           (prelim-alist atc-symbol-type-alistp)
                                           (prec-tags atc-string-taginfo-alistp)
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
                                           prec-tags
                                           ctx
                                           state))
          (type-fn (ffn-symb conjunct))
          (type (atc-recognizer-to-type type-fn prec-tags))
          ((when (not type))
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           prec-tags
                                           ctx
                                           state))
          (arg (fargn conjunct 1))
          ((unless (member-eq arg formals))
           (atc-typed-formals-prelim-alist fn
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prelim-alist
                                           prec-tags
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
                                       prec-tags
                                       ctx
                                       state)))

   (define atc-typed-formals-final-alist ((fn symbolp)
                                          (formals symbol-listp)
                                          (guard pseudo-termp)
                                          (prelim-alist atc-symbol-type-alistp)
                                          (prec-tags atc-string-taginfo-alistp)
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
                                                             prec-tags
                                                             ctx
                                                             state)))
       (acl2::value (acons formal type typed-formals)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp)
                      (var-term-alist symbol-pseudoterm-alistp)
                      (inscope atc-symbol-type-alist-listp)
                      (loop-flag booleanp)
                      (affect symbol-listp)
                      (fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      (prec-tags atc-string-taginfo-alistp)
                      (proofs booleanp)
                      (ctx ctxp)
                      state)
  :returns (mv erp
               (val (tuple (items block-item-listp)
                           (type typep)
                           (limit pseudo-termp)
                           val)
                    :hints nil) ; for speed
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
     we also return a C type, which is the one returned by the statement.
     This type may be @('void').")
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
     there are three cases.
     If the term involves a @('declar<n>') wrapper,
     we ensure that a variable with
     the same symbol name as the first bound variable
     is not already in scope
     (i.e. in the symbol table)
     and that the name is a portable ASCII identifier;
     we generate a declaration for the variable,
     initialized with the expression obtained
     from the term that the variable is bound to,
     which also determines the type of the variable,
     and which must affect the bound variables except the first one;
     the type must not be a pointer type (code generation fails if it is).
     Otherwise, if the term involves an @('assign<n>') wrapper,
     we ensure that the first bound variable is assignable,
     which implies that it must be in scope,
     and we also ensure that it has the same type as the one in scope;
     we generate an assignment whose right-hand side is
     obtained from the unwrapped term,
     which must be an expression term returning a C value
     that affects the bound variables except the first one.
     Otherwise, if the term involves no wrapper,
     we ensure that the bound variables are all assignable,
     and that the non-wrapped term has the form
     described in the user documentation;
     we generate code that affects the variables from that term.
     In all cases, we recursively generate the block items for the body
     and we put those just after the preceding code.
     We use the sum of the two limits as the overall limit:
     thus, after @(tsee exec-block-item-list) executes
     the block items for the bound term,
     it still has enough limit to execute the block items for the body term.")
   (xdoc::p
    "If the term is a @(tsee let), there are five cases.
     If the binding has the form of an array write,
     we generate an array assignment.
     If the binding has the form of a structure write,
     we generate a structure pointer member assignment.
     The other three cases are similar to
     the three @(tsee mv-let) cases above.
     The limit is calculated as follows.
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
     The first block item is a declaration, an assignment, or a function call.
     If it is a declaration, we need 1 to go from @(tsee exec-block-item)
     to the @(':declon') case and to @(tsee exec-expr-call-or-pure),
     for which we get the limit.
     If it is an assignment, we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and to @(tsee exec-stmt),
     another 1 to go from there to the @(':expr') case
     and to @(tsee exec-expr-call-or-asg),
     another 1 to fo from there to @(tsee exec-expr-asg),
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
     this is the end of a list of block items that affects that variable.
     We generate 1 as the limit,
     because we need 1 to go from @(tsee exec-block-item-list)
     to the empty list case.")
   (xdoc::p
    "If the term is an @(tsee mv), there are three cases.
     If the loop flag is @('t'), it is an error.
     Otherwise, if the arguments of @(tsee mv) are the @('affect') variables,
     we return nothing, because
     this is the end of a list of block items that affects that variable;
     we return 1 as the limit, for the same reason as the case above.
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
    "If the term is a call of
     a non-recursive target function that returns @('void'),
     the term represents an expression statement
     consisting of a call to the corresponding C function.
     The loop flag must be @('nil') for this to be allowed.
     We ensure that all the pointer arguments are equal to the formals,
     and that the variables affected by the called function are correct.
     We retrieve the limit term associated to the called function,
     which, as explained in @(tsee atc-fn-info),
     suffices to execute @(tsee exec-fun).
     But here we are executing lists of block items,
     so we need to add 1 to go from @(tsee exec-block-item-list)
     to the call of @(tsee exec-block-item),
     another 1 to go from there to the call of @(tsee exec-stmt),
     another 1 to go from there to the call of @(tsee exec-expr-call-or-asg),
     another 1 to go from there to the call of @(tsee exec-expr-call),
     and another 1 to go from there to the call of @(tsee exec-fun).")
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
       (wrld (w state))
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
                            prec-tags
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
                            prec-tags
                            proofs
                            ctx
                            state))
             ((mv erp test-expr state) (atc-gen-expr-bool test
                                                          inscope
                                                          prec-tags
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
                            prec-tags
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
                            prec-tags
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
       ((mv okp var? vars indices val body wrapper?) (atc-check-mv-let term))
       ((when okp)
        (b* ((all-vars (if var? (cons var? vars) vars))
             (val-instance (fty-fsublis-var var-term-alist val))
             (vals (atc-make-mv-nth-terms indices val-instance))
             (var-term-alist-body
              (atc-update-var-term-alist all-vars vals var-term-alist))
             ((when (eq wrapper? 'declar))
              (b* ((var var?)
                   ((mv type? & errorp) (atc-check-var var inscope))
                   ((when errorp)
                    (er-soft+ ctx t irr
                              "When generating C code for the function ~x0, ~
                               a new variable ~x1 has been encountered ~
                               that has the same symbol name as, ~
                               but different package name from, ~
                               a variable already in scope. ~
                               This is disallowed."
                              fn var))
                   ((when type?)
                    (er-soft+ ctx t irr
                              "The variable ~x0 in the function ~x1 ~
                               is already in scope and cannot be re-declared."
                              var fn))
                   ((unless (ident-stringp (symbol-name var)))
                    (er-soft+ ctx t irr
                              "The symbol name ~s0 of ~
                               the MV-LET variable ~x1 of the function ~x2 ~
                               must be a portable ASCII C identifier, ~
                               but it is not."
                              (symbol-name var) var fn))
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
                   ((mv erp
                        (list init-expr init-type init-affect init-limit)
                        state)
                    (atc-gen-expr val
                                  var-term-alist
                                  inscope
                                  fn
                                  prec-fns
                                  prec-tags
                                  ctx
                                  state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal init-affect vars))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must affect the variables ~x2, ~
                               but it affects ~x3 instead."
                              val var vars init-affect))
                   ((mv erp typed-formals state)
                    (atc-typed-formals fn prec-tags ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp & state) (atc-ensure-formals-not-lost vars
                                                                  affect
                                                                  typed-formals
                                                                  fn
                                                                  ctx
                                                                  state))
                   ((when erp) (mv erp irr state))
                   ((mv tyspec declor) (ident+type-to-tyspec+declor
                                        (make-ident :name (symbol-name var))
                                        init-type))
                   (declon (make-obj-declon :tyspec tyspec
                                            :declor declor
                                            :init (initer-single init-expr)))
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
                                  prec-tags
                                  proofs
                                  ctx
                                  state))
                   (type body-type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 3)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list init-limit body-limit))))))
                (acl2::value (list (cons item body-items)
                                   type
                                   limit))))
             ((when (eq wrapper? 'assign))
              (b* ((var var?)
                   ((mv type? innermostp &) (atc-check-var var inscope))
                   ((unless (atc-var-assignablep var innermostp affect))
                    (er-soft+ ctx t irr
                              "When generating C code for the function ~x0, ~
                               an attempt is being made ~
                               to modify a non-assignable variable ~x1."
                              fn var))
                   (prev-type type?)
                   ((mv erp
                        (list rhs-expr rhs-type rhs-affect rhs-limit)
                        state)
                    (atc-gen-expr val
                                  var-term-alist
                                  inscope
                                  fn
                                  prec-fns
                                  prec-tags
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
                   ((unless (equal rhs-affect vars))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must affect the variables ~x2, ~
                               but it affects ~x3 instead."
                              val var vars rhs-affect))
                   ((mv erp typed-formals state)
                    (atc-typed-formals fn prec-tags ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp & state) (atc-ensure-formals-not-lost vars
                                                                  affect
                                                                  typed-formals
                                                                  fn
                                                                  ctx
                                                                  state))
                   ((when erp) (mv erp irr state))
                   ((when (type-case rhs-type :array))
                    (raise "Internal error: array type ~x0." rhs-type)
                    (acl2::value irr))
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
                                  prec-tags
                                  proofs
                                  ctx
                                  state))
                   (type body-type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 6)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list rhs-limit body-limit))))))
                (acl2::value (list (cons item body-items)
                                   type
                                   limit))))
             ((unless (eq wrapper? nil))
              (prog2$ (raise "Internal error: LET wrapper is ~x0." wrapper?)
                      (acl2::value irr)))
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
             ((mv erp typed-formals state)
              (atc-typed-formals fn prec-tags ctx state))
             ((when erp) (mv erp irr state))
             ((mv erp & state) (atc-ensure-formals-not-lost vars
                                                            affect
                                                            typed-formals
                                                            fn
                                                            ctx
                                                            state))
             ((when erp) (mv erp irr state))
             ((er (list xform-items xform-type xform-limit))
              (atc-gen-stmt val
                            var-term-alist
                            inscope
                            nil
                            vars
                            fn
                            prec-fns
                            prec-tags
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
             ((er (list body-items body-type body-limit))
              (atc-gen-stmt body
                            var-term-alist-body
                            inscope
                            loop-flag
                            affect
                            fn
                            prec-fns
                            prec-tags
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
              (b* (((unless (eq wrapper? nil))
                    (er-soft+ ctx t irr
                              "The array write term ~x0 to which ~x1 is bound ~
                               has the ~x2 wrapper, which is disallowed."
                              val var wrapper?))
                   ((unless (member-eq var affect))
                    (er-soft+ ctx t irr
                              "The array ~x0 is being written to, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var affect))
                   ((mv erp (list arr-expr type1) state)
                    (atc-gen-expr-pure var inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp (list sub-expr type2) state)
                    (atc-gen-expr-pure sub inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp (list elem-expr type3) state)
                    (atc-gen-expr-pure elem inscope prec-tags fn ctx state))
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
                               is being indexed with ~
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
                                  prec-tags
                                  proofs
                                  ctx
                                  state))
                   (limit (pseudo-term-fncall 'binary-+
                                              (list (pseudo-term-quote 4)
                                                    body-limit))))
                (acl2::value (list (cons item body-items)
                                   body-type
                                   limit))))
             ((mv okp member-value tag member-name member-type)
              (atc-check-struct-write-scalar var val prec-tags))
             ((when okp)
              (b* (((unless (eq wrapper? nil))
                    (er-soft+ ctx t irr
                              "The structure write term ~x0 ~
                               to which ~x1 is bound ~
                               has the ~x2 wrapper, which is disallowed."
                              val var wrapper?))
                   ((unless (member-eq var affect))
                    (er-soft+ ctx t irr
                              "The structure ~x0 is being written to, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var affect))
                   ((mv erp (list struct-expr type1) state)
                    (atc-gen-expr-pure var inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((mv erp (list member-expr type2) state)
                    (atc-gen-expr-pure member-value
                                       inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal type1 (type-pointer (type-struct tag))))
                    (er-soft+ ctx t irr
                              "The structure ~x0 of type ~x1 ~
                               does not have the expected type ~x2. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var type1 (type-pointer (type-struct tag))))
                   ((unless (equal type2 member-type))
                    (er-soft+ ctx t irr
                              "The structure ~x0 of type ~x1 ~
                               is being written to with ~
                               a member ~x2 of type ~x3, ~
                               instead of type ~x4 as expected. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var type1 member-value type2 member-type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (make-expr-memberp :target struct-expr
                                                  :name member-name)
                         :arg2 member-expr))
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
                                  prec-tags
                                  proofs
                                  ctx
                                  state))
                   (limit (pseudo-term-fncall 'binary-+
                                              (list (pseudo-term-quote 4)
                                                    body-limit))))
                (acl2::value (list (cons item body-items)
                                   body-type
                                   limit))))
             ((mv okp index elem tag member index-type elem-type)
              (atc-check-struct-write-array var val prec-tags))
             ((when okp)
              (b* (((unless (eq wrapper? nil))
                    (er-soft+ ctx t irr
                              "The structure write term ~x0 ~
                               to which ~x1 is bound ~
                               has the ~x2 wrapper, which is disallowed."
                              val var wrapper?))
                   ((unless (member-eq var affect))
                    (er-soft+ ctx t irr
                              "The structure ~x0 is being written to, ~
                               but it is not among the variables ~x1 ~
                               currently affected."
                              var affect))
                   ((mv erp (list struct-expr struct-type) state)
                    (atc-gen-expr-pure var inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal struct-type
                                   (type-pointer (type-struct tag))))
                    (er-soft+ ctx t irr
                              "The structure ~x0 of type ~x1 ~
                               does not have the expected type ~x2. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var struct-type (type-pointer (type-struct tag))))
                   ((mv erp (list index-expr index-type1) state)
                    (atc-gen-expr-pure index inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal index-type1 index-type))
                    (er-soft+ ctx t irr
                              "The structure ~x0 of type ~x1 ~
                               is being written to with ~
                               an index ~x2 of type ~x3, ~
                               instead of type ~x4 as expected. ~
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var struct-type index index-type1 index-type))
                   ((mv erp (list elem-expr elem-type1) state)
                    (atc-gen-expr-pure elem inscope prec-tags fn ctx state))
                   ((when erp) (mv erp irr state))
                   ((unless (equal elem-type1 elem-type))
                    (er-soft+ ctx t irr
                              "The structure ~x0 of type ~x1 ~
                               is being written to with ~
                               a member array element ~x2 of type ~x3, ~
                               instead of type ~x4 as expected.
                               This is indicative of ~
                               unreachable code under the guards, ~
                               given that the code is guard-verified."
                              var struct-type elem elem-type1 elem-type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (make-expr-arrsub
                                :arr (make-expr-memberp
                                      :target struct-expr
                                      :name member)
                                :sub index-expr)
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
                                  prec-tags
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
                   ((unless (ident-stringp (symbol-name var)))
                    (er-soft+ ctx t irr
                              "The symbol name ~s0 of ~
                               the LET variable ~x1 of the function ~x2 ~
                               must be a portable ASCII C identifier, ~
                               but it is not."
                              (symbol-name var) var fn))
                   ((mv erp
                        (list init-expr init-type init-affect init-limit)
                        state)
                    (atc-gen-expr val
                                  var-term-alist
                                  inscope
                                  fn
                                  prec-fns
                                  prec-tags
                                  ctx
                                  state))
                   ((when erp) (mv erp irr state))
                   ((when (consp init-affect))
                    (er-soft+ ctx t irr
                              "The term ~x0 to which the variable ~x1 is bound ~
                               must not affect any variables, ~
                               but it affects ~x2 instead."
                              val var init-affect))
                   ((mv tyspec declor) (ident+type-to-tyspec+declor
                                        (make-ident :name (symbol-name var))
                                        init-type))
                   (declon (make-obj-declon :tyspec tyspec
                                            :declor declor
                                            :init (initer-single init-expr)))
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
                                  prec-tags
                                  proofs
                                  ctx
                                  state))
                   (type body-type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 3)
                                 (pseudo-term-fncall
                                  'binary-+
                                  (list init-limit body-limit))))))
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
                    (atc-gen-expr val
                                  var-term-alist
                                  inscope
                                  fn
                                  prec-fns
                                  prec-tags
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
                   ((when (type-case rhs-type :array))
                    (raise "Internal error: array type ~x0." rhs-type)
                    (acl2::value irr))
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
                                  prec-tags
                                  proofs
                                  ctx
                                  state))
                   (type body-type)
                   (limit (pseudo-term-fncall
                           'binary-+
                           (list (pseudo-term-quote 6)
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
                         we encountered a term ~x1, ~
                         to which a LET variable is bound, ~
                         that is not wrapped by C::DECLAR or C::ASSIGN, ~
                         and that is neither an IF or a loop function call. ~
                         This is disallowed."
                        fn val))
             ((mv erp typed-formals state)
              (atc-typed-formals fn prec-tags ctx state))
             ((when erp) (mv erp irr state))
             ((mv erp & state) (atc-ensure-formals-not-lost (list var)
                                                            affect
                                                            typed-formals
                                                            fn
                                                            ctx
                                                            state))
             ((when erp) (mv erp irr state))
             ((er (list xform-items xform-type xform-limit))
              (atc-gen-stmt val
                            var-term-alist
                            inscope
                            nil
                            (list var)
                            fn
                            prec-fns
                            prec-tags
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
                            prec-tags
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
          (acl2::value (list nil (type-void) (pseudo-term-quote 1)))))
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
            (acl2::value (list nil (type-void) (pseudo-term-quote 1))))
           ((equal (cdr terms) affect)
            (b* (((mv erp (list expr type eaffect limit) state)
                  (atc-gen-expr (car terms)
                                var-term-alist
                                inscope
                                fn
                                prec-fns
                                prec-tags
                                ctx
                                state))
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
                         but in the function ~x0 it ends with ~x1 instead."
                        fn term))
             (formals (formals+ loop-fn wrld))
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
       ((when (equal term `(,fn ,@(formals+ fn wrld))))
        (if loop-flag
            (acl2::value (list nil (type-void) (pseudo-term-quote 1)))
          (er-soft+ ctx t irr
                    "When generating code for the recursive function ~x0, ~
                     a recursive call to the loop function occurs ~
                     not at the end of the computation on some path."
                    fn)))
       ((mv okp called-fn args in-types out-type fn-affect limit)
        (atc-check-cfun-call term var-term-alist prec-fns wrld))
       ((when (and okp
                   (type-case out-type :void)))
        (b* (((when loop-flag)
              (er-soft+ ctx t irr
                        "A loop body must end with ~
                         a recursive call on every path, ~
                         but in the function ~x0 it ends with ~x1 instead."
                        fn term))
             ((unless (atc-check-cfun-call-args (formals+ called-fn wrld)
                                                in-types
                                                args))
              (er-soft+ ctx t irr
                        "The call ~x0 does not satisfy the restrictions ~
                         on array arguments being identical to the formals."
                        term))
             ((unless (equal affect fn-affect))
              (er-soft+ ctx t irr
                        "When generating C code for the function ~x0, ~
                         a call of the non-recursive function ~x1 ~
                         has been encountered that affects ~x2, ~
                         which differs from the variables ~x3 ~
                         being affected here."
                        fn loop-fn fn-affect affect))
             ((mv erp (list arg-exprs types) state)
              (atc-gen-expr-pure-list args
                                      inscope
                                      prec-tags
                                      fn
                                      ctx
                                      state))
             ((when erp) (mv erp irr state))
             ((unless (equal types in-types))
              (er-soft+ ctx t irr
                        "The function ~x0 with input types ~x1 ~
                         is applied to terms ~x2 returning ~x3. ~
                         This is indicative of provably dead code, ~
                         given that the code is guard-verified."
                        called-fn in-types args types))
             (call-expr (make-expr-call :fun (make-ident
                                              :name (symbol-name called-fn))
                                        :args arg-exprs)))
          (acl2::value (list (list (block-item-stmt (stmt-expr call-expr)))
                             (type-void)
                             `(binary-+ '5 ,limit)))))
       ((mv erp (list expr type eaffect limit) state)
        (atc-gen-expr term
                      var-term-alist
                      inscope
                      fn
                      prec-fns
                      prec-tags
                      ctx
                      state))
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
       ((when (type-case type :array))
        (raise "Internal error: array type ~x0." type)
        (acl2::value irr))
       ((when (type-case type :pointer))
        (er-soft+ ctx t irr
                  "When generating a return statement for function ~x0, ~
                   the term ~x1 that represents the return expression ~
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

  (verify-guards atc-gen-stmt
    :hints (("Goal" :in-theory (disable atc-gen-stmt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-stmt ((term pseudo-termp)
                           (inscope atc-symbol-type-alist-listp)
                           (fn symbolp)
                           (measure-for-fn symbolp)
                           (measure-formals symbol-listp)
                           (prec-fns atc-symbol-fninfo-alistp)
                           (prec-tags atc-string-taginfo-alistp)
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
                    ;; for speed:
                    :hints (("Goal" :induct (atc-gen-loop-stmt term
                                                               inscope
                                                               fn
                                                               measure-for-fn
                                                               measure-formals
                                                               prec-fns
                                                               prec-tags
                                                               proofs
                                                               ctx
                                                               state))))
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
       (wrld (w state))
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
                           prec-tags
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
                           prec-tags
                           proofs
                           ctx
                           state))
       ((mv erp test-expr state) (atc-gen-expr-bool test
                                                    inscope
                                                    prec-tags
                                                    fn
                                                    ctx
                                                    state))
       ((when erp) (mv erp (irr) state))
       (formals (formals+ fn wrld))
       ((mv okp affect)
        (b* (((when (member-eq else formals)) (mv t (list else)))
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
                      prec-tags
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
       ((when (eq measure-for-fn 'quote))
        (raise "Internal error: the measure function is QUOTE.")
        (acl2::value (irr)))
       (measure-call (pseudo-term-fncall measure-for-fn measure-formals))
       (limit `(binary-+ '1 (binary-+ ,body-limit ,measure-call))))
    (acl2::value (list stmt test then affect body-limit limit)))
  :measure (pseudo-term-count term)
  :guard-hints (("Goal" :in-theory (enable acl2::pseudo-fnsym-p)))
  ///

  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name cons-true-listp-of-atc-gen-loop-stmt-val
        :rule-classes :type-prescription
        ;;  for speed:
        :hints (("Goal" :induct (atc-gen-loop-stmt term
                                                   inscope
                                                   fn
                                                   measure-for-fn
                                                   measure-formals
                                                   prec-fns
                                                   prec-tags
                                                   proofs
                                                   ctx
                                                   state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-declon-list ((typed-formals atc-symbol-type-alistp)
                                   (fn symbolp)
                                   (ctx ctxp)
                                   state)
  :returns (mv erp
               (params param-declon-listp)
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
    "We check that the name of the parameter is a portable C identifier,
     and distinct from the names of the other parameters."))
  (b* (((when (endp typed-formals)) (acl2::value nil))
       ((cons formal type) (car typed-formals))
       (name (symbol-name formal))
       ((unless (ident-stringp name))
        (er-soft+ ctx t nil
                  "The symbol name ~s0 of ~
                   the formal parameter ~x1 of the function ~x2 ~
                   must be a portable ASCII C identifier, but it is not."
                  name formal fn))
       (cdr-formals (strip-cars (cdr typed-formals)))
       ((when (member-equal name (symbol-name-lst cdr-formals)))
        (er-soft+ ctx t nil
                  "The formal parameter ~x0 of the function ~x1 ~
                   has the same symbol name as ~
                   another formal parameter among ~x2; ~
                   this is disallowed, even if the package names differ."
                  formal fn cdr-formals))
       ((mv tyspec declor) (ident+type-to-tyspec+declor (make-ident :name name)
                                                        type))
       (param (make-param-declon :tyspec tyspec
                                 :declor declor))
       ((er params)
        (atc-gen-param-declon-list (cdr typed-formals) fn ctx state)))
    (acl2::value (cons param params)))
  :prepwork ((local
              (in-theory
               (e/d
                (symbol-listp-of-strip-cars-when-atc-symbol-type-alistp)
                ;; for speed:
                (always$
                 member-equal
                 symbol-name-lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-fun-env-thm ((fn symbolp)
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
  (b* (((unless (fun-infop finfo?)) (mv nil nil names-to-avoid))
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

(define atc-gen-fn-result-thm ((fn symbolp)
                               (type? type-optionp)
                               (affect symbol-listp)
                               (typed-formals atc-symbol-type-alistp)
                               (prec-fns atc-symbol-fninfo-alistp)
                               (prec-tags atc-string-taginfo-alistp)
                               (names-to-avoid symbol-listp)
                               (wrld plist-worldp))
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem about the result(s) of @('fn')."
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
     "A formal parameter is constrained to be a C value by the guard.")
    (xdoc::li
     "Calls of @(tsee sint-dec-const), @(tsee add-sint-sint), etc.
      are known to return C values.")
    (xdoc::li
     "Calls of arrays and structure readers and writers
      are known to return C values.")
    (xdoc::li
     "A @(tsee let) or @(tsee mv-let) variable is equal to a term that,
      recursively, always returns a C value.")
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
      that return a non-@('void') result
      and also affect arrays and structures)."))
   (xdoc::p
    "This suggests a coarse but adequate proof strategy:
     We use the theory consisting of
     the definition of @('fn'),
     the return type theorems of @(tsee sint-dec-const) and related functions,
     the return type theorems for array and structure readers and writers,
     and the theorems about the preceding functions;
     we also add a @(':use') hint for the guard theorem of @('fn').
     The theorems about structure readers and writers
     are taken from the alist of the preceding structure tags.")
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
     an optional C result
     and zero or more affected variables or arrays or structures.
     We collect all of them.
     The C result is determined from the optional C type of the function,
     which is @('nil') for recursive functions,
     and may or may not be @('void') for non-recursive functions.
     The affected variables are also considered as results.
     We concatenate zero or one types from @('type?')
     with zero or more types from @('affect') and @('typed-formals').
     More precisely, we make an alist instead of a list,
     whose values are the types in question
     and whose keys are @('nil') for the C result (if present)
     and the names in @('affect') for the other ones.
     Then we operate on the resulting alist,
     which forms all the results of the function
     with their names (and @('nil') for the result, if present).
     The alist is never empty (an ACL2 function must always return something);
     If the alist is a singleton,
     we generate assertions about the function call.
     If the list has multiple elements,
     we generate assertions for the @(tsee mv-nth)s of the function call.")
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
    "For each result of the function,
     we always generate an assertion about its C type.")
   (xdoc::p
    "We also generate assertions saying that the results are not @('nil').
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
     the executable counterparts of the type recognizers;
     the subgoals that arise without them have the form
     @('(<recognizer> nil)').")
   (xdoc::p
    "We also generate assertions saying that
     each array returned by the function
     has the same length as the corresponding input array.
     This is necessary for the correctness proofs of
     functions that call this function."))
  (b* ((results1 (and type?
                      (not (type-case type? :void))
                      (list (cons nil type?))))
       (results2 (atc-gen-fn-result-thm-aux1 affect typed-formals))
       (results (append results1 results2))
       ((unless (consp results))
        (raise "Internal error: the function ~x0 has no results." fn)
        (mv nil nil names-to-avoid))
       (formals (formals+ fn wrld))
       (fn-call `(,fn ,@formals))
       (conjuncts (atc-gen-fn-result-thm-aux2 results
                                              (if (consp (cdr results))
                                                  0
                                                nil)
                                              fn-call
                                              wrld))
       (conclusion
        (if (and (consp conjuncts)
                 (not (consp (cdr conjuncts))))
            (car conjuncts)
          `(and ,@conjuncts)))
       (name (add-suffix fn
                         (if (consp (cdr results))
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
                  *atc-array-write-return-rewrite-rules*
                  *atc-array-length-write-rules*
                  ',(atc-string-taginfo-alist-to-reader-return-thms prec-tags)
                  ',(atc-string-taginfo-alist-to-writer-return-thms prec-tags)
                  '(,fn
                    ,@(atc-symbol-fninfo-alist-to-result-thms
                       prec-fns (all-fnnames (ubody+ fn wrld)))
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
                    condexpr
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
                    (:e sllongp)
                    (:e uchar-arrayp)
                    (:e schar-arrayp)
                    (:e ushort-arrayp)
                    (:e sshort-arrayp)
                    (:e uint-arrayp)
                    (:e sint-arrayp)
                    (:e ulong-arrayp)
                    (:e slong-arrayp)
                    (:e ullong-arrayp)
                    (:e sllong-arrayp)
                    ,@(loop$ for recog
                             in (atc-string-taginfo-alist-to-recognizers
                                 prec-tags)
                             collect `(:e ,recog)))))
                '(:use (:guard-theorem ,fn))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv (list event) name names-to-avoid))

  :prepwork

  ((define atc-gen-fn-result-thm-aux1 ((affect symbol-listp)
                                       (typed-formals atc-symbol-type-alistp))
     :returns (results atc-symbol-type-alistp :hyp (symbol-listp affect))
     :parents nil
     (cond ((endp affect) nil)
           (t (b* ((type (cdr (assoc-eq (car affect)
                                        typed-formals))))
                (if (typep type)
                    (acons (car affect)
                           type
                           (atc-gen-fn-result-thm-aux1 (cdr affect)
                                                       typed-formals))
                  (raise "Internal error: variable ~x0 not found in ~x1."
                         (car affect) typed-formals))))))

   (define atc-gen-fn-result-thm-aux2 ((results atc-symbol-type-alistp)
                                       (index? maybe-natp)
                                       (fn-call pseudo-termp)
                                       (wrld plist-worldp))
     :returns conjuncts
     :parents nil
     (b* (((when (endp results)) nil)
          (theresult (if index?
                         `(mv-nth ,index? ,fn-call)
                       fn-call))
          ((cons name type) (car results))
          (type-conjunct `(,(atc-type-to-recognizer type wrld) ,theresult))
          (nonnil-conjunct? (and index? (list theresult)))
          (arraylength-conjunct?
           (b* (((unless (type-case type :pointer)) nil)
                (reftype (type-pointer->to type))
                ((unless (type-integerp reftype)) nil)
                (reftype-array-length (pack (integer-type-to-fixtype reftype)
                                            '-array-length)))
             (list `(equal (,reftype-array-length ,theresult)
                           (,reftype-array-length ,name))))))
       (append (list type-conjunct)
               nonnil-conjunct?
               arraylength-conjunct?
               (atc-gen-fn-result-thm-aux2 (cdr results)
                                           (and index? (1+ index?))
                                           fn-call
                                           wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-outer-bindings-and-hyps ((typed-formals atc-symbol-type-alistp)
                                         (compst-var symbolp)
                                         (fn-recursivep booleanp))
  :returns (mv (bindings doublet-listp)
               (pointer-hyps true-listp)
               (pointer-subst symbol-symbol-alistp
                              :hyp (atc-symbol-type-alistp typed-formals))
               (instantiation doublet-listp))
  :short "Generate the outer bindings,
          pointer hypotheses,
          pointer substitutions,
          and lemma instantiation,
          for a correctness theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both C functions and C loops have correctness theorems of the form
     @('(b* (<bindings>) ...)').
     Here we generate the @('<bindings>'),
     which we designate as `outer' since they are
     at the outermost level of the theorem's formula.
     We also generate some of the hypotheses
     used in the correctness theorems
     that relate to the bindings,
     explained below.
     We also generate a variable substitution, explained below.
     We also generate an instantiation
     for a lemma used in the hints of the generated theorem.")
   (xdoc::p
    "The (outer) bindings can be determined from
     the formals of the ACL2 function @('fn') that represents
     the C function or C loop.
     The bindings differ between C functions and loops,
     but there is also commonality,
     which justifies having this one ACL2 code generation function
     that handles both cases.")
   (xdoc::p
    "Consider a non-recursive @('fn'), which represents a C function.
     Its correctness theorem equates (roughly speaking)
     a call of @(tsee exec-fun) with a call of @('fn').
     However, while @('fn') takes arrays and structures as arguments,
     @(tsee exec-fun) takes pointers to those arrays and structures.
     So we introduce variables for the pointers,
     named after the formals of @('fn') that are arrays or structures:
     we add @('-PTR') to the formals of @('fn'),
     which should not cause name conflicts because
     the names of the formals must be portable C identifiers.
     For each array or structure formal @('a') of @('fn'),
     we generate a pointer variable @('a-ptr') as explained,
     along with a binding
     @('(a (read-object (value-pointer->designator a-ptr) compst))'):
     this binding relates the two variables,
     and lets us use the guard of @('fn') as hypothesis in the theorem,
     which uses @('a'),
     which the binding replaces with the array or structure
     pointed to by @('a-ptr').
     Along with this binding, we also generate hypotheses saying that
     @('a-ptr') is a top-level pointer of the appropriate type;
     the type is determined from the type of the formal @('a').
     Along with the binding and the hypotheses,
     we also generate an alist element @('(a . a-ptr)'),
     returned as part of the @('pointer-subst') result,
     that is used to generate the argument list of @(tsee exec-fun),
     by applying the substitution @('pointer-subst') to the formals of @('fn'):
     this way, @('a') gets substituted with @('a-ptr'),
     which is what we want since @(tsee exec-fun) takes pointers, not arrays.")
   (xdoc::p
    "The non-array non-structure formals of a non-recursive @('fn')
     do not cause any bindings, hypotheses, or substitutions to be generated.
     They are passed to both @(tsee exec-fun) and @('fn') in the theorem,
     and it is the guard of @('fn') that constrains them
     in the hypotheses of the theorem.")
   (xdoc::p
    "The treatment of a recursive @('fn') is a bit more complicated.
     The correctness theorem for the loop represented by @('fn')
     equates (roughly speaking)
     a call of @(tsee exec-stmt) with a call of @('fn').
     However, @(tsee exec-stmt) is called on a computation state,
     not on anything that corresponds to the formals of @('fn'),
     as is the case for a non-recursive @('fn') as explained above.
     There is still a correspondence, of course:
     the formals of @('fn') correspond to variables in the computation state.
     We consider separately
     the case of arrays or structures,
     and the case of non-arrays and non-structures.")
   (xdoc::p
    "If @('a') is a non-array non-structure formal of a recursive @('fn'),
     it corresponds to @('(read-var <a> compst)'),
     where @('<a>') is the identifier derived from the name of @('a').
     Thus, in this case we generate the binding @('(a (read-var <a> compst))').
     Since no pointers are involved, in this case we generate
     no hypotheses and no substitutions.")
   (xdoc::p
    "If @('a') is an array or structure formal of a recursive @('fn'),
     we introduce an additional @('a-ptr') variable,
     similarly to the case of non-recursive @('fn').
     We generate two bindings @('(a-ptr (read-var <a> compst))')
     and @('(a (read-object (value-pointer->designator a-ptr) compst))'),
     in that order.
     The first binding serves to tie @('a-ptr')
     to the corresponding variable in the computation state,
     which has the name of @('a'), but it holds a pointer.
     The second binding is analogous in purpose
     to the case of a non-recursive @('fn') explained above:
     it lets us use the guard of @('fn'), which references @('a'),
     in the hypotheses of the generated theorem
     without having to make an explicit substitution,
     because the bindings are in fact doing the substitution.
     It should be clear why the two bindings have to be in that order;
     the bindings are put into a @(tsee b*),
     which enforces the order.
     We generate no substitution map in @('pointer-subst') here,
     because that only applies to @(tsee exec-fun),
     which is not used for C loops.")
   (xdoc::p
    "The reason for generating and using these bindings in the theorems,
     as opposed to making the substitutions in the theorem's formula,
     is greater readability.
     Particularly in the case of loop theorems,
     if @('a') occurs a few times in the guard,
     the guard with just @('a') in those occurrences is more readable than
     if all those occurrences are replaced with @('(read-var <a> compst)').")
   (xdoc::p
    "The lemma instantiation is similar to the bindings,
     but it only concerns the formals of @('fn'), not the @('a-ptr') variables.
     The instantiation is used on the guard and termination theorems of @('fn'),
     and therefore it can only concern the formals of @('fn')."))
  (b* (((when (endp typed-formals)) (mv nil nil nil nil))
       ((cons formal type) (car typed-formals))
       (formal-ptr (add-suffix-to-fn formal "-PTR"))
       (formal-objdes `(value-pointer->designator ,formal-ptr))
       (formal-id `(ident ,(symbol-name formal)))
       (pointerp (type-case type :pointer))
       (bindings
        (if fn-recursivep
            (if pointerp
                (list `(,formal-ptr (read-var ,formal-id ,compst-var))
                      `(,formal (read-object ,formal-objdes ,compst-var)))
              (list `(,formal (read-var ,formal-id ,compst-var))))
          (if pointerp
              (list `(,formal (read-object ,formal-objdes ,compst-var)))
            nil)))
       (subst? (and pointerp
                    (list (cons formal formal-ptr))))
       (hyps (and pointerp
                  (list `(valuep ,formal-ptr)
                        `(value-case ,formal-ptr :pointer)
                        `(not (value-pointer-nullp ,formal-ptr))
                        `(equal (objdesign-kind
                                 (value-pointer->designator ,formal-ptr))
                                :address)
                        `(equal (value-pointer->reftype ,formal-ptr)
                                ,(type-to-maker (type-pointer->to type))))))
       (inst (if fn-recursivep
                 (if pointerp
                     (list `(,formal (read-object (value-pointer->designator
                                                   (read-var ,formal-id
                                                             ,compst-var))
                                                  ,compst-var)))
                   (list `(,formal (read-var ,formal-id ,compst-var))))
               (if pointerp
                   (list `(,formal (read-object ,formal-objdes ,compst-var)))
                 nil)))
       ((mv more-bindings more-hyps more-subst more-inst)
        (atc-gen-outer-bindings-and-hyps (cdr typed-formals)
                                         compst-var
                                         fn-recursivep)))
    (mv (append bindings more-bindings)
        (append hyps more-hyps)
        (append subst? more-subst)
        (append inst more-inst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-object-disjoint-hyps ((pointer-vars symbol-listp))
  :returns (hyps true-listp)
  :short "Generate hypotheses saying that the pointers
          designate disjoint objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 functions that represent C functions and loops
     take and return whole arrays and structured as inputs:
     thus, the possible modification to each array or structure
     only applies to that array or structure.
     In the generated C code,
     arrays and structures are passed as pointers instead.
     If two of these pointers, for different arrays or structures in ACL2,
     were equal, then the C code would not be correct in general,
     because modifying one array or structure would also modify the other one:
     there is, in fact, just one array or structure,
     which both pointers point to,
     but here we are talking about the two different arrays or structures
     in the ACL2 representation.
     It is thus critical that the generated correctness theorems
     include the assumption that all the pointers are distinct.
     This is the case
     not only for the arrays and structures that may be modified,
     but also for the ones that may not:
     otherwise, we could not rely on the latter to be unmodified,
     during the symbolic execution proof.")
   (xdoc::p
    "We generate these hypotheses here,
     by going through the pointer variables involved in
     the correctness theorem of the C function or loop.
     More precisely, we generate hypotheses saying that
     the object designated by the pointers are pairwise disjoint."))
  (b* (((when (endp pointer-vars)) nil)
       (var (car pointer-vars))
       (hyps (loop$ for var2 in (cdr pointer-vars)
                    collect `(object-disjointp
                              (value-pointer->designator ,var)
                              (value-pointer->designator ,var2))))
       (more-hyps (atc-gen-object-disjoint-hyps (cdr pointer-vars))))
    (append hyps more-hyps))
  :prepwork ((local (in-theory (enable acl2::loop-book-theory)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-final-compustate ((affect symbol-listp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (pointer-subst symbol-symbol-alistp)
                                       (compst-var symbolp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C function says that
     executing the function on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     and on generic arguments
     yields an optional result (absent if the function is @('void'))
     and a computation state obtained by modifying
     zero or more arrays and structures in the computation state.
     These are the arrays and structures affected by the C function,
     which the correctness theorem binds to the results of
     the ACL2 function that represents the C function.
     The modified computation state is expressed as
     a nest of @(tsee write-object) calls.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "The parameter @('affect') passed to this code
     consists of the formals of @('fn') that represent arrays and structures
     affected by the body of the ACL2 function that represents the C function.
     The parameter @('pointer-subst') is
     the result of @(tsee atc-gen-outer-bindings-and-hyps)
     that maps array and structure formals of the ACL2 function
     to the corresponding pointer variables used by the correctness theorems.
     Thus, we go through @('affect'),
     looking up the corresponding pointer variables in @('pointer-subst'),
     and we construct
     each nested @(tsee write-object) call,
     which needs both a pointer and an array or structure;
     we distinguish between arrays and structures
     via the types of the formals.")
   (xdoc::p
    "Note that, in the correctness theorem,
     the new array and structure variables are bound to
     the possibly modified arrays and structures returned by the ACL2 function:
     these new array and structure variables are obtained by adding @('-NEW')
     to the corresponding formals of the ACL2 function;
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers."))
  (b* (((when (endp affect)) compst-var)
       (formal (car affect))
       (type (cdr (assoc-eq formal typed-formals)))
       ((when (not type))
        (raise "Internal error: formal ~x0 not found." formal))
       ((unless (type-case type :pointer))
        (raise "Internal error: affected formal ~x0 has type ~x1."
               formal type)))
    `(write-object (value-pointer->designator ,(cdr (assoc-eq formal
                                                              pointer-subst)))
                   ,(add-suffix-to-fn formal "-NEW")
                   ,(atc-gen-cfun-final-compustate (cdr affect)
                                                   typed-formals
                                                   pointer-subst
                                                   compst-var)))
  :prepwork
  ((defrulel lemma
     (implies (symbol-symbol-alistp x)
              (alistp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-correct-thm ((fn symbolp)
                                  (typed-formals atc-symbol-type-alistp)
                                  (type typep)
                                  (affect symbol-listp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prec-tags atc-string-taginfo-alistp)
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
     an optional C result and zero or more modified arrays and structures.
     If it returns a C result (i.e. if the C function is not @('void')),
     we bind a result variable to it;
     the value is @('nil') if the C function is @('void').
     We also bind the formals that are arrays or structures
     to the (other or only) results of @('fn') (if any).
     We actually use new variables for the latter,
     for greater clarity in the theorem formulation:
     the new variables are obtained by adding @('-NEW')
     to the corresponding array and structure formals of @('fn');
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers.")
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
     The proof is carried out in the theory that consists of exactly
     the general rules in @(tsee *atc-all-rules*),
     some structure-specific rules that are similar to
     rules for arrays in @(tsee *atc-all-rules*),
     plus the definition of @(tsee not) (more on this below),
     plus the definition of @('fn') (clearly),
     plus the theorems about the results of the functions called by @('fn'),
     plust the type prescriptions of the functions called by @('fn'),
     plus the correctness theorems of the functions called by @('fn'),
     plus the theorems asserting that
     the measures of the called recursive functions are naturals,
     plus the theorem about the current function in the function environment;
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
     We enable @(tsee not) because, without it,
     we have found at least one case in which some ACL2 heuristic defeats
     what should be a propositional inference;
     the issue is related to clausification,
     and enabling @(tsee not) seems to overcome the issue,
     at least in that case we found.")
   (xdoc::p
    "Furthermore, we generate a @(':use') hint
     to augment the theorem's formula with the guard theorem of @('fn'),
     with the pointer arguments replaced by
     the dereferenced arrays and structures.
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
  (b* ((name (cdr (assoc-eq fn fn-thms)))
       (formals (strip-cars typed-formals))
       (compst-var (genvar 'atc "COMPST" nil formals))
       (fenv-var (genvar 'atc "FENV" nil formals))
       (limit-var (genvar 'atc "LIMIT" nil formals))
       (result-var (if (type-case type :void)
                       nil
                     (genvar 'atc "RESULT" nil formals)))
       ((mv formals-bindings pointer-hyps pointer-subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var nil))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs pointer-subst)))
       (hyps `(and (compustatep ,compst-var)
                   (equal ,fenv-var (init-fun-env ,prog-const))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@pointer-hyps
                   ,@diff-pointer-hyps
                   ,(untranslate (uguard+ fn wrld) nil wrld)))
       (exec-fun-args (fsublis-var-lst pointer-subst formals))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (fn-results (append (if (type-case type :void)
                               nil
                             (list result-var))
                           affect-new))
       (fn-binder (if (endp (cdr fn-results))
                      (car fn-results)
                    `(mv ,@fn-results)))
       (final-compst
        (atc-gen-cfun-final-compustate affect
                                       typed-formals
                                       pointer-subst
                                       compst-var))
       (concl `(equal (exec-fun (ident ,(symbol-name fn))
                                (list ,@exec-fun-args)
                                ,compst-var
                                ,fenv-var
                                ,limit-var)
                      (b* ((,fn-binder (,fn ,@formals)))
                        (mv ,result-var ,final-compst))))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions-called
        (loop$ for called in (strip-cars prec-fns)
               collect `(:t ,called)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (hints `(("Goal"
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               not
                               ,fn
                               ,@result-thms
                               ,@struct-reader-return-thms
                               ,@struct-writer-return-thms
                               ,@type-of-value-thms
                               ,@member-read-thms
                               ,@member-write-thms
                               ,@type-prescriptions-called
                               ,@type-prescriptions-struct-readers
                               ,@correct-thms
                               ,@measure-thms
                               ,fn-fun-env-thm))
                 :use (:instance (:guard-theorem ,fn)
                       :extra-bindings-ok ,@instantiation)
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
  :short "Lift @(tsee atc-formal-pointerp) to lists."
  (atc-formal-pointerp x typed-formals)
  :true-listp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-find-affected ((fn symbolp)
                           (term pseudo-termp)
                           (typed-formals atc-symbol-type-alistp)
                           (prec-fns atc-symbol-fninfo-alistp)
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
    "This is used on the body of each non-recursive target function @('fn'),
     in order to determine the variables affected by it,
     according to the nomenclature in the user documentation.
     We visit the leaves of the term
     according to the @(tsee if) and @(tsee let) structure,
     and ensure that they all have the same form,
     which must be one of the following forms:")
   (xdoc::ul
    (xdoc::li
     "A call of a (recursive or non-recursive) target function @('fn0')
      that precedes @('fn') in the list of targets.
      In this case, @('term') affects the same variables as @('fn0').
      We use @(tsee atc-check-cfun-call) and @(tsee atc-check-loop-call)
      to check if the term is a call of a target function
      and to retrieve that function's affected variables:
      we pass @('nil') as the variable-term alist,
      because it does not change the returned affected variables,
      which is the only thing we care about here,
      ignoring all the other results.")
    (xdoc::li
     "A formal parameter @('var') of @('fn') with pointer type.
      In this case, @('term') affects the list of variables @('(var)').")
    (xdoc::li
     "A term @('ret') that is not a call of @('fn0') as above
      and is not a formal parameter of @('fn') of pointer type.
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
             ((when mbtp) (atc-find-affected fn
                                             then
                                             typed-formals
                                             prec-fns
                                             ctx
                                             state))
             ((mv mbt$p &) (check-mbt$-call test))
             ((when mbt$p) (atc-find-affected fn
                                              then
                                              typed-formals
                                              prec-fns
                                              ctx
                                              state))
             ((er then-affected) (atc-find-affected fn
                                                    then
                                                    typed-formals
                                                    prec-fns
                                                    ctx
                                                    state))
             ((er else-affected) (atc-find-affected fn
                                                    else
                                                    typed-formals
                                                    prec-fns
                                                    ctx
                                                    state)))
          (if (equal then-affected else-affected)
              (acl2::value then-affected)
            (er-soft+ ctx t nil
                      "When generating code for function ~x0, ~
                       an IF branch affects variables ~x1, ~
                       while the other branch affects variables ~x2: ~
                       this is disallowed."
                      fn then-affected else-affected))))
       ((mv okp & body &) (fty-check-lambda-call term))
       ((when okp) (atc-find-affected fn
                                      body
                                      typed-formals
                                      prec-fns
                                      ctx
                                      state))
       ((mv okp & & & & affected &)
        (atc-check-cfun-call term nil prec-fns (w state)))
       ((when okp) (acl2::value affected))
       ((mv okp & & & affected & &)
        (atc-check-loop-call term nil prec-fns))
       ((when okp) (acl2::value affected))
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
           (enable symbol-listp-of-strip-cars-when-atc-symbol-type-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fundef ((fn symbolp)
                        (prec-fns atc-symbol-fninfo-alistp)
                        (prec-tags atc-string-taginfo-alistp)
                        (proofs booleanp)
                        (prog-const symbolp)
                        (init-fun-env-thm symbolp)
                        (fn-thms symbol-symbol-alistp)
                        (print evmac-input-print-p)
                        (names-to-avoid symbol-listp)
                        (ctx ctxp)
                        state)
  :returns (mv erp
               (val "A @('(tuple (fundef fundefp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-prec-fns atc-symbol-fninfo-alistp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C function definition
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
       ((unless (ident-stringp name))
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
       ((er typed-formals) (atc-typed-formals fn prec-tags ctx state))
       ((er params) (atc-gen-param-declon-list typed-formals fn ctx state))
       (body (ubody+ fn wrld))
       ((er affect) (atc-find-affected fn
                                       body
                                       typed-formals
                                       prec-fns
                                       ctx
                                       state))
       ((er (list items type limit)) (atc-gen-stmt body
                                                   nil
                                                   (list typed-formals)
                                                   nil
                                                   affect
                                                   fn
                                                   prec-fns
                                                   prec-tags
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
       (id (make-ident :name name))
       ((mv tyspec &) (ident+type-to-tyspec+declor id type))
       (fundef (make-fundef :tyspec tyspec
                            :declor (make-fun-declor-base :name id
                                                          :params params)
                            :body items))
       (finfo (fun-info-from-fundef fundef))
       (limit `(binary-+ '2 ,limit))
       ((mv local-events
            exported-events
            fn-fun-env-thm
            fn-result-thm
            fn-correct-thm
            names-to-avoid)
        (if proofs
            (b* (((mv fn-fun-env-events
                      fn-fun-env-thm
                      names-to-avoid)
                  (atc-gen-cfun-fun-env-thm fn
                                            prog-const
                                            finfo
                                            init-fun-env-thm
                                            names-to-avoid
                                            wrld))
                 ((mv fn-result-events
                      fn-result-thm
                      names-to-avoid)
                  (atc-gen-fn-result-thm fn
                                         type
                                         affect
                                         typed-formals
                                         prec-fns
                                         prec-tags
                                         names-to-avoid
                                         wrld))
                 ((mv fn-correct-local-events
                      fn-correct-exported-events
                      fn-correct-thm)
                  (atc-gen-cfun-correct-thm fn
                                            typed-formals
                                            type
                                            affect
                                            prec-fns
                                            prec-tags
                                            prog-const
                                            fn-thms
                                            fn-fun-env-thm
                                            limit
                                            wrld))
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
                 (exported-events fn-correct-exported-events))
              (mv local-events
                  exported-events
                  fn-fun-env-thm
                  fn-result-thm
                  fn-correct-thm
                  names-to-avoid))
          (mv nil nil nil nil nil names-to-avoid)))
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
    (acl2::value (list fundef
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
               ((mv okp subst) (one-way-unify meas-gen meas-inst))
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
              `(mv ,@(symbol-list-fix affect))
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

(define atc-gen-loop-test-correct-thm ((fn symbolp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (loop-test exprp)
                                       (test-term pseudo-termp)
                                       (fn-thms symbol-symbol-alistp)
                                       (prec-tags atc-string-taginfo-alistp)
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
       (formals (strip-cars typed-formals))
       (compst-var (genvar 'atc "COMPST" nil formals))
       ((mv formals-bindings pointer-hyps & instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t))
       (hyps `(and (compustatep ,compst-var)
                   (not (equal (compustate-frames-number ,compst-var) 0))
                   ,@pointer-hyps
                   ,(untranslate (uguard+ fn wrld) nil wrld)))
       (concl `(equal (exec-test (exec-expr-pure ',loop-test ,compst-var))
                      ,test-term))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not
                               ,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               ,@struct-reader-return-thms
                               ,@member-read-thms))
                 :use ((:instance (:guard-theorem ,fn)
                        :extra-bindings-ok ,@instantiation))
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
                                       (pointer-subst symbol-symbol-alistp)
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
     one or more variables and zero or more arrays in the computation state.
     These are the variables and arrays affected by the loop,
     which the correctness theorem binds to the results of the loop function,
     and which have corresponding named variables and heap arrays
     in the computation state.
     The modified computation state is expressed as
     a nest of @(tsee write-var) and @(tsee write-object) calls.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "Note that, in the correctness theorem,
     the new array variables are bound to
     the possibly modified arrays returned by the ACL2 function:
     these new array variables are obtained by adding @('-NEW')
     to the corresponding formals of the ACL2 function;
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers."))
  (b* (((when (endp mod-vars)) compst-var)
       (mod-var (car mod-vars))
       (ptr (cdr (assoc-eq mod-var pointer-subst))))
    (if ptr
        `(write-object (value-pointer->designator ,ptr)
                       ,(add-suffix-to-fn mod-var "-NEW")
                       ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                       pointer-subst
                                                       compst-var))
      `(write-var (ident ,(symbol-name (car mod-vars)))
                  ,(add-suffix-to-fn (car mod-vars) "-NEW")
                  ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                  pointer-subst
                                                  compst-var)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-body-correct-thm ((fn symbolp)
                                       (typed-formals atc-symbol-type-alistp)
                                       (affect symbol-listp)
                                       (loop-body stmtp)
                                       (test-term pseudo-termp)
                                       (body-term pseudo-termp)
                                       (prec-fns atc-symbol-fninfo-alistp)
                                       (prec-tags atc-string-taginfo-alistp)
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
       ((mv formals-bindings pointer-hyps pointer-subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs pointer-subst)))
       (hyps `(and (compustatep ,compst-var)
                   (not (equal (compustate-frames-number ,compst-var) 0))
                   (equal ,fenv-var (init-fun-env ,prog-const))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@pointer-hyps
                   ,@diff-pointer-hyps
                   ,(untranslate (uguard+ fn wrld) nil wrld)
                   ,(untranslate test-term nil wrld)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (affect-binder (if (endp (cdr affect-new))
                          (car affect-new)
                        `(mv ,@affect-new)))
       (final-compst (atc-gen-loop-final-compustate affect
                                                    pointer-subst
                                                    compst-var))
       (body-term (atc-loop-body-term-subst body-term fn affect))
       (concl `(equal (exec-stmt ',loop-body ,compst-var ,fenv-var ,limit-var)
                      (b* ((,affect-binder ,body-term))
                        (mv nil ,final-compst))))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions-called
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               not
                               ,@struct-reader-return-thms
                               ,@struct-writer-return-thms
                               ,@type-of-value-thms
                               ,@member-read-thms
                               ,@member-write-thms
                               ,@type-prescriptions-called
                               ,@type-prescriptions-struct-readers
                               ,@result-thms
                               ,@correct-thms
                               ,@measure-thms))
                 :use ((:instance (:guard-theorem ,fn)
                        :extra-bindings-ok ,@instantiation))
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
                                  (typed-formals atc-symbol-type-alistp)
                                  (affect symbol-listp)
                                  (loop-test exprp)
                                  (loop-body stmtp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prec-tags atc-string-taginfo-alistp)
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
     The theory for the subgoal includes
     fewer rules than the ones for the full symbolic execution,
     because we use the correctness theorems for the loop test and body
     as rewrite rules instead, which take care of most of the execution.
     The @(':expand') hint applies to the loop function,
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
       ((mv formals-bindings pointer-hyps pointer-subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs pointer-subst)))
       (hyps `(and (compustatep ,compst-var)
                   (not (equal (compustate-frames-number ,compst-var) 0))
                   (equal ,fenv-var (init-fun-env ,prog-const))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@pointer-hyps
                   ,@diff-pointer-hyps
                   ,(untranslate (uguard+ fn wrld) nil wrld)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (affect-binder (if (endp (cdr affect-new))
                          (car affect-new)
                        `(mv ,@affect-new)))
       (final-compst (atc-gen-loop-final-compustate affect
                                                    pointer-subst
                                                    compst-var))
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
       (formula-lemma `(b* (,@formals-bindings) (implies ,hyps ,concl-lemma)))
       (formula-thm `(b* (,@formals-bindings) (implies ,hyps ,concl-thm)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (result-thms (cons fn-result-thm result-thms))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms prec-fns called-fns))
       (type-prescriptions-called
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (lemma-hints `(("Goal"
                       :do-not-induct t
                       :in-theory (append
                                   *atc-symbolic-computation-state-rules*
                                   *atc-valuep-rules*
                                   *atc-value-listp-rules*
                                   *atc-value-optionp-rules*
                                   *atc-type-of-value-rules*
                                   *atc-type-of-value-option-rules*
                                   *atc-value-array->elemtype-rules*
                                   *atc-array-length-rules*
                                   *atc-array-length-write-rules*
                                   *atc-other-executable-counterpart-rules*
                                   *atc-other-definition-rules*
                                   *atc-distributivity-over-if-rewrite-rules*
                                   *atc-identifier-rules*
                                   *atc-not-rules*
                                   *atc-integer-size-rules*
                                   *atc-other-rewrite-rules*
                                   *atc-integer-ops-1-return-rewrite-rules*
                                   *atc-integer-ops-2-return-rewrite-rules*
                                   *atc-integer-convs-return-rewrite-rules*
                                   *atc-array-read-return-rewrite-rules*
                                   *atc-array-write-return-rewrite-rules*
                                   *atc-more-rewrite-rules*
                                   *atc-type-prescription-rules*
                                   *atc-compound-recognizer-rules*
                                   *integer-value-disjoint-rules*
                                   *array-value-disjoint-rules*
                                   '(,@not-error-thms
                                     ,@valuep-thms
                                     not
                                     ,exec-stmt-while-for-fn
                                     ,@struct-reader-return-thms
                                     ,@struct-writer-return-thms
                                     ,@type-of-value-thms
                                     ,@member-read-thms
                                     ,@member-write-thms
                                     ,@type-prescriptions-called
                                     ,@type-prescriptions-struct-readers
                                     ,@result-thms
                                     ,@correct-thms
                                     ,@measure-thms
                                     ,natp-of-measure-of-fn-thm
                                     ,correct-test-thm
                                     ,correct-body-thm))
                       :use ((:instance (:guard-theorem ,fn)
                              :extra-bindings-ok ,@instantiation)
                             (:instance ,termination-of-fn-thm
                              :extra-bindings-ok ,@instantiation))
                       :expand (:lambdas
                                (,fn ,@(fsublis-var-lst
                                        (doublets-to-alist
                                         instantiation)
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
                      (prec-tags atc-string-taginfo-alistp)
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
       ((mv measure-of-fn-event
            measure-of-fn
            measure-formals
            names-to-avoid)
        (if proofs
            (atc-gen-loop-measure-fn fn names-to-avoid wrld)
          (mv '(_) nil nil names-to-avoid)))
       ((er typed-formals) (atc-typed-formals fn prec-tags ctx state))
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
                           prec-tags
                           proofs
                           ctx
                           state))
       ((er (list local-events
                  exported-events
                  natp-of-measure-of-fn-thm
                  fn-result-thm
                  fn-correct-thm
                  names-to-avoid))
        (if proofs
            (b* (((mv fn-result-events
                      fn-result-thm
                      names-to-avoid)
                  (atc-gen-fn-result-thm fn
                                         nil
                                         loop-affect
                                         typed-formals
                                         prec-fns
                                         prec-tags
                                         names-to-avoid
                                         wrld))
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
                                                 typed-formals
                                                 loop-test
                                                 test-term
                                                 fn-thms
                                                 prec-tags
                                                 names-to-avoid
                                                 wrld))
                 ((mv body-local-events
                      correct-body-thm
                      names-to-avoid)
                  (atc-gen-loop-body-correct-thm fn
                                                 typed-formals
                                                 loop-affect
                                                 loop-body
                                                 test-term
                                                 body-term
                                                 prec-fns
                                                 prec-tags
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
                                            typed-formals
                                            loop-affect
                                            loop-test
                                            loop-body
                                            prec-fns
                                            prec-tags
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
                 (local-events (append progress-start?
                                       (and measure-of-fn
                                            (list measure-of-fn-event))
                                       fn-result-events
                                       exec-stmt-while-events
                                       (list natp-of-measure-of-fn-thm-event)
                                       (list termination-of-fn-thm-event)
                                       test-local-events
                                       body-local-events
                                       correct-local-events
                                       progress-end?))
                 (exported-events correct-exported-events))
              (acl2::value
               (list local-events
                     exported-events
                     natp-of-measure-of-fn-thm
                     fn-result-thm
                     fn-correct-thm
                     names-to-avoid)))
          (acl2::value (list nil nil nil nil nil names-to-avoid))))
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

(define atc-gen-tag-member-read-thms ((tag identp)
                                      (recognizer symbolp)
                                      (fixer-recognizer-thm symbolp)
                                      (not-error-thm symbolp)
                                      (meminfo defstruct-member-infop)
                                      (names-to-avoid symbol-listp)
                                      (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (member-read-thms "A @(tsee symbol-listp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorems to rewrite
          the execution of certain pure expressions to structure reads,
          for a member of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This class of theorems are the structure counterpart of
     the ones that rewrite @(tsee exec-arrsub) to array readers,
     generated in @(see atc-exec-arrsub-rules-generation).")
   (xdoc::p
    "For a scalar member (which must have integer type),
     we generate a single theorem that
     rewrites calls of @(tsee exec-memberp)
     to calls of the reader.")
   (xdoc::p
    "For an array member (which must have integer element type),
     we generate 10 theorems, one for each integer index type.
     The theorem rewrites calls of @(tsee exec-arrsub-of-memberp)
     to calls of the readers.
     The generation of these theorems relies on the fact that
     the order of the readers and the checkers matches the order of
     the types in @(tsee *integer-nonbool-nonchar-types*).
     Note that the @(tsee defstruct-member-info)
     contains 11 readers and 11 checkers,
     where the first reader and checker operate on ACL2 integers,
     while the other 10 readers and 10 checkers operate on C integers.
     We iterate through the 10 readers and checkers on C integers,
     while using the reader and checker on ACL2 integers at each iteration."))
  (b* ((memtype (defstruct-member-info->memtype meminfo))
       (memname (member-type->name memtype))
       (type (member-type->type memtype))
       (readers (defstruct-member-info->readers meminfo))
       (checkers (defstruct-member-info->checkers meminfo))
       ((when (type-integerp type))
        (b* (((unless (and (consp readers)
                           (endp (cdr readers))))
              (prog2$
               (raise "Internal error: not one reader ~x0." readers)
               (mv nil nil nil)))
             (reader (car readers))
             (thm-name (pack 'exec-member-read-when-
                             recognizer
                             '-and-
                             (ident->name memname)))
             ((mv thm-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (formula
              `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'ptr)
                             (valuep ptr)
                             (value-case ptr :pointer)
                             (not (value-pointer-nullp ptr))
                             (equal (value-pointer->reftype ptr)
                                    (type-struct (ident ,(ident->name tag))))
                             (equal struct
                                    (read-object (value-pointer->designator ptr)
                                                 compst))
                             (,recognizer struct))
                        (equal (exec-memberp ptr
                                             (ident ,(ident->name memname))
                                             compst)
                               (,reader struct))))
             (hints `(("Goal"
                       :in-theory
                       '(exec-memberp
                         not-errorp-when-valuep-rewrite
                         value-resultp-when-valuep
                         value-result-fix-when-value-resultp
                         ,recognizer
                         ,reader
                         ,not-error-thm
                         ,fixer-recognizer-thm))))
             ((mv event &) (evmac-generate-defthm thm-name
                                                  :formula formula
                                                  :hints hints
                                                  :enable nil)))
          (mv (list event) (list thm-name) names-to-avoid)))
       ((unless (type-case type :array))
        (prog2$
         (raise "Internal error: member type ~x0." type)
         (mv nil nil nil)))
       (elemtype (type-array->of type))
       ((unless (type-integerp elemtype))
        (prog2$
         (raise "Internal error: array member element type ~x0." elemtype)
         (mv nil nil nil))))
    (atc-gen-tag-member-read-thms-aux tag
                                      recognizer
                                      fixer-recognizer-thm
                                      memname
                                      elemtype
                                      *integer-nonbool-nonchar-types*
                                      (car readers)
                                      (car checkers)
                                      (cdr readers)
                                      (cdr checkers)
                                      names-to-avoid
                                      wrld))

  :prepwork
  ((define atc-gen-tag-member-read-thms-aux ((tag identp)
                                             (recognizer symbolp)
                                             (fixer-recognizer-thm symbolp)
                                             (memname identp)
                                             (elemtype typep)
                                             (indextypes type-listp)
                                             (reader-acl2int symbolp)
                                             (checker-acl2int symbolp)
                                             (readers symbol-listp)
                                             (checkers symbol-listp)
                                             (names-to-avoid symbol-listp)
                                             (wrld plist-worldp))
     :guard (and (type-integerp elemtype)
                 (type-integer-listp indextypes))
     :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
                  (member-read-thms "A @(tsee symbol-listp).")
                  (updated-names-to-avoid "A @(tsee symbol-listp)."))
     :mode :program
     :parents nil
     (b* (((when (endp indextypes)) (mv nil nil nil))
          (indextype (car indextypes))
          (reader (car readers))
          (checker (car checkers))
          (indexfixtype (integer-type-to-fixtype indextype))
          (elemfixtype (integer-type-to-fixtype elemtype))
          (indextypep (pack indexfixtype 'p))
          (indextype-integer-value (pack indexfixtype '-integer-value))
          (array-reader (pack elemfixtype '-array-read-alt-def))
          (array-checker (pack elemfixtype '-array-index-okp))
          (not-error-array-thm (pack 'not-errorp-when- elemfixtype '-arrayp))
          (kind-array-thm (pack 'value-kind-when- elemfixtype '-arrayp))
          (valuep-when-indextype (pack 'valuep-when- indextypep))
          (type-thm (pack indexfixtype '->get$inline))
          (thm-name (pack 'exec-member-read-when-
                          recognizer
                          '-and-
                          (ident->name memname)
                          '-
                          indexfixtype))
          ((mv thm-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (formula
           `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'ptr)
                          (valuep ptr)
                          (value-case ptr :pointer)
                          (not (value-pointer-nullp ptr))
                          (equal (value-pointer->reftype ptr)
                                 (type-struct (ident ,(ident->name tag))))
                          (equal struct
                                 (read-object (value-pointer->designator ptr)
                                              compst))
                          (,recognizer struct)
                          (equal array
                                 (value-struct-read (ident
                                                     ,(ident->name memname))
                                                    struct))
                          (,indextypep index)
                          (,checker index))
                     (equal (exec-arrsub-of-memberp ptr
                                                    (ident
                                                     ,(ident->name memname))
                                                    index
                                                    compst)
                            (,reader index struct))))
          (hints `(("Goal"
                    :in-theory
                    '(exec-arrsub-of-memberp
                      value-struct-read
                      exec-integer
                      ifix
                      integer-range-p
                      not-errorp-when-valuep-rewrite
                      value-fix-when-valuep
                      value-result-fix-when-value-resultp
                      value-resultp-when-valuep
                      value-integerp
                      value-unsigned-integerp-alt-def
                      value-signed-integerp-alt-def
                      (:e ident)
                      ,@*integer-value-disjoint-rules*
                      ,recognizer
                      ,fixer-recognizer-thm
                      ,checker
                      ,checker-acl2int
                      ,reader
                      ,reader-acl2int
                      ,indextype-integer-value
                      ,array-reader
                      ,array-checker
                      ,not-error-array-thm
                      ,kind-array-thm
                      ,valuep-when-indextype
                      (:t ,type-thm)))))
          ((mv event &) (evmac-generate-defthm thm-name
                                               :formula formula
                                               :hints hints
                                               :enable nil))
          ((mv events thm-names names-to-avoid)
           (atc-gen-tag-member-read-thms-aux tag
                                             recognizer
                                             fixer-recognizer-thm
                                             memname
                                             elemtype
                                             (cdr indextypes)
                                             reader-acl2int
                                             checker-acl2int
                                             (cdr readers)
                                             (cdr checkers)
                                             names-to-avoid
                                             wrld)))
       (mv (cons event events)
           (cons thm-name thm-names)
           names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-read-all-thms ((tag identp)
                                          (recognizer symbolp)
                                          (fixer-recognizer-thm symbolp)
                                          (not-error-thm symbolp)
                                          (meminfos defstruct-member-info-listp)
                                          (names-to-avoid symbol-listp)
                                          (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (member-read-thms "A @(tsee symbol-listp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorems to rewrite
          the execution of certain pure expressions to structure reads,
          for all the members of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on @('readers') to be in the same order as @('members')."))
  (b* (((when (endp meminfos)) (mv nil nil names-to-avoid))
       ((mv events thms names-to-avoid)
        (atc-gen-tag-member-read-thms tag
                                      recognizer
                                      fixer-recognizer-thm
                                      not-error-thm
                                      (car meminfos)
                                      names-to-avoid
                                      wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-read-all-thms tag
                                          recognizer
                                          fixer-recognizer-thm
                                          not-error-thm
                                          (cdr meminfos)
                                          names-to-avoid
                                          wrld)))
    (mv (append events more-events)
        (append thms more-thms)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-write-thms ((tag identp)
                                       (recognizer symbolp)
                                       (fixer-recognizer-thm symbolp)
                                       (not-error-thm symbolp)
                                       (type-of-value-thm symbolp)
                                       (meminfo defstruct-member-infop)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (member-write-thms "A @(tsee symbol-listp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorems to rewrite
          the execution of certain assignment expressions to structure writes,
          for a member of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This class of theorems are the structure counterpart of
     the ones that rewrite @(tsee exec-expr-asg)
     that have @(':arrsub') left expressions
     to array writers,
     in @(see atc-exec-expr-asg-arrsub-rules-generation).")
   (xdoc::p
    "For a scalar member (which must have integer type),
     we generate a single theorem that
     rewrites certain calls of @(tsee exec-expr-asg)
     to calls of the writer.")
   (xdoc::p
    "For an array member (which must have integer element type),
     we generate 10 theorems, one for each integer index type.
     The theorem rewrites certain calls of @(tsee exec-expr-asg)
     to calls of the writers.
     The generation of these theorems relies on the fact that
     the order of the writers and the checkers matches the order of
     the types in @(tsee *integer-nonbool-nonchar-types*).
     Note that the @(tsee defstruct-member-info)
     contains 11 writers and 11 checkers,
     where the first writer and checker operate on ACL2 integers,
     while the other 10 writers and 10 checkers operate on C integers.
     We iterate through the 10 writers and checkers on C integers,
     while using the writer and checker on ACL2 integers at each iteration."))
  (b* ((memtype (defstruct-member-info->memtype meminfo))
       (memname (member-type->name memtype))
       (type (member-type->type memtype))
       (writers (defstruct-member-info->writers meminfo))
       (writer-return-thms (defstruct-member-info->writer-return-thms meminfo))
       (writer-return-thm (car writer-return-thms))
       (checkers (defstruct-member-info->checkers meminfo))
       ((when (type-integerp type))
        (b* (((unless (and (consp writers)
                           (endp (cdr writers))))
              (prog2$
               (raise "Internal error: not one writer ~x0." writers)
               (mv nil nil nil)))
             (writer (car writers))
             (thm-name (pack 'exec-member-write-when-
                             recognizer
                             '-and-
                             (ident->name memname)))
             ((mv thm-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (typep (atc-type-to-recognizer type wrld))
             ((unless typep)
              (raise "Internal error: unsupported member type ~x0." type)
              (mv nil nil nil))
             (formula
              `(implies (and (syntaxp (quotep e))
                             (equal (expr-kind e) :binary)
                             (equal (binop-kind (expr-binary->op e)) :asg)
                             (equal left (expr-binary->arg1 e))
                             (equal right (expr-binary->arg2 e))
                             (equal (expr-kind left) :memberp)
                             (equal target (expr-memberp->target left))
                             (equal member (expr-memberp->name left))
                             (equal (expr-kind target) :ident)
                             (equal member (ident ,(ident->name memname)))
                             (not (zp limit))
                             (equal ptr (read-var (expr-ident->get target)
                                                  compst))
                             (valuep ptr)
                             (value-case ptr :pointer)
                             (not (value-pointer-nullp ptr))
                             (equal (value-pointer->reftype ptr)
                                    (type-struct (ident ,(ident->name tag))))
                             (equal struct
                                    (read-object (value-pointer->designator ptr)
                                                 compst))
                             (,recognizer struct)
                             (equal val (exec-expr-pure right compst))
                             (,typep val))
                        (equal (exec-expr-asg e compst fenv limit)
                               (write-object (value-pointer->designator ptr)
                                             (,writer val struct)
                                             compst))))
             (hints `(("Goal"
                       :in-theory
                       '(exec-expr-asg
                         not-errorp-when-valuep-rewrite
                         valuep-when-ucharp
                         valuep-when-scharp
                         valuep-when-ushortp
                         valuep-when-sshortp
                         valuep-when-uintp
                         valuep-when-sintp
                         valuep-when-ulongp
                         valuep-when-slongp
                         valuep-when-ullongp
                         valuep-when-sllongp
                         consp-when-ucharp
                         consp-when-scharp
                         consp-when-ushortp
                         consp-when-sshortp
                         consp-when-uintp
                         consp-when-sintp
                         consp-when-ulongp
                         consp-when-slongp
                         consp-when-ullongp
                         consp-when-sllongp
                         uchar-fix-when-ucharp
                         schar-fix-when-scharp
                         ushort-fix-when-ushortp
                         sshort-fix-when-sshortp
                         uint-fix-when-uintp
                         sint-fix-when-sintp
                         ulong-fix-when-ulongp
                         slong-fix-when-slongp
                         ullong-fix-when-ullongp
                         sllong-fix-when-sllongp
                         ,writer
                         ,not-error-thm
                         ,recognizer
                         ,fixer-recognizer-thm
                         ,type-of-value-thm)
                       :use
                       (:instance
                        ,writer-return-thm
                        (val (b* ((left (expr-binary->arg1 e)))
                               (exec-expr-pure (expr-binary->arg2 e) compst)))
                        (struct (b* ((left (expr-binary->arg1 e))
                                     (target (expr-memberp->target left))
                                     (ptr (read-var (c::expr-ident->get target)
                                                    compst))
                                     (struct (read-object
                                              (value-pointer->designator ptr)
                                              compst)))
                                  struct))))))
             ((mv event &) (evmac-generate-defthm thm-name
                                                  :formula formula
                                                  :hints hints
                                                  :enable nil)))
          (mv (list event) (list thm-name) names-to-avoid)))
       ((unless (type-case type :array))
        (prog2$
         (raise "Internal error: member type ~x0." type)
         (mv nil nil nil)))
       (elemtype (type-array->of type))
       ((unless (type-integerp elemtype))
        (prog2$
         (raise "Internal error: array member element type ~x0." elemtype)
         (mv nil nil nil))))
    (atc-gen-tag-member-write-thms-aux tag
                                       recognizer
                                       fixer-recognizer-thm
                                       memname
                                       elemtype
                                       *integer-nonbool-nonchar-types*
                                       (car writers)
                                       (car checkers)
                                       (cdr writers)
                                       (cdr checkers)
                                       writer-return-thm
                                       not-error-thm
                                       type-of-value-thm
                                       names-to-avoid
                                       wrld))

  :prepwork
  ((define atc-gen-tag-member-write-thms-aux ((tag identp)
                                              (recognizer symbolp)
                                              (fixer-recognizer-thm symbolp)
                                              (memname identp)
                                              (elemtype typep)
                                              (indextypes type-listp)
                                              (writer-acl2int symbolp)
                                              (checker-acl2int symbolp)
                                              (writers symbol-listp)
                                              (checkers symbol-listp)
                                              (writer-return-thm symbolp)
                                              (not-error-thm symbolp)
                                              (type-of-value-thm symbolp)
                                              (names-to-avoid symbol-listp)
                                              (wrld plist-worldp))
     :guard (and (type-integerp elemtype)
                 (type-integer-listp indextypes))
     :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
                  (member-write-thms "A @(tsee symbol-listp).")
                  (updated-names-to-avoid "A @(tsee symbol-listp)."))
     :mode :program
     :parents nil
     (b* (((when (endp indextypes)) (mv nil nil nil))
          (indextype (car indextypes))
          (writer (car writers))
          (checker (car checkers))
          (indexfixtype (integer-type-to-fixtype indextype))
          (elemfixtype (integer-type-to-fixtype elemtype))
          (indextypep (pack indexfixtype 'p))
          (elemtypep (pack elemfixtype 'p))
          (indextype-integer-value (pack indexfixtype '-integer-value))
          (array-writer (pack elemfixtype '-array-write-alt-def))
          (array-checker (pack elemfixtype '-array-index-okp))
          (not-error-array-thm (pack 'not-errorp-when- elemfixtype '-arrayp))
          (kind-array-thm (pack 'value-kind-when- elemfixtype '-arrayp))
          (valuep-when-indextype (pack 'valuep-when- indextypep))
          (valuep-when-elemtypep (pack 'valuep-when- elemtypep))
          (indextype->get (pack indexfixtype '->get))
          (type-thm (pack indexfixtype '->get$inline))
          (thm-name (pack 'exec-member-write-when-
                          recognizer
                          '-and-
                          (ident->name memname)
                          '-
                          indexfixtype))
          (arrayp-of-arrary-write
           (pack elemfixtype '-arrayp-of- elemfixtype '-array-write))
          ((mv thm-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (formula
           `(implies (and (syntaxp (quotep e))
                          (equal (expr-kind e) :binary)
                          (equal (binop-kind (expr-binary->op e)) :asg)
                          (equal left (expr-binary->arg1 e))
                          (equal right (expr-binary->arg2 e))
                          (equal (expr-kind left) :arrsub)
                          (equal array (expr-arrsub->arr left))
                          (equal index (expr-arrsub->sub left))
                          (equal (expr-kind array) :memberp)
                          (equal target (expr-memberp->target array))
                          (equal member (expr-memberp->name array))
                          (equal (expr-kind target) :ident)
                          (equal member (ident ,(ident->name memname)))
                          (not (zp limit))
                          (equal ptr (read-var (expr-ident->get target)
                                               compst))
                          (valuep ptr)
                          (value-case ptr :pointer)
                          (not (value-pointer-nullp ptr))
                          (equal (value-pointer->reftype ptr)
                                 (type-struct (ident ,(ident->name tag))))
                          (equal struct
                                 (read-object (value-pointer->designator ptr)
                                              compst))
                          (,recognizer struct)
                          (equal idx (exec-expr-pure index compst))
                          (,indextypep idx)
                          (,checker idx)
                          (equal val (exec-expr-pure right compst))
                          (,elemtypep val))
                     (equal (exec-expr-asg e compst fenv limit)
                            (write-object (value-pointer->designator ptr)
                                          (,writer idx val struct)
                                          compst))))
          (hints `(("Goal"
                    :in-theory
                    '(exec-expr-asg
                      exec-integer
                      value-struct-read
                      value-struct-write
                      not-errorp-when-valuep-rewrite
                      value-integerp
                      value-unsigned-integerp-alt-def
                      value-signed-integerp-alt-def
                      value-fix-when-valuep
                      ifix
                      integer-range-p
                      (:e ident)
                      (:compound-recognizer consp-when-ucharp)
                      ,recognizer
                      ,fixer-recognizer-thm
                      ,not-error-thm
                      ,type-of-value-thm
                      ,kind-array-thm
                      ,indextype-integer-value
                      ,checker
                      ,checker-acl2int
                      ,writer
                      ,writer-acl2int
                      ,not-error-array-thm
                      ,array-writer
                      ,array-checker
                      ,valuep-when-elemtypep
                      ,valuep-when-indextype
                      ,@*integer-value-disjoint-rules*
                      (:t ,type-thm))
                    :use
                    ((:instance
                      ,writer-return-thm
                      (index
                       (,indextype->get
                        (exec-expr-pure (expr-arrsub->sub (expr-binary->arg1 e))
                                        compst)))
                      (val
                       (exec-expr-pure (expr-binary->arg2 e) compst))
                      (struct
                       (read-object
                        (value-pointer->designator
                         (read-var
                          (expr-ident->get
                           (expr-memberp->target
                            (expr-arrsub->arr (expr-binary->arg1 e))))
                          compst))
                        compst)))
                     (:instance
                      ,arrayp-of-arrary-write
                      (array
                       (value-struct-read-aux
                        (ident ,(ident->name memname))
                        (value-struct->members
                         (read-object
                          (value-pointer->designator
                           (read-var
                            (expr-ident->get
                             (expr-memberp->target
                              (expr-arrsub->arr (expr-binary->arg1 e))))
                            compst))
                          compst))))
                      (index
                       (,indextype->get
                        (exec-expr-pure
                         (expr-arrsub->sub (expr-binary->arg1 e))
                         compst)))
                      (element
                       (exec-expr-pure (expr-binary->arg2 e) compst)))))))
          ((mv event &) (evmac-generate-defthm thm-name
                                               :formula formula
                                               :hints hints
                                               :enable nil))
          ((mv events thm-names names-to-avoid)
           (atc-gen-tag-member-write-thms-aux tag
                                              recognizer
                                              fixer-recognizer-thm
                                              memname
                                              elemtype
                                              (cdr indextypes)
                                              writer-acl2int
                                              checker-acl2int
                                              (cdr writers)
                                              (cdr checkers)
                                              writer-return-thm
                                              not-error-thm
                                              type-of-value-thm
                                              names-to-avoid
                                              wrld)))
       (mv (cons event events)
           (cons thm-name thm-names)
           names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-write-all-thms
  ((tag identp)
   (recognizer symbolp)
   (fixer-recognizer-thm symbolp)
   (not-error-thm symbolp)
   (type-of-value-thm symbolp)
   (meminfos defstruct-member-info-listp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (member-write-thms "A @(tsee symbol-listp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorems to rewrite @(tsee exec-expr-asg)
          with a @(':memberp') left expression
          to a structure writer,
          for all the members of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on @('writers') and @('writer-return-thms')
     to be in the same order as @('members')."))
  (b* (((when (endp meminfos)) (mv nil nil names-to-avoid))
       ((mv events thms names-to-avoid)
        (atc-gen-tag-member-write-thms tag
                                       recognizer
                                       fixer-recognizer-thm
                                       not-error-thm
                                       type-of-value-thm
                                       (car meminfos)
                                       names-to-avoid
                                       wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-write-all-thms tag
                                           recognizer
                                           fixer-recognizer-thm
                                           not-error-thm
                                           type-of-value-thm
                                           (cdr meminfos)
                                           names-to-avoid
                                           wrld)))
    (mv (append events more-events)
        (append thms more-thms)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-struct-declon-list ((meminfos member-type-listp))
  :returns (declons struct-declon-listp)
  :short "Generate a list of C structure declarations
          from a list of member types."
  (b* (((when (endp meminfos)) nil)
       (meminfo (car meminfos))
       ((member-type meminfo) meminfo)
       ((mv tyspec declor) (ident+type-to-tyspec+declor meminfo.name
                                                        meminfo.type))
       (declon (make-struct-declon :tyspec tyspec :declor declor))
       (declons (atc-gen-struct-declon-list (cdr meminfos))))
    (cons declon declons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-declon ((tag symbolp)
                            (prec-tags atc-string-taginfo-alistp)
                            (proofs booleanp)
                            (names-to-avoid symbol-listp)
                            (ctx ctxp)
                            state)
  :returns (mv erp
               (val "A @('(tuple (declon tag-declonp)
                                 (local-events pseudo-event-form-listp)
                                 (updated-prec-tags atc-string-taginfo-alistp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C structure type declaration,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the tag is not already in the table of preceding tags.
     We extend the table with the information for this tag,
     retrieved from the @(tsee defstruct) table in the ACL2 world")
   (xdoc::p
    "This has no accompanying generated theorems."))
  (b* ((irr (list (irr-tag-declon) nil nil nil))
       (tag (symbol-name tag))
       ((when (consp (assoc-equal tag prec-tags)))
        (raise "Internal error: tag ~x0 already encountered." tag)
        (acl2::value irr))
       (info (defstruct-table-lookup tag (w state)))
       ((unless info)
        (er-soft+ ctx t irr
                  "There is no DEFSTRUCT associated to the tag ~x0."
                  tag))
       (meminfos (defstruct-info->members info))
       (memtypes (defstruct-member-info-list->memtype-list meminfos))
       (tag-ident (defstruct-info->tag info))
       (recognizer (defstruct-info->recognizer info))
       (fixer-recognizer-thm (defstruct-info->fixer-recognizer-thm info))
       (not-error-thm (defstruct-info->not-error-thm info))
       (type-of-value-thm (defstruct-info->type-of-value-thm info))
       (struct-declons (atc-gen-struct-declon-list memtypes))
       ((mv read-thm-events read-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-read-all-thms tag-ident
                                              recognizer
                                              fixer-recognizer-thm
                                              not-error-thm
                                              meminfos
                                              names-to-avoid
                                              (w state))
          (mv nil nil names-to-avoid)))
       ((mv write-thm-events write-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-write-all-thms tag-ident
                                               recognizer
                                               fixer-recognizer-thm
                                               not-error-thm
                                               type-of-value-thm
                                               meminfos
                                               names-to-avoid
                                               (w state))
          (mv nil nil names-to-avoid)))
       (thm-events (append read-thm-events write-thm-events))
       (info (make-atc-tag-info :defstruct info
                                :member-read-thms read-thm-names
                                :member-write-thms write-thm-names))
       (prec-tags (acons tag info prec-tags)))
    (acl2::value
     (list (make-tag-declon-struct :tag tag-ident
                                   :members struct-declons)
           thm-events
           prec-tags
           names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-declon-list ((targets symbol-listp)
                                 (prec-fns atc-symbol-fninfo-alistp)
                                 (prec-tags atc-string-taginfo-alistp)
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
  :short "Generate a list of C external declarations from the targets,
          including generating C loops from recursive ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After we process the first function @('fn') in @('fns'),
     we use the extended @('prec-fns') for the subsequent functions.")
   (xdoc::p
    "We treat @(tsee defstruct) tags differently.
     We treat recursive and non-recursive functions differently."))
  (b* (((when (endp targets)) (acl2::value (list nil nil nil names-to-avoid)))
       (target (car targets))
       ((unless (function-symbolp target (w state)))
        (b* (((mv erp
                  (list tag-declon tag-thms prec-tags names-to-avoid)
                  state)
              (atc-gen-tag-declon target prec-tags proofs names-to-avoid ctx state))
             ((when erp) (mv erp (list nil nil nil names-to-avoid) state))
             (ext (ext-declon-tag-declon tag-declon))
             ((er (list exts local-events exported-events names-to-avoid))
              (atc-gen-ext-declon-list (cdr targets) prec-fns prec-tags proofs
                                       prog-const init-fun-env-thm fn-thms
                                       fn-appconds appcond-thms
                                       print names-to-avoid ctx state)))
          (acl2::value (list (cons ext exts)
                             (append tag-thms local-events)
                             exported-events
                             names-to-avoid))))
       (fn target)
       ((er (list exts local-events exported-events prec-fns names-to-avoid))
        (if (irecursivep+ fn (w state))
            (b* (((mv erp
                      (list local-events
                            exported-events
                            prec-fns
                            names-to-avoid)
                      state)
                  (atc-gen-loop fn prec-fns prec-tags proofs prog-const
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
                     fundef local-events exported-events prec-fns names-to-avoid)
                    state)
                (atc-gen-fundef fn prec-fns prec-tags proofs
                                prog-const init-fun-env-thm fn-thms
                                print names-to-avoid ctx state))
               ((when erp) (mv erp (list nil nil nil nil) state))
               (ext (ext-declon-fundef fundef)))
            (acl2::value (list (list ext)
                               local-events
                               exported-events
                               prec-fns
                               names-to-avoid)))))
       ((er
         (list more-exts more-local-events more-exported-events names-to-avoid))
        (atc-gen-ext-declon-list (cdr targets) prec-fns prec-tags proofs
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

(define atc-gen-transunit ((targets symbol-listp)
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
                  (atc-gen-appconds targets (w state)))
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
        (atc-gen-ext-declon-list targets nil nil proofs
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

(define atc-gen-file ((tunit transunitp)
                      (output-file stringp)
                      (pretty-printing pprint-options-p)
                      state)
  :returns (mv erp val state)
  :mode :program
  :short "Pretty-print the generated C code (i.e. translation unit)
          to the output file."
  (b* ((lines (pprint-transunit tunit pretty-printing)))
    (pprinted-lines-to-file lines output-file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file-event ((tunit transunitp)
                            (output-file stringp)
                            (pretty-printing pprint-options-p)
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
          (b* (((er &) (atc-gen-file ',tunit
                                     ,output-file
                                     ',pretty-printing
                                     state)))
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

(define atc-gen-everything ((targets symbol-listp)
                            (output-file stringp)
                            (pretty-printing pprint-options-p)
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
        (atc-gen-transunit targets proofs prog-const wf-thm fn-thms
                           print names-to-avoid ctx state))
       ((er file-gen-event) (atc-gen-file-event tunit
                                                output-file
                                                pretty-printing
                                                print
                                                state))
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
