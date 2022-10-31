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

(include-book "../language/types")

(local (include-book "std/alists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-variable-tables
  :parents (atc-event-and-code-generation)
  :short "Tables of ACL2 variables, and operations on these tables."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atc-var-info
  :short "Fixtype of information associatated to
          an ACL2 variable translated to a C variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each variable, we store its C type,
     and the name of a theorem about the variable.
     (We are not generating the theorem yet, but we will soon.)."))
  ((type type)
   (thm symbol))
  :pred atc-var-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist atc-var-info-list
  :short "Fixtype of lists of information associatated to
          an ACL2 variable translated to a C variable."
  :elt-type atc-var-info
  :true-listp t
  :elementp-of-nil nil
  :pred atc-var-info-listp)

;;;;;;;;;;

(std::defprojection atc-var-info-list->type-list ((x atc-var-info-listp))
  :returns (types type-listp)
  :short "Lift @(tsee atc-var-info->type) to lists."
  (atc-var-info->type x))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption atc-var-info-option
  atc-var-info
  :short "Fixtype of optional information associatated to
          an ACL2 variable translated to a C variable."
  :pred atc-var-info-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist atc-var-info-option-list
  :short "Fixtype of lists of optional information associatated to
          an ACL2 variable translated to a C variable."
  :elt-type atc-var-info-option
  :true-listp t
  :elementp-of-nil t
  :pred atc-var-info-option-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-symbol-varinfo-alist
  :short "Fixtype of alists from symbols to variable information."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to represent scopes in the symbol tables for variables.")
   (xdoc::p
    "They are also used to represent information about
     the formals of an ACL2 function.
     This is a slightly different use than in symbol tables."))
  :key-type symbol
  :val-type atc-var-info
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred atc-symbol-varinfo-alistp
  ///

  (defrule atc-var-infop-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-varinfo-alistp x)
                  (assoc-equal k x))
             (atc-var-infop (cdr (assoc-equal k x)))))

  (defruled symbol-listp-of-strip-cars-when-atc-symbol-varinfo-alistp
    (implies (atc-symbol-varinfo-alistp x)
             (symbol-listp (strip-cars x))))

  (defruled atc-var-info-listp-of-strip-cdrs-when-atc-symbol-varinfo-alistp
    (implies (atc-symbol-varinfo-alistp x)
             (atc-var-info-listp (strip-cdrs x)))
    :enable atc-symbol-varinfo-alistp)

  (defruled symbol-alistp-when-atc-symbol-varinfo-alistp
    (implies (atc-symbol-varinfo-alistp x)
             (symbol-alistp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atc-symbol-varinfo-alist-list
  :short "Fixtype of lists of alists from symbols to variable information."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent symbol tables for variables.
     The @(tsee car) is the innermost scope."))
  :elt-type atc-symbol-varinfo-alist
  :true-listp t
  :elementp-of-nil t
  :pred atc-symbol-varinfo-alist-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-var ((var symbolp) (inscope atc-symbol-varinfo-alist-listp))
  :returns (info? atc-var-info-optionp)
  :short "Obtain the information for a variable from the symbol table."
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
    (or (cdr (assoc-eq var (atc-symbol-varinfo-alist-fix (car inscope))))
        (atc-get-var var (cdr inscope)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-vars ((vars symbol-listp)
                      (inscope atc-symbol-varinfo-alist-listp))
  :returns (info?-list atc-var-info-option-listp)
  :short "Lift @(tsee atc-get-var) to lists."
  (cond ((endp vars) nil)
        (t (cons (atc-get-var (car vars) inscope)
                 (atc-get-vars (cdr vars) inscope)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-var-check-innermost ((var symbolp)
                                     (inscope atc-symbol-varinfo-alist-listp))
  :returns (mv (info? atc-var-info-optionp)
               (innermostp booleanp))
  :short "Obtain the information for a variable from the symbol table,
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
      (inscope atc-symbol-varinfo-alist-listp)
      (innermostp booleanp))
     :returns (mv (info? atc-var-info-optionp)
                  (innermostp booleanp :hyp (booleanp innermostp)))
     :parents nil
     (b* (((when (endp inscope)) (mv nil nil))
          (scope (atc-symbol-varinfo-alist-fix (car inscope)))
          (type? (cdr (assoc-eq var scope)))
          ((when type?) (mv type? innermostp)))
       (atc-get-var-check-innermost-aux var (cdr inscope) nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-vars-check-innermost ((vars symbol-listp)
                                      (inscope atc-symbol-varinfo-alist-listp))
  :returns (mv (info?-list atc-var-info-option-listp)
               (innermostp-list boolean-listp))
  :short "Lift @(tsee atc-get-var-check-innermost) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when we encounter an @(tsee mv-let) in code generation.
     We need to ensure that all the variables are in scope,
     and we need to know which ones are in the innermost scope.
     This function returns that information."))
  (b* (((when (endp vars)) (mv nil nil))
       ((mv info? innermostp)
        (atc-get-var-check-innermost (car vars) inscope))
       ((mv info?-list innermostp-list)
        (atc-get-vars-check-innermost (cdr vars) inscope)))
    (mv (cons info? info?-list)
        (cons innermostp innermostp-list)))
  ///

  (defret len-of-atc-get-vars-check-innermost.info?-list
    (equal (len info?-list)
           (len vars)))

  (defret len-of-atc-get-vars-check-innermost.innermostp-list
    (equal (len innermostp-list)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-add-var ((var symbolp)
                     (info atc-var-infop)
                     (inscope atc-symbol-varinfo-alist-listp))
  :returns (new-inscope atc-symbol-varinfo-alist-listp)
  :short "Add a variable with some information to the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is added to the innermost scope.
     The symbol table has always at least one scope.")
   (xdoc::p
    "This is always called after checking that
     that variable is not already in scope (via @(tsee atc-check-var)).
     So it unconditionally adds the variable without checking first."))
  (cons (acons (symbol-fix var)
               (atc-var-info-fix info)
               (atc-symbol-varinfo-alist-fix (car inscope)))
        (atc-symbol-varinfo-alist-list-fix (cdr inscope))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-var ((var symbolp) (inscope atc-symbol-varinfo-alist-listp))
  :returns (mv (info? atc-var-info-optionp)
               (innermostp booleanp)
               (errorp booleanp))
  :short "Check a variable against a symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is in the symbol table, we return its information,
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
                              (inscope atc-symbol-varinfo-alist-listp)
                              (innermostp booleanp))
     :returns (mv (info? atc-var-info-optionp)
                  (innermostp booleanp :hyp (booleanp innermostp))
                  (errorp booleanp))
     :parents nil
     (b* (((when (endp inscope)) (mv nil nil nil))
          (scope (car inscope))
          (info? (cdr (assoc-eq var (atc-symbol-varinfo-alist-fix scope))))
          ((when info?) (mv info? innermostp nil))
          ((when (member-equal (symbol-name var)
                               (symbol-name-lst (strip-cars scope))))
           (mv nil nil t)))
       (atc-check-var-aux var (cdr inscope) nil)))))
