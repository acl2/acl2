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
  :short "Tables of C variables, and operations on them,
          used internally by ATC."
  :order-subtopics t
  :default-parent t)

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
     that variable is not already in scope (via @(tsee atc-check-var)).
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
