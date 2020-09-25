; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defequal

  :parents (soft-macros)

  :short "Introduce an equality between functions."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "In a first-order language like the one of ACL2,
      a second-order equality (i.e. an equality between two functions)
      cannot be expressed directly as a second-order assertion of the form")
    (xdoc::codeblock
     "(equal f g)")
    (xdoc::p
     "but it can be expressed as a first-order assertion of the form")
    (xdoc::codeblock
     "(forall (x1 ... xn) (equal (f x1 ... xn) (g x1 ... xn)))")

    (xdoc::p
     "This macro generates such expression of equality,
      as a @(tsee defun-sk2),
      which already includes a rewrite rule from @('f') to @('g');
      the macro also generates an rewrite rule from @('g') to @('f').
      It also generates a theory invariant
      preventing both rewrite rules from being simultaneously enabled.")

    (xdoc::p
     "Thus, this macro automates the boilerplate of function equalities,
      and provides some support for reasoning about them.
      This macro may be extended with additional reasoning support."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(defequal name"
     "          :left ...                  ; no default"
     "          :right ...                 ; no default"
     "          :vars ...                  ; default :auto"
     "          :enable ...                ; default nil"
     "          :verify-guards ...         ; default t"
     "          :left-to-right-name ...    ; default :auto"
     "          :left-to-right-enable ...  ; default nil"
     "          :right-to-left-name ...    ; default :auto"
     "          :right-to-left-enable ...  ; default nil"
     "          :print ...                 ; default :result"
     "          :show-only ...             ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Specifies the name of the generated function.")
     (xdoc::p
      "It must be a symbol.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('name') be the name of this function."))

    (xdoc::desc
     (list
      "@(':left') &mdash; no default"
      "@(':right') &mdash; no default")
     (xdoc::p
      "Specify the functions to use as
       the left-hand and right-hand sides of the equality.")
     (xdoc::p
      "Each must be an existing function symbol.
       It may be a SOFT function variable,
       a SOFT second-order function,
       a regular first-order function,
       etc.")
     (xdoc::p
      "The two functions must have the same arity,
       which must not be 0.")
     (xdoc::p
      "At least one of the two functions must
       be a function variable or a second-order function.")
     (xdoc::p
      "If the @(':verify-guards') input (see below) is @('t'),
       the two functions must have guard @('t') and be guard-verified.
       Support for more general guards may be added in the future.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('left') and @('right') be the names of these functions,
       and let @('n') be their arity."))

    (xdoc::desc
     "@(':vars') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the variables to use in the quantification.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "A list of distinct symbols that are legal variables.
        Its length must be @('n').")
      (xdoc::li
       "@(':auto'), to use the list of symbols @('(x1 ... xn)'),
        all in the same package as @('name')."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('x1'), ..., @('xn') be these variables."))

    (xdoc::desc
     "@(':enable') &mdash; default @('nil')."
     (xdoc::p
      "Specifies whether @('name') should be enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable it.")
      (xdoc::li
       "@('nil'), to disable it.")))

    (xdoc::desc
     "@(':verify-guards') &mdash; default @('t')."
     (xdoc::p
      "Specifies whether @('name') should be guard-verified.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to guard-verify it.")
      (xdoc::li
       "@('nil'), to not guard-verify it."))
     (xdoc::p
      "Unless both @('left') and @('right') have guard @('t'),
       this should be set to @('nil')."))

    (xdoc::desc
     "@(':left-to-right-name') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the name of the theorem
       that rewrites @('left') to @('right').")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the name obtained by concatenating
        the name of @('left'), `@('-to-')', and the name of @('right'),
        in the same package as @('name').")
      (xdoc::li
       "Any other symbol, to use as the name of the theorem."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('left-to-right') be the name of this theorem."))

    (xdoc::desc
     "@(':left-to-right-enable') &mdash; default @('nil')."
     (xdoc::p
      "Specifies whether @('left-to-right') should be enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable it.")
      (xdoc::li
       "@('nil'), to disable it."))
     (xdoc::p
      "If this is @('t'), @(':right-to-left-enable') must be @('nil')."))

    (xdoc::desc
     "@(':right-to-left-name') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the name of the theorem
       that rewrites @('left') to @('right').")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the name obtained by concatenating
        the name of @('left'), `@('-to-')', and the name of @('right'),
        in the same package as @('name').")
      (xdoc::li
       "Any other symbol, to use as the name of the theorem."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('right-to-left') be the name of this theorem."))

    (xdoc::desc
     "@(':right-to-left-enable') &mdash; default @('nil')."
     (xdoc::p
      "Specifies whether @('right-to-left') should be enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable it.")
      (xdoc::li
       "@('nil'), to disable it."))
     (xdoc::p
      "If this is @('t'), @(':left-to-right-enable') must be @('nil')."))

    (xdoc::evmac-input-print defequal)

    (xdoc::evmac-input-show-only defequal))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Function that expresses the equality of @('left') and @('right'):")
     (xdoc::codeblock
      "(defun-sk2 name ()"
      "  (forall (x1 ... xn)"
      "          (equal (left x1 ... xn)"
      "                 (right x1 ... xn)))"
      "  :rewrite :direct"
      "  :thm-name left-to-right)")
     (xdoc::p
      "Note the generation of @('left-to-right') as a direct rewrite rule.
       See next item."))

    (xdoc::desc
     "@('left-to-right')"
     (xdoc::p
      "Theorem that rewrites @('left') to @('right'):")
     (xdoc::codeblock
      "(defthm left-to-right"
      "  (implies (name)"
      "           (equal (left x1 ... xn)"
      "                  (right x1 ... xn))))")
     (xdoc::p
      "This is generated by the @(tsee defun-sk2).
       See previous item."))

    (xdoc::desc
     "@('right-to-left')"
     (xdoc::p
      "Theorem that rewrites @('right') to @('left'):")
     (xdoc::codeblock
      "(defthm right-to-left"
      "  (implies (name)"
      "           (equal (right x1 ... xn)"
      "                  (left x1 ... xn))))")
     (xdoc::p
      "This is generated by the @(tsee defun-sk2).
       See previous item.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy defequal)))
