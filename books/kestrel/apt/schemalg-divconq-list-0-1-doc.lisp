; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "schemalg-doc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc schemalg-divconq-list-0-1

  :parents (schemalg)

  :short "APT schematic algorithm tranformation:
          specifics for the divide-and-conquer list 0-1 schema."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is a divide-and-conquer schema over (true or dotted) lists,
      with one base case for lists of length 0
      and one recursive case for list of length 1 or more."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(schemalg old"
     "          :schema :divconq-list-0-1"
     "          :list-input     ; default :auto"
     "          :cdr-output     ; default :auto"
     "          :fvar-0-name    ; default :auto"
     "          :fvar-1-name    ; default :auto"
     "          :spec-0-name    ; default :auto"
     "          :spec-0-enable  ; default nil"
     "          :spec-1-name    ; default :auto"
     "          :spec-1-enable  ; default nil"
     "          ... ; see :doc schemalg"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('old') &mdash; additional requirements"
     (xdoc::p
      "@('old') must have the form described in
       Section `Input/Output Relation with Selected Input and Modified Inputs'
       of @(see specification-forms).
       Let
       @('?f'),
       @('x'),
       @('x1'), ..., @('xn'),
       @('a1<x1,...,xn>'), ..., @('am<x1,...,xn>'), and
       @('(lambda (x x1 ... xn y) iorel<x,x1,...,xn,y>)')
       be as described there."))

    (xdoc::desc
     "@(':list-input') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the argument of the call of @('?f')
       that is treated as the list on which @('algo[?f1]...[?fp]') operates.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to specify the only argument of the call of @('?f'),
        when the call has exactly one argument.
        It is an error for @(':list-input') to be @(':auto')
        when the call has more than one argument.")
      (xdoc::li
       "An argument of the call of @('?f') that is a symbol,
        to specify that argument."))
     (xdoc::p
      "This is indicated as @('x')
       in the description of the @('old') input above."))

    (xdoc::desc
     "@(':cdr-output') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the name of the variable to use for
       the solution (i.e. output) for the @(tsee cdr) of the list,
       in the generated sub-specification for the recursive case.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('cdr-output'),
        in the same package as @('old').")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('y') be this name.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('y') is denoted by @($y$)."))

    (xdoc::desc
     "@(':fvar-0-name') &mdash; additional information"
     (xdoc::p
      "If this input is @(':auto'), we use
       the name of @('?f'),
       followed by `@('-0')',
       with the resulting name in the same package as @('?f').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('?g') be the name determined by this input
       (whether it is @(':auto') or not)."))

    (xdoc::desc
     "@(':fvar-1-name') &mdash; additional information"
     (xdoc::p
      "If this input is @(':auto'), we use
       the name of @('?f'),
       followed by `@('-1')',
       with the resulting name in the same package as @('?f').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('?h') be the name determined by this input
       (whether it is @(':auto') or not)."))

    (xdoc::desc
     "@(':spec-0-name') &mdash; additional information"
     (xdoc::p
      "If this input is @(':auto'), we use
       the name of @('old'),
       followed by `@('-0')',
       followed by @('?g') between square brackets,
       with the resulting name in the same package as @('old').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('old-0[?g]') be the name determined by this input
       (whether it is @(':auto') or not)."))

    (xdoc::desc
     "@(':spec-1-name') &mdash; additional information"
     (xdoc::p
      "If this input is @(':auto'), we use
       the name of @('old'),
       followed by `@('-1')',
       followed by @('?h') between square brackets,
       with the resulting name in the same package as @('old').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('old-1[?h]') be the name determined by this input
       (whether it is @(':auto') or not)."))

    (xdoc::p
     "See @(tsee schemalg) for the rest of the description of the inputs."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('?g')"
     (xdoc::p
      "Function variable used for lists of length 0:")
     (xdoc::codeblock
      "(soft::defunvar ?g (* * ... *) => *)")
     (xdoc::p
      "where the number of arguments is @('m+1'),
       i.e. the same as @('?f').")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('?g') is denoted by @($g$)."))

    (xdoc::desc
     "@('?h')"
     (xdoc::p
      "Function variable used for lists of length 1 or more:")
     (xdoc::codeblock
      "(soft::defunvar ?h (* * ... * *) => *)")
     (xdoc::p
      "where the number of arguments is @('m+2'),
       i.e. the same as @('?f') plus one.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('?h') is denoted by @($h$)."))

    (xdoc::desc
     "@('algo[?g][?h]')"
     (xdoc::p
      "Algorithm schema:")
     (xdoc::codeblock
      "(soft::defun2 algo[?g][?h] (x z1 ... zm)"
      "  (cond ((atom x) (?g x z1 ... zm))"
      "        (t (?h (car x)"
      "               z1"
      "               ..."
      "               zm"
      "               (algo[?g][?h] (cdr x) z1 ... zm)))))")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('algo[?g][?h]') is denoted by @($A(g,h)$)
       and @('z1'), ..., @('zm') are denoted by @($\\overline{z}$)."))

    (xdoc::desc
     "@('old-0[?g]')"
     (xdoc::p
      "Sub-specification for lists of length 0:")
     (xdoc::codeblock
      "(soft::defun-sk2 old-0[?g] ()"
      "  (forall (x x1 ... xn)"
      "          (impliez (atom x)"
      "                   iorel<x,x1,...,xn,"
      "                         (?g x a1<x1,...,xn> ... am<x1,...,xn>))))"))

    (xdoc::desc
     "@('old-1[?h]')"
     (xdoc::p
      "Sub-specification for lists of length 1 or more:")
     (xdoc::codeblock
      "(soft::defun-sk2 old-1[?h] ()"
      "  (forall (x x1 ... xn y)"
      "          (impliez (and (consp x)"
      "                        iorel<(cdr x),x1,...,xn,y>)"
      "                   iorel<x,x1,...,xn,"
      "                         (?h (car x)"
      "                             a1<x1,...,xn>"
      "                             ..."
      "                             am<x1,...,xn>"
      "                             y))))"))

    (xdoc::p
     "See @(tsee schemalg) for
      the rest of the description of the generated events."))))
