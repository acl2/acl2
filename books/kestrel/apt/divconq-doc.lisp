; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "utilities/xdoc-constructors")

; (depends-on "design-notes/divconq.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *divconq-design-notes*
  (xdoc::&& "@('divconq') "
            (xdoc::ahref "res/kestrel-apt-design-notes/divconq.pdf"
                         "design notes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc divconq

  :parents (apt)

  :short "APT divide-and-conquer transformation:
          solve a problem by
          decomposing it into sub-problems
          and composing the sub-solutions."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Divide-and-conquer is a well-known algorithmic approach,
      in which the problem to solve is decomposed into sub-problems
      that are recursively solved and whose solutions are composed
      to obtain a solution to the original problem.
      This recursive decomposition ends
      when non-decomposable sub-problems are reached
      that can be solved directly.
      For example, many sorting algorithms follow this approach.")

    (xdoc::p
     "Divide-and-conquer, like other algorithmic approaches,
      can be formalized via algorithm schemas
      that consist of higher-order functions and accompanying theorems.
      Given that ACL2 is first-order,
      these would have to be second-order functions and theorems, specifically.
      Even though ACL2 is first-order,
      it is possible to mimic enough ``second-orderness'' in ACL2
      to represent algorithm schemas like divide-and-conquer,
      and to apply them to specifications that are second-order predicates
      (i.e. first-order predicates
      that mimic second-order predicates to a sufficient extent).
      These specifications express constraints
      on the first-order functions of interest,
      and are linked by backward implications as the refinement relation.
      This is according to the `shallow pop-refinement' approach,
      described in "
     (xdoc::ahref "http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3"
                  "the ACL2-2015 paper on SOFT")
     ".")

    (xdoc::p
     "The " *divconq-design-notes* ", which use "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
     ", provide the mathematical concepts and template proofs
      upon which this transformation is based.
      These notes should be read alongside this reference documentation,
      which refers to them in some places.")

    (xdoc::p
     "This transformation currently uses "
     (xdoc::seetopic "soft::soft" "SOFT")
     " to mimic the needed second-order features.
      Future versions of this transformation may use
      the built-in @(tsee apply$)
      instead or in addition.")

    (xdoc::p
     "Currently this transformation is limited
      to one divide-and-conquer schema, namely fold on lists.
      Support for more divide-and-conquer schemas is planned."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(divconq old"
     "         :schema             ; no default"
     "         :list-input         ; default :auto"
     "         :fvar-atom-name     ; default :auto"
     "         :fvar-cons-name     ; default :auto"
     "         :fold-name          ; default :auto"
     "         :fold-enable        ; default nil"
     "         :spec-atom-name     ; default :auto"
     "         :spec-atom-enable   ; default nil"
     "         :spec-cons-name     ; default :auto"
     "         :spec-cons-enable   ; default nil"
     "         :equal-fold-name    ; default :auto"
     "         :equal-fold-enable  ; default nil"
     "         :cdr-output         ; default :auto"
     "         :new-name           ; default :auto"
     "         :new-enable         ; default :auto"
     "         :old-if-new-name    ; default from table"
     "         :old-if-new-enable  ; default from table"
     "         :verify-guards      ; default :auto"
     "         :print              ; default :result"
     "         :show-only          ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must be a SOFT quantifier function
       (see `Classification' section in @(tsee soft::defsoft))
       that depends on one function variable (call it @('?f')),
       that has no parameters,
       and whose body has the form")
     (xdoc::codeblock
      "(forall (x0 x1 ... xn) (iorel x0 x1 ... xn (?f x0 x1 ... xn)))")
     (xdoc::p
      "where @('iorel') is a function symbol
       and @('n') may be 0.
       If the @(':verify-guards') input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('old') is denoted by @($S$),
       @('?f') is denoted by @($f$),
       @('iorel') is denoted by @($R$), and
       @('x0'), ..., @('xn') are denoted by the single variable @($x$)
       (the generalization to multiple variables
       is straighforward in the design notes)."))

    (xdoc::desc
     "@(':schema') &mdash; no default"
     (xdoc::p
      "Indicates the divide-and-conquer schema to use.")
     (xdoc::p
      "Currenty, this must be @(':list-fold'):
       only the list fold schema is supported.
       Support for more schemas is planned."))

    (xdoc::desc
     "@(':list-input') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the input of @('?f') that is treated as
       the list on which @('fold[?g][?h]') operates.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to specify @('x0').")
      (xdoc::li
       "One of @('x0'), ..., @('xn'), to specify that variable."))
     (xdoc::p
      "(See the required form of @('old') above.)")
     (xdoc::p
      "In the rest of this documentation page, for ease of exposition,
       we assume that this is the variable @('x0').")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       this is the (only) variable @($x$).
       However, it is easy to see how the design notes
       can be generalized to multiple variables."))

    (xdoc::desc
     "@(':fvar-atom-name') &mdash; default @(':auto')"
     (xdoc::p
      "Determines the name of the generated function variable
       for the sub-function called for @(tsee atom) inputs.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use @('?f') followed by @('-atom').")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('?g') be this name."))

    (xdoc::desc
     "@(':fvar-cons-name') &mdash; default @(':auto')"
     (xdoc::p
      "Determines the name of the generated function variable
       for the sub-function called for @(tsee consp) inputs.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use @('?f') followed by @('-cons').")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('?h') be this name."))

    (xdoc::desc
     "@(':fold-name') &mdash; default @(':auto')"
     (xdoc::p
      "Determines the name of the generated
       list fold second-order function.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('fold')
        (in the same package as @('old')),
        followed by the name of @('?g') between square brackets,
        followed by the name of @('?h') between square brackets.")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('fold[?g][?h]') be this name."))

    (xdoc::desc
     "@(':fold-enable') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether @('fold[?g][?h]') is enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable it.")
      (xdoc::li
       "@('nil'), to disable it.")))

    (xdoc::desc
     "@(':spec-atom-name') &mdash; @(':auto')"
     (xdoc::p
      "Determines the name of the generated sub-specification
       second-order predicate for the function variable @('?g').")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('spec-atom')
        (in the same package as @('old')),
        followed by the name of @('?g') between square brackets.")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('spec-atom[?g]') be this name."))

    (xdoc::desc
     "@(':spec-atom-enable') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether @('spec-atom[?g]'),
       and its associated @(tsee defun-sk) rewrite rule,
       are enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable them.")
      (xdoc::li
       "@('nil'), to disable them.")))

    (xdoc::desc
     "@(':spec-cons-name') &mdash; @(':auto')"
     (xdoc::p
      "Determines the name of the generated sub-specification
       second-order predicate for the function variable @('?h').")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('spec-cons')
        (in the same package as @('old')),
        followed by the name of @('?h') between square brackets.")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('spec-cons[?h]') be this name."))

    (xdoc::desc
     "@(':spec-cons-enable') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether @('spec-cons[?h]'),
       and its associated @(tsee defun-sk) rewrite rule,
       are enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable them.")
      (xdoc::li
       "@('nil'), to disable them.")))

    (xdoc::desc
     "@(':equal-fold-name') &mdash; @(':auto')"
     (xdoc::p
      "Determines the name of the generated second-order equality
       between @('?f') and @('fold[?g][?h]').")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('equal')
        (in the same package as @('old')),
        followed by the name of @('?f') between square brackets,
        followed by the name of @('fold[?g][?h]') between square brackets.")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('equal[?f][fold[?g][?h]]') be this name."))

    (xdoc::desc
     "@(':equal-fold-enable') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether @('equal[?f][fold[?g][?h]]'),
       and its associated @(tsee defun-sk) rewrite rule,
       are enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable them.")
      (xdoc::li
       "@('nil'), to disable them.")))

    (xdoc::desc
     "@(':cdr-output') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the name of the variable to use for
       the solution (i.e. output) for the @(tsee cdr) of the input,
       in the generated sub-specification @('spec-cons[?h]').")
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
      "In the " *divconq-design-notes* ",
       @('y') is denoted by @($y$)."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-old-if-new-name)

    (xdoc::desc-apt-input-old-if-new-enable)

    (xdoc::desc
     "@(':verify-guards') &mdash; default @(':auto')"
     (xdoc::p
      "Determines whether the guards of the generated function(s)
       are to be verified or not.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to verify them.")
      (xdoc::li
       "@('nil'), to not verify them.")
      (xdoc::li
       "@(':auto'), to verify them if and only if
        the guards of @('old') are verified.")))

    (xdoc::evmac-input-print divconq)

    (xdoc::evmac-input-show-only divconq))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('?g')"
     (xdoc::p
      "Function variable to use for the sub-function
       that @('fold[?g][?h]') calls or the @(tsee atom) inputs:")
     (xdoc::codeblock
      "(soft::defunvar ?g (* * ... *) => *)")
     (xdoc::p
      "where the number of arguments is @('n+1'),
       i.e. the same as @('?f').")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('?g') is denoted by @($g$)."))

    (xdoc::desc
     "@('?h')"
     (xdoc::p
      "Function variable to use for the sub-function
       that @('fold[?g][?h]') calls or the @(tsee consp) inputs:")
     (xdoc::codeblock
      "(soft::defunvar ?h (* * ... * *) => *)")
     (xdoc::p
      "where the number of arguments is @('n+2'),
       i.e. the same as @('?f') plus one.")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('?h') is denoted by @($h$)."))

    (xdoc::desc
     "@('fold[?g][?h]')"
     (xdoc::p
      "List fold function:")
     (xdoc::codeblock
      "(soft::defun2 fold[?g][?h] (x0 x1 ... xn)"
      "  (cond ((atom x0) (?g x0 x1 ... xn))"
      "        (t (?h (car x0)"
      "               x1"
      "               ..."
      "               xn"
      "               (fold[?g][?h] (cdr x0) x1 ... xn)))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('fold[?g][?h]') is denoted by @($\\mathit{fold}(g,h)$)."))

    (xdoc::desc
     "@('spec-atom[?g]')"
     (xdoc::p
      "Sub-specification for @('?g'):")
     (xdoc::codeblock
      "(soft::defun-sk2 spec-atom[?g] ()"
      "  (forall (x0 x1 ... xn)"
      "          (impliez (atom x0)"
      "                   (iorel x0 x1 ... xn (?g x0 x1 ... xn)))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('spec-atom[?g]') is denoted by @($S_\\mathrm{g}(g)$)."))

    (xdoc::desc
     "@('spec-cons[?h]')"
     (xdoc::p
      "Sub-specification for @('?h'):")
     (xdoc::codeblock
      "(soft::defun-sk2 spec-cons[?h] ()"
      "  (forall (x0 x1 ... xn y)"
      "          (impliez (and (consp x0)"
      "                        (iorel (cdr x0) x1 ... xn y))"
      "                   (iorel x0 x1 ... xn (?h (car x0) x1 ... xn y)))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('spec-cons[?h]') is denoted by @($S_\\mathrm{h}(h)$)."))

    (xdoc::desc
     "@('equal[?f][fold[?g][?h]]')"
     (xdoc::p
      "Equality between @('?f') and @('fold[?g][?h]'):")
     (xdoc::codeblock
      "(soft::defun-sk2 equal[?f][fold[?g][?h]] ()"
      "  (forall (x0 x1 ... xn)"
      "          (equal (?f x0 x1 ... xn)"
      "                 (fold[?g][?h] x0 x1 ... xn))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       this equality is just denoted by @($f=\\mathit{fold}(g,h)$),
       but this must be expressed as a second-order @(tsee defun-sk) in ACL2."))

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Specification strengthened by choosing the list fold algorithm schema:")
     (xdoc::codeblock
      "(soft::defun2 new ()"
      "  (and (equal[?f][fold[?g][?h]])"
      "       (spec-atom[?g])"
      "       (spec-cons[?h])))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('new') is denoted by @($S'$)."))

    (xdoc::desc
     "@('old-if-new')"
     (xdoc::p
      "Theorem asserting that @('new') implies @('old')
       (i.e. a refinement relation):")
     (xdoc::codeblock
      "(defthm old-if-new"
      "  (implies (new)"
      "           (old))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('old-if-new') is denoted by @($SS'$).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy divconq)))
