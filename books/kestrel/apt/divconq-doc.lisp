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
       that has no parameters,
       that depends on one function variable (call it @('?f')),
       and whose body has the form")
     (xdoc::codeblock
      "(forall (x x1 ... xn)"
      "        iorel<x,x1,...,xn,(?f x a1<x1,...,xn> ... am<x1,...,xn>)>)")
     (xdoc::p
      "where @('n') may be 0 and
       @('iorel<...>') is a term that depends on the quantified variables
       and that contains a single occurrence of
       a call of @('?f') of the form shown above,
       where @('m') may be 0 and
       each @('aj<x1,...,xn>') is a term that depends on @('x1'), ..., @('xn')
       (and must not depend on @('x')).
       The variable @('x') does not actually have to be
       the first quantified variable in the list after @('forall')
       and the first argument of the call of @('?f'):
       it may be anywhere in the list and in any argument position,
       as it is identified by the @(':list-input') input (see below);
       to ease exposition, in the rest of the documentation page
       we assume that it is the first one, as shown above.")
     (xdoc::p
      "If the @(':verify-guards')input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       in Section `More General List Fold Schema and Its Application',
       @('old') is denoted by @($S$),
       @('?f') is denoted by @($f$),
       @('x') is denoted by @($x$),
       @('x1'), ..., @('xn') are denoted by @($\\overline{x}$),
       @('a1<x1,...,xn>'), ..., @('am<x1,...,xn>') are denoted
       by @($\\overline{\\alpha}(\\overline{x})$), and
       @('(lambda (x x1 ... xn y) iorel<x,x1,...,xn,y>)') is denoted
       by @($R$)."))

    (xdoc::desc
     "@(':schema') &mdash; no default"
     (xdoc::p
      "Indicates the divide-and-conquer schema to use.")
     (xdoc::p
      "Currenty, this must be @(':list-fold'):
       only the list fold schema is supported.
       Support for more schemas is planned.")
     (xdoc::p
      "In the " *divconq-design-notes* ", the schema is described
       in Section `More General List Fold Schema and Its Application'."))

    (xdoc::desc
     "@(':list-input') &mdash; default @(':auto')"
     (xdoc::p
      "Specifies the argument of the call of @('?f')
       that is treated as the list on which @('fold[?g][?h]') operates.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to specify the only argument of the call of @('?f'),
        when the call has exactly one argument.
        It is an error for @(':list-input') to be @(':auto')
        when the call has more than argument.")
      (xdoc::li
       "An argument of the call of @('?f') that is a symbol,
        to specify that argument."))
     (xdoc::p
      "This is indicated as @('x')
       in the description of the @('old') input above."))

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

    (xdoc::desc-apt-input-verify-guards)

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
      "where the number of arguments is @('m+1'),
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
      "where the number of arguments is @('m+2'),
       i.e. the same as @('?f') plus one.")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('?h') is denoted by @($h$)."))

    (xdoc::desc
     "@('fold[?g][?h]')"
     (xdoc::p
      "List fold function:")
     (xdoc::codeblock
      "(soft::defun2 fold[?g][?h] (x z1 ... zm)"
      "  (cond ((atom x) (?g x z1 ... zm))"
      "        (t (?h (car x)"
      "               z1"
      "               ..."
      "               zm"
      "               (fold[?g][?h] (cdr x) z1 ... zm)))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('fold[?g][?h]') is denoted by @($\\mathit{fold}(g,h)$)
       and @('z1'), ..., @('zm') are denoted by @($\\overline{z}$)."))

    (xdoc::desc
     "@('spec-atom[?g]')"
     (xdoc::p
      "Sub-specification for @('?g'):")
     (xdoc::codeblock
      "(soft::defun-sk2 spec-atom[?g] ()"
      "  (forall (x x1 ... xn)"
      "          (impliez (atom x)"
      "                   iorel<x,x1,...,xn,"
      "                         (?g x a1<x1,...,xn> ... am<x1,...,xn>))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('spec-atom[?g]') is denoted by @($S_\\mathrm{g}(g)$)."))

    (xdoc::desc
     "@('spec-cons[?h]')"
     (xdoc::p
      "Sub-specification for @('?h'):")
     (xdoc::codeblock
      "(soft::defun-sk2 spec-cons[?h] ()"
      "  (forall (x x1 ... xn y)"
      "          (impliez (and (consp x)"
      "                        iorel<(cdr x),x1,...,xn,y>)"
      "                   iorel<x,x1,...,xn,"
      "                         (?h (car x)"
      "                             a1<x1,...,xn>"
      "                             ..."
      "                             am<x1,...,xn>"
      "                             y))))")
     (xdoc::p
      "In the " *divconq-design-notes* ",
       @('spec-cons[?h]') is denoted by @($S_\\mathrm{h}(h)$)."))

    (xdoc::desc
     "@('equal[?f][fold[?g][?h]]')"
     (xdoc::p
      "Equality between @('?f') and @('fold[?g][?h]'):")
     (xdoc::codeblock
      "(soft::defun-sk2 equal[?f][fold[?g][?h]] ()"
      "  (forall (x z1 ... zm)"
      "          (equal (?f x z1 ... zm)"
      "                 (fold[?g][?h] x z1 ... zm))))")
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
