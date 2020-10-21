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

; (depends-on "design-notes/schemalg.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *schemalg-design-notes*
  (xdoc::&& "@('schemalg') "
            (xdoc::ahref "res/kestrel-apt-design-notes/schemalg.pdf"
                         "design notes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc schemalg

  :parents (apt)

  :short "APT schematic algorithm transformation:
          refine a specification by constraining a function
          to have a certain algorithmic form."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This transformation operates on a specification
      expressed as a second-order predicate
      that constrains a function to be synthesized,
      according to the shallow pop-refinement approach
      described in "
     (xdoc::ahref "http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3"
                  "the ACL2-2015 paper on SOFT")
     ". Currently, the second-order predicate must be expressed in "
     (xdoc::seetopic "soft::soft" "SOFT")
     ". In the future, this transformation may be extended
      to operate also on second-order predicates
      expressed via the built-in @(tsee apply$).")

    (xdoc::p
     "This transformation generates a refined specification
      that constrains the specification's function variable
      to be equal to a specified second-order function
      that captures an algorithmic structure.
      This introduces additional function variables,
      the ones that the second-order function depends on.
      The specified second-order function is accompanied by a theorem
      asserting the correctness of the algorithm
      given assumptions on these function variables.
      The transformation generates additional specifications
      corresponding to these assumptions.
      This way, once solutions for these specifications are synthesized,
      they can be composed into a solution for the original specification.")

    (xdoc::p
     "This transformation supports a number of algorithm schemas,
      each of which is described by
      the second-order function that defines it,
      the second-order theorem that states its correctness,
      and the forms of specifications that the schema applies to.
      This manual page provides the general reference for the transformation;
      there are separate manual pages that describe the specifics
      of the supported algorithm schemas.
      Support for additional schemas may be added in the future.")

    (xdoc::p
     "The " *schemalg-design-notes* ", which use "
     (xdoc::ahref "res/kestrel-design-notes/notation.pdf" "this notation")
     ", provide the mathematical concepts and template proofs
      upon which this transformation is based
      along with all the supported algorithm schemas.
      These design notes should be read alongside this reference documentation,
      which refers to them in some places.
      These design notes also refer to the "
     (xdoc::ahref "res/kestrel-apt-design-notes/specs-refs.pdf"
                  "`Specifications and Refinements' design notes")
     ", which therefore should be also read as needed."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(schemalg old"
     "          :schema             ; no default"
     "          :...                ; schema-specific defaults"
     "          :fvar-...-name      ; default :auto"
     "          :algo-name          ; default :auto"
     "          :algo-enable        ; default nil"
     "          :spec-...-name      ; default :auto"
     "          :spec-...-enable    ; default nil"
     "          :equal-algo-name    ; default :auto"
     "          :equal-algo-enable  ; default nil"
     "          :new-name           ; default :auto"
     "          :new-enable         ; default :auto"
     "          :old-if-new-name    ; default from table"
     "          :old-if-new-enable  ; default from table"
     "          :verify-guards      ; default :auto"
     "          :print              ; default :result"
     "          :show-only          ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must be a SOFT function that has no parameters
       and that depends on one function variable.
       Let this function variable be @('?f').")
     (xdoc::p
      "If the @(':verify-guards')input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "Additional requirements on the body of @('old') are stated
       in the documentation page for the chosen algorithm schema.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('old') is denoted by @($S$),
       @('?f') is denoted by @($f$), and
       the body of @('old') is denoted by @($\\Phi[f]$).
       Since currently SOFT function variables always return single values,
       it is always the case that @($m=1$), in the codomain of @($f$)."))

    (xdoc::desc
     "@(':schema') &mdash; no default"
     (xdoc::p
      "Indicates the algorithm schema to use.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li "@(':divconq-list-0-1')")
      (xdoc::li "@(':divconq-list-0-1-2')")
      (xdoc::li "@(':divconq-oset-0-1')"))
     (xdoc::p
      "(More may be added in the future.)")
     (xdoc::p
      "See the respective documentation pages for details."))

    (xdoc::desc
     "@(':...') &mdash; schema-specific defaults."
     (xdoc::p
      "For each choice of the @(':schema') input,
       this transformation may take additional inputs
       that are specific to the schema.
       These are described in the schema-specific documentation pages."))

    (xdoc::desc
     "@(':fvar-...-name') &mdash; default @(':auto')."
     (xdoc::p
      "For each choice of the @(':schema') input,
       there are one or more @(':fvar-...-name') inputs,
       which determine the names of the generate function variables
       that the algorithm schema's second-order function depends on.
       The number and names of these inputs are described in
       the schema-specific documentation page.")
     (xdoc::p
      "Each must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use a symbol constructed as
        described in the schema-specific documentation page.")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('?f1'), ..., @('?fp') be these names."))

    (xdoc::evmac-desc-input-name
     "algo"
     :desc "the generated second-order function for the algorithm schema"
     :auto-desc "the name of @('?f'),
                 without the @('?') if it starts with one,
                 followed by the name of @('?f1') between square brackets,
                 ...,
                 followed by the name of @('?fp') between square brackets,
                 with the resulting name in the same package as @('?f')"
     :name-rest "algo[?f1]...[?fp]")

    (xdoc::evmac-desc-input-enable-t/nil
     "algo"
     :desc "@('algo[?f1]...[?fp]')")

    (xdoc::desc
     "@(':spec-...-name') &mdash; default @(':auto')"
     (xdoc::p
      "For each choice of the @(':schema') input,
       there are one or more @(':spec-...-name') inputs,
       which determine the names of the generated
       second-order predicates for the sub-specifications
       derived from the schema.
       The number and names of these inputs are described in
       the schema-specific documentation page.")
     (xdoc::p
      "Each must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use a symbol constructed as
        described in the schema-specific documentation page.")
      (xdoc::li
       "Any other symbol, to use as the name."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('spec1[?f1]...[?fp]'), ..., @('specq[?f1]...[?fp]')
       be these names."))

    (xdoc::desc
     "@(':spec-...-enable') &mdash; default @('nil')"
     (xdoc::p
      "For each choice of the @(':schema') input,
       there are one or more @(':spec-...-enable') inputs,
       one for each @(':spec-...-name') inputs,
       which determine whether the corresponding predicate among
       @('spec1[?f1]...[?fp]'), ..., @('specq[?f1]...[?fp]')
       is enabled or not.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable the predicate.")
      (xdoc::li
       "@('nil'), to disable the predicate.")))

    (xdoc::evmac-desc-input-name
     "equal-algo"
     :desc "the generated second-order equality
            between @('?f') and @('algo[?f1]...[?fp]')"
     :auto-desc "the symbol @('equal'),
                 followed by
                 the name of @('?f') between square brackets,
                 followed by
                 the name of @('algo[?f1]...[?fp]') between square brackets,
                 with the resulting name in the same package as @('?f')"
     :name-rest "equal[?f][algo[?f1]...[?fp]]")

    (xdoc::evmac-desc-input-enable-t/nil
     "equal-algo"
     :desc "@('equal[?f][algo[?f1]...[?fp]]')
            (along its associated @(tsee defun-sk) rewrite rule)")

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-old-if-new-name)

    (xdoc::desc-apt-input-old-if-new-enable)

    (xdoc::desc-apt-input-verify-guards)

    (xdoc::evmac-input-print schemalg)

    (xdoc::evmac-input-show-only schemalg))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     (list "@('?f1')" "@('...')" "@('?fp')")
     (xdoc::p
      "Function variables that @('algo[?f1]...[?fp]') depends on:")
     (xdoc::codeblock
      "(soft::defunvar ?f1 (* ... *) => *)"
      "..."
      "(soft::defunvar ?fp (* ... *) => *)")
     (xdoc::p
      "whose exact number and arities are described
       in the schema-specific documentation page.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('?f1'), ..., @('?fp') are denoted by @($f_1,\\ldots,f_p$)."))

    (xdoc::desc
     "@('algo[?f1]...[?fp]')"
     (xdoc::p
      "Second-order function for the algorithm schema:")
     (xdoc::codeblock
      "(soft::defun2 algo[?f1]...[?fp] ...)")
     (xdoc::p
      "whose exact form is described
       in the schema-specific documentation page.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('algo[?f1]...[?fp]') is denoted by @($A(f_1,\\ldots,f_p)$),
       whose correctness theorem formula is denoted by
       @($$\\Psi_1[f_1,\\ldots,f_p]
           \\wedge
           \\cdots
           \\wedge
           \\Psi_q[f_1,\\ldots,f_p]
           \\Longrightarrow
           \\Psi[f_1,\\ldots,f_p]$$)."))

    (xdoc::desc
     (list "@('spec1[?f1]...[?fp]')" "@('...')" "@('specq[?f1]...[?fp]')")
     (xdoc::p
      "Second-order predicates for the sub-specifications:")
     (xdoc::codeblock
      "(soft::defun-sk2 spec1[?f1]...[?fp] ...)"
      "..."
      "(soft::defun-sk2 specq[?f1]...[?fp] ...)")
     (xdoc::p
      "whose exact form is described
       in the schema-specific documentation page.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       @('spec1[?f1]...[?fp]'), ..., @('specq[?f1]...[?fp]')
       are denoted by @($S_1,\\ldots,S_q)$),
       and their bodies are denoted by
       @($\\sigma(\\Psi_1[f_1,\\ldots,f_p]),
          \\ldots,
          \\sigma(\\Psi_q[f_1,\\ldots,f_p])$),
       where @($\sigma(\\Psi[f]) = \Phi[f]$)."))

    (xdoc::desc
     "@('equal[?f][algo[?f1]...[?fp]]')"
     (xdoc::p
      "Equality between @('?f') and @('algo[?f1]...[?fp]'):")
     (xdoc::codeblock
      "(soft::defequal equal[?f][algo[?f1]...[?fp]]"
      "  :left ?f"
      "  :right algo[?f1]...[?fp]"
      "  :vars ...)")
     (xdoc::p
      "whose specific @(':vars') variables are described
       in the schema-specific documentation page.")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
       this equality is denoted by @($f = A(f_1,\\ldots,f_p)$)."))

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Specification strengthened by choosing the algorithm schema:")
     (xdoc::codeblock
      "(soft::defun2 new ()"
      "  (and (equal[?f][algo[?f1]...[?fp]])"
      "       (spec1[?f1]...[?fp])"
      "       ..."
      "       (specq[?f1]...[?fp])))")
     (xdoc::p
      "In the " *schemalg-design-notes* ",
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
      "In the " *schemalg-design-notes* ",
       @('old-if-new') is denoted by @($SS'$).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy schemalg)))
