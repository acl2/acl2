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
(include-book "casesplit")

; (depends-on "design-notes/casesplit.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *casesplit-design-notes*
  (xdoc::ahref "res/kestrel-apt-design-notes/casesplit.pdf" "design notes"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc casesplit

  :parents (apt)

  :short "APT case splitting transformation:
          rephrase a function definition by cases."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Given a function,
      and some theorems asserting its equality to other functions
      under different conditions,
      this transformation generates an equivalent function
      defined to be equal to those other functions
      under suitable conditions.")

    (xdoc::p
     "This transformation can be used to bring together
      different refinements of the original function
      made under the different conditions,
      each such refinement being possibly initiated by
      a use of @(tsee restrict) with the corresponding condition.")

    (xdoc::p
     "These " *casesplit-design-notes* ", which use "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
     ", provide the mathematical concepts and template proofs
      upon which this transformation is based.
      These notes should be read alongside this reference documentation,
      which refers to them in some places."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto casesplit)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must be in logic mode,
       return a non-" (xdoc::seetopic "mv" "multiple") " value, and
       have no input or output " (xdoc::seetopic "acl2::stobj" "stobjs") "."
      " If the @(':verify-guards') input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "Let @('x1'), ..., @('xn') be the formal arguments of @('old')")
     (xdoc::p
      "Let @('old-guard<x1,...,xn>') be the guard term of @('old').")
     (xdoc::p
      "In the " *casesplit-design-notes* ",
       @('old') is denoted by @($f$)."))

    (xdoc::desc
     "@('conditions')"
     (xdoc::p
      "Denotes the conditions that define the cases
       in which the definition of the new function is split.")
     (xdoc::p
      "It must be a non-empty true list @('(cond1 ... condp)') of terms
       that include no free variables other than @('x1'), ..., @('xn'),
       that only call logic-mode functions,
       that return non-" (xdoc::seetopic "mv" "multiple") " values,
       and that have no output " (xdoc::seetopic "acl2::stobj" "stobjs") "."
      " If the generated function is guard-verified
       (which is determined by the @(':verify-guards') input; see below),
       then the terms must only call guard-verified functions,
       except possibly in the @(':logic') subterms of @(tsee mbe)s
       and via @(tsee ec-call).
       The terms must not include any calls to @('old').")
     (xdoc::p
      "In order to highlight the dependence on @('x1'), ..., @('xn'),
       in the rest of this documentation page,
       @('condk<x1,...,xn>') may be used for @('condk').")
     (xdoc::p
      "In the " *casesplit-design-notes* ",
       @('condk') is denoted by @($c_k$), for @($1 \\leq k \\leq p$)."))

    (xdoc::desc
     "@('theorems')"
     (xdoc::p
      "Denotes the theorems that assert
       the equality of @('old') to other functions
       under certain conditions.")
     (xdoc::p
      "It must be a non-empty true list of symbols @('(thm1 ... thmp thm0)')
       that name existing theorems, each of the form")
     (xdoc::codeblock
      "(defthm thmk"
      "  (implies hypk<x1,...,xn>"
      "           (equal (old x1 ... xn)"
      "                  newk<x1,...,xn>)))")
     (xdoc::p
      "where @('hypk') and @('newk') are terms
       that depend on (some of) @('x1'), ..., @('xn')
       (so that the theorem includes
       no free variables other than @('x1'), ..., @('xn')).
       As a special case, the theorem may have no hypothesis,
       which is equivalent to @('hyp<x1,...,xn>') being @('t').
       The rule classes of the theorem are irrelevant, as is its enablement.")
     (xdoc::p
      "The fact that @('thm0') comes after @('thm1'), ..., @('thmp')
       is intentional, since each @('thmk') corresponds to @('condk')
       as explicated below.")
     (xdoc::p
      "In the " *casesplit-design-notes* ",
       @('thmk'), @('hypk') and  @('newk')
       are denoted by @($\\mathit{ff}'_k$), @($h_k$), and @($f_k$),
       for @($0 \\leq k \\leq p$)."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-thm-name :never)

    (xdoc::desc-apt-input-thm-enable :never)

    (xdoc::desc-apt-input-verify-guards :never)

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print casesplit)

    (xdoc::evmac-input-show-only casesplit))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    casesplit

    (xdoc::desc
     (list
      "@(':thm1-hyp')"
      "..."
      "@(':thmp-hyp')")
     (xdoc::p
      "@('condk'), along with the negation of the preceding conditions,
       establishes the hypothesis of @('thmk'):")
     (xdoc::codeblock
      "(implies (and (not cond1<x1,...,xn>)"
      "              ..."
      "              (not condk-1<x1,...,xn>)"
      "              condk<x1,...,xn>)"
      "         hypk<x1,...,xn>)")
     (xdoc::p
      "There are @('p') applicability conditions of this form.")
     (xdoc::p
      "Each of these corresponds to a @($H_k$)
       in the " *casesplit-design-notes* ",
       for @($1 \\leq k \\leq p$)."))

    (xdoc::desc
     "@(':thm0-hyp')"
     (xdoc::p
      "The negation of all the conditions
       establishes the hypothesis of @('thm0'):")
     (xdoc::codeblock
      "(implies (and (not cond1<x1,...,xn>)"
      "              ..."
      "              (not condk<x1,...,xn>))"
      "         hyp0<x1,...,xn>)")
     (xdoc::p
      "This corresponds to @($H_0$)
       in the " *casesplit-design-notes* "."))

    (xdoc::desc
     (list
      "@('cond1-guard')"
      "..."
      "@('condp-guard')")
     (xdoc::p
      "Each @('condk') is well-defined (according to its guards)
       under the negation of the preceding conditions:")
     (xdoc::codeblock
      "(implies (and "
      "              (not cond1<x1,...,xn>)"
      "              ..."
      "              (not condk-1<x1,...,xn>))"
      "         condk-guard<x1,...,xn>)")
     (xdoc::p
      "where @('condk-guard') consists of
       the guard obligations of @('condk').")
     (xdoc::p
      "There are @('p') applicability conditions of this form.")
     (xdoc::p
      "Each of these corresponds to a @($\\mathit{GC}_k$)
       in the " *casesplit-design-notes* ",
       for @($1 \\leq k \\leq p$).")
     (xdoc::p
      "These applicability conditions are present if and only if
       the generated function is guard-verified
       (which is determined by the @(':verify-guards') input; see above)."))

    (xdoc::desc
     (list
      "@('new1-guard')"
      "..."
      "@('newp-guard')")
     (xdoc::p
      "Each @('newk') is well-defined (according to its guards)
       under @('condk') and the negation of the preceding conditions:")
     (xdoc::codeblock
      "(implies (and (not cond1<x1,...,xn>)"
      "              ..."
      "              (not condk-1<x1,...,xn>)"
      "              condk<x1,...,xn>)"
      "         newk-guard<x1,...,xn>)")
     (xdoc::p
      "where @('newk-guard') consists of
       the guard obligations of @('newk').")
     (xdoc::p
      "There are @('p') applicability conditions of this form.")
     (xdoc::p
      "Each of these corresponds to a @($\\mathit{Gf}_k$)
       in the " *casesplit-design-notes* ",
       for @($1 \\leq k \\leq p$).")
     (xdoc::p
      "These applicability conditions are present if and only if
       the generated function is guard-verified
       (which is determined by the @(':verify-guards') input; see above)."))

    (xdoc::desc
     "@('new0-guard')"
     (xdoc::p
      "@('new0') is well-defined (according to its guards)
       under the negation of all the conditions:")
     (xdoc::codeblock
      "(implies (and (not cond1<x1,...,xn>)"
      "              ..."
      "              (not condk<x1,...,xn>))"
      "         new0-guard<x1,...,xn>)")
     (xdoc::p
      "where @('new0-guard') consists of
       the guard obligations of @('new0').")
     (xdoc::p
      "This corresponds to @($\\mathit{Gf}_0$)
       in the " *casesplit-design-notes* ".")
     (xdoc::p
      "This applicability condition is present if and only if
       the generated function is guard-verified
       (which is determined by the @(':verify-guards') input; see above).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Equivalent definition of @('old') by cases:")
     (xdoc::codeblock
      "(defun new (x1 ... xn)"
      "  (cond (cond1<x1,...,xn> new1<x1,...,xn>)"
      "        ..."
      "        (condk<x1,...,xn> newk<x1,...,xn>)"
      "        (t new0<x1,...,xn>)))")
     (xdoc::p
      "This function is not recursive.")
     (xdoc::p
      "The guard is the same as @('old').")
     (xdoc::p
      "In the " *casesplit-design-notes* ",
       @('new') is denoted by @($f'$)."))

    (xdoc::desc
     "@('old-to-new')"
     (xdoc::p
      "Theorem that relates @('old') to @('new'):")
     (xdoc::codeblock
      "(defthm old-to-new"
      "  (equal (old x1 ... xn)"
      "         (new x1 ... xn)))")
     (xdoc::p
      "In the " *casesplit-design-notes* ",
       @('old-to-new') is denoted by @($\\mathit{ff}'$).")))))
