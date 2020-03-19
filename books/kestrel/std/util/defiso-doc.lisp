; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defiso")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

; (depends-on "design-notes/defiso.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *defiso-design-notes*
  (xdoc::a :href "res/kestrel-std-util-design-notes/defiso.pdf" "design notes"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defiso

  :parents (std/util-extensions std/util)

  :short "Establish an isomorphic mapping between two domains."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Two domains (i.e. predicates) @($A$) and @($B$) are isomorphic iff
      there exist mutually inverse isomorphisms @($\\alpha$) and @($\\beta$)
      between the two domains.
      The domains and isomorphisms are illustrated in these "
     *defiso-design-notes*
     ", which use this "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "notation")
     ".")

    (xdoc::p
     "This macro attempts to verify that
      two specified domains are isomorphic,
      using two specified functions as the mutually inverse isomorphisms.
      The verification amounts to
      proving the applicability conditions below as theorems,
      from which additional theorems are automatically proved.")

    (xdoc::p
     "The domains, isomorphisms, and theorems
      are recorded in the ACL2 @(see world),
      under a specified name that can be referenced from other tools
      (e.g. " (xdoc::seetopic "apt::apt" "APT") " transformations).")

    (xdoc::p
     "The domains may have multiple arguments,
      and the isomorphisms may have multiple arguments and results.
      In this case, the domains are subsets of
      cartesian products of the ACL2 universe of values,
      and the isomorphisms map tuples to tuples,
      as shown in the design notes."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto defiso)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name under which the domains, isomorphisms, and theorems
       are recorded in the world.")
     (xdoc::p
      "It must be a symbol that is not a keyword."))

    (xdoc::desc
     (list
      "@('doma')"
      "@('domb')"
      "@('alpha')"
      "@('beta')")
     (xdoc::p
      "Denote
       the domain @($A$),
       the domain @($B$),
       the isomorphism @($\\alpha$) from @($A$) to @($B$), and
       the isomorphism @($\\beta$) from @($B$) to @($A$).")
     (xdoc::evmac-desc-function/lambda/macro
      :subject "Each"
      :guard "the @(':guard-thms') input is @('t')")
     (xdoc::p
      "Let @('n') be the arity of @('doma'),
       and @('m') be the arity of @('domb').
       Then:
       @('alpha') must take @('n') arguments and return @('m') results;
       @('beta') must take @('m') arguments and return @('n') results;
       @('doma') and @('domb') must return one result."))

    (xdoc::desc
     "@(':unconditional') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether some of the applicability conditions
       and generated theorems are unconditional, i.e. without hypotheses
       (see details in `Variant: Unconditional Theorems' in the "
      *defiso-design-notes*
      ", and in the `Applicability Conditions' and `Generated Events' sections
       below):")
     (xdoc::ul
      (xdoc::li
       "@('t'), for unconditional (i.e. stronger) theorems.")
      (xdoc::li
       "@('nil'), for conditional (i.e. normal) theorems.")))

    (xdoc::desc
     "@(':guard-thms') &mdash; default @('t')"
     (xdoc::p
      "Determines whether the @('...-guard') applicability conditions below
       are checked, and generated as theorems:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to check and generate them.")
      (xdoc::li
       "@('nil'), to not check and generate them.")))

    (xdoc::desc
     "@(':thm-names') &mdash; default @('nil')"
     (xdoc::p
      "Non-default names for the generated theorems.")
     (xdoc::p
      "It must be a "
      (xdoc::seetopic "acl2::keyword-value-listp" "keyword-value list")
      " @('(thm1 name1 ... thmp namep)'),
       where each @('thmk') is a keyword
       that identifies one of the generated theorems below,
       and each @('namek') is a valid fresh theorem name."))

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print defiso)

    (xdoc::evmac-input-show-only defiso))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    defiso

    (xdoc::evmac-appcond
     ":alpha-image"
     (xdoc::&&
      (xdoc::p
       "The isomorphism @($\\alpha$) maps
        the domain @($A$) to the domain @($B$):")
      (xdoc::codeblock
       ";; when m = 1:"
       "(implies (doma a1 ... an)"
       "         (domb (alpha a1 ... an)))"
       ""
       ";; when m > 1:"
       "(implies (doma a1 ... an)"
       "         (mv-let (b1 ... bm) (alpha a1 ... an)"
       "           (domb b1 ... bm)))"))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($\\alpha{}A$)")

    (xdoc::evmac-appcond
     ":beta-image"
     (xdoc::&&
      (xdoc::p
       "The isomorphism @($\\beta$) maps
        the domain @($B$) to the domain @($A$):")
      (xdoc::codeblock
       ";; when n = 1:"
       "(implies (domb b1 ... bm)"
       "         (doma (beta b1 ... bm)))"
       ""
       ";; when n > 1:"
       "(implies (domb b1 ... bm)"
       "         (mv-let (a1 ... an) (beta b1 ... bm)"
       "           (doma a1 ... an)))"))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($\\beta{}B$)")

    (xdoc::evmac-appcond
     ":beta-of-alpha"
     (xdoc::&&
      (xdoc::p
       "The isomorphism @($\\beta$) is left inverse of
        the isomorphism @($\\alpha$):")
      (xdoc::codeblock
       ";; when m = n = 1 and :unconditional is nil:"
       "(implies (doma a)"
       "         (equal (beta (alpha a))"
       "                a))"
       ""
       ";; when m = n = 1 and :unconditional is t:"
       "(equal (beta (alpha a))"
       "       a)"
       ""
       ";; when m = 1 and n > 1 and :unconditional is nil:"
       "(implies (doma a1 ... an)"
       "         (mv-let (aa1 ... aan) (beta (alpha a1 ... an))"
       "           (and (equal aa1 a1)"
       "                ..."
       "                (equal aan an))))"
       ""
       ";; when m = 1 and n > 1 and :unconditional is t:"
       "(mv-let (aa1 ... aan) (beta (alpha a1 ... an))"
       "  (and (equal aa1 a1)"
       "       ..."
       "       (equal aan an)))"
       ""
       ";; when m > 1 and n = 1 and :unconditional is nil:"
       "(implies (doma a)"
       "         (mv-let (b1 ... bm) (alpha a)"
       "           (equal (beta b1 ... bm)"
       "                  a)))"
       ""
       ";; when m > 1 and n = 1 and :unconditional is t:"
       "(mv-let (b1 ... bm) (alpha a)"
       "  (equal (beta b1 ... bm)"
       "         a))"
       ""
       ";; when m > 1 and n > 1 and :unconditional is nil:"
       "(implies (doma a1 ... an)"
       "         (mv-let (b1 ... bm) (alpha a1 ... an)"
       "           (mv-let (aa1 ... aan) (beta b1 ... bm)"
       "             (and (equal aa1 a1)"
       "                  ..."
       "                  (equal aan an)))))"
       ""
       ";; when m > 1 and n > 1 and :unconditional is t:"
       "(mv-let (b1 ... bm) (alpha a1 ... an)"
       "  (mv-let (aa1 ... aan) (beta b1 ... bm)"
       "    (and (equal aa1 a1)"
       "         ..."
       "         (equal aan an))))"))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($\\beta{}\\alpha$) or  @($\\beta{}\\alpha'$)")

    (xdoc::evmac-appcond
     ":alpha-of-beta"
     (xdoc::&&
      (xdoc::p
       "The isomorphism @($\\alpha$) is left inverse of
        the isomorphism @($\\beta$):")
      (xdoc::codeblock
       ";; when n = m = 1 and :unconditional is nil:"
       "(implies (domb b)"
       "         (equal (alpha (beta b))"
       "                b))"
       ""
       ";; when n = m = 1 and :unconditional is t:"
       "(equal (alpha (beta b))"
       "       b)"
       ""
       ";; when n = 1 and m > 1 and :unconditional is nil:"
       "(implies (domb b1 ... bm)"
       "         (mv-let (bb1 ... bbm) (alpha (beta b1 ... bm))"
       "           (and (equal bb1 b1)"
       "                ..."
       "                (equal bbm bm))))"
       ""
       ";; when n = 1 and m > 1 and :unconditional is t:"
       "(mv-let (bb1 ... bbm) (alpha (beta b1 ... bm))"
       "  (and (equal bb1 b1)"
       "       ..."
       "       (equal bbm bm)))"
       ""
       ";; when n > 1 and m = 1 and :unconditional is nil:"
       "(implies (domb b)"
       "         (mv-let (a1 ... an) (beta b)"
       "           (equal (alpha a1 ... an)"
       "                  b)))"
       ""
       ";; when n > 1 and m = 1 and :unconditional is t:"
       "(mv-let (a1 ... an) (beta b)"
       "  (equal (alpha a1 ... an)"
       "         b))"
       ""
       ";; when n > 1 and m > 1 and :unconditional is nil:"
       "(implies (domb b1 ... bm)"
       "         (mv-let (a1 ... an) (beta b1 ... bm)"
       "           (mv-let (bb1 ... bbm) (alpha a1 ... an)"
       "             (and (equal bb1 b1)"
       "                  ..."
       "                  (equal bbm bm)))))"
       ""
       ";; when n > 1 and m > 1 and :unconditional is t:"
       "(mv-let (a1 ... an) (beta b1 ... bm)"
       "  (mv-let (bb1 ... bbm) (alpha a1 ... an)"
       "    (and (equal bb1 b1)"
       "         ..."
       "         (equal bbm bm))))"))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($\\alpha{}\\beta$) or @($\\alpha{}\\beta'$)")

    (xdoc::p
     "The @(':beta-image') and @(':alpha-of-beta') theorems
      imply that the isomorphism @($\\alpha$)
      is surjective over the domain @($B$):
      for every @('(b1 ... bm)') in @('domb')
      there is a @('(a1 ... an)') in @('doma'),
      namely @('(beta b1 ... bm)'),
      such that @('(alpha a1 ... bm)') is @('(b1 ... bm)').
      See @($\\alpha{}s$) in the "
     *defiso-design-notes*
     ".")

    (xdoc::p
     "The @(':alpha-image') and @(':beta-of-alpha') theorems
      imply that the isomorphism @($\\beta$)
      is surjective over the domain @($A$):
      for every @('(a1 ... an)') in @('doma')
      there is a @('(b1 ... bm)') in @('domb'),
      namely @('(alpha a1 ... an)'),
      such that @('(beta b1 ... bm)') is @('(a1 ... an)').
      See @($\\beta{}s$) in the "
     *defiso-design-notes*
     ".")

    (xdoc::evmac-appcond
     ":doma-guard"
     (xdoc::&&
      (xdoc::p
       "The domain @($A$) is well-defined everywhere:")
      (xdoc::codeblock
       "doma-guard<a1,...,an>")
      (xdoc::p
       "where @('doma-guard<a1,...,an>') is:
        the guard term of @('doma'),
        if @('doma') is a function;
        the guard obligation of the body of @('doma'),
        if @('doma') is a lambda expression."))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($G{}A$)"
     :presence "@(':guard-thms') is @('t')")

    (xdoc::evmac-appcond
     ":domb-guard"
     (xdoc::&&
      (xdoc::p
       "The domain @($B$) is well-defined everywhere:")
      (xdoc::codeblock
       "domb-guard<b1,...,bm>")
      (xdoc::p
       "where @('domb-guard<b1,...,bm>') is:
        the guard term of @('domb'),
        if @('domb') is a function;
        the guard obligation of the body of @('domb'),
        if @('domb') is a lambda expression."))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($G{}B$)"
     :presence "@(':guard-thms') is @('t')")

    (xdoc::evmac-appcond
     ":alpha-guard"
     (xdoc::&&
      (xdoc::p
       "The isomorphism @($\\alpha$) is well-defined
        at least over the domain @($A$):")
      (xdoc::codeblock
       "(implies (doma a1 ... an)"
       "         alpha-guard<a1,...,an>)")
      (xdoc::p
       "where @('alpha-guard<a1,...,an>') is:
        the guard term of @('alpha'),
        if @('alpha') is a function;
        the guard obligation of the body of @('alpha'),
        if @('alpha') is a lambda expression."))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($G{}\\alpha$)"
     :presence "@(':guard-thms') is @('t')")

    (xdoc::evmac-appcond
     ":beta-guard"
     (xdoc::&&
      (xdoc::p
       "The isomorphism @($\\beta$) is well-defined
        at least over the domain @($B$):")
      (xdoc::codeblock
       "(implies (domb b1 ... bm)"
       "         beta-guard<b1,...,bm>)")
      (xdoc::p
       "where @('beta-guard<b1,...,bm>') is:
        the guard term of @('beta'),
        if @('beta') is a function;
        the guard obligation of the body of @('beta'),
        if @('beta') is a lambda expression."))
     :design-notes *defiso-design-notes*
     :design-notes-appcond "@($G{}\\beta$)"
     :presence "@(':guard-thms') is @('t')"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "Unless overridden via the @(':thm-names') input,
      the name of each generated theorem consists of
      the input @('name') of @('defiso'),
      followed by @('.'),
      followed by the identifying keyword (without @(':')) below.")

    (xdoc::p
     "The theorems are generated as enabled rewrite rules
      if they are valid rewrite rules;
      otherwise, they are generated with no rule classes.
      This is done via @(tsee defthmr).")

    (xdoc::desc
     (list
      "@(':alpha-image')"
      "@(':beta-image')"
      "@(':beta-of-alpha')"
      "@(':alpha-of-beta')"
      "@(':doma-guard')"
      "@(':domb-guard')"
      "@(':alpha-guard')"
      "@(':beta-guard')")
     (xdoc::p
      "A theorem for each applicability condition.
       The @('...-guard') theorems are generated if and only if
       @(':guard-thms') is @('t')."))

    (xdoc::desc
     "@(':alpha-injective')"
     (xdoc::p
      "The isomorphism @($\\alpha$) is injective:")
     (xdoc::codeblock
      ";; when :unconditional is nil:"
      "(defthmr name.alpha-injective"
      "  (implies (and (doma a1 ... an)"
      "                (doma aa1 ... aan))"
      "           (equal (equal (alpha a1 ... an)"
      "                         (alpha aa1 ... aan))"
      "                  (and (equal a1 aa1)"
      "                       ..."
      "                       (equal an aan)))))"
      ""
      ";; when :unconditional is t:"
      "(defthmr name.alpha-injective"
      "  (equal (equal (alpha a1 ... an)"
      "                (alpha aa1 ... aan))"
      "         (and (equal a1 aa1)"
      "              ..."
      "              (equal an aan))))")
     (xdoc::p
      "This corresponds to @($\\alpha{}i$) or @($\\alpha{}i'$) in the "
      *defiso-design-notes*
      ".")
     (xdoc::p
      "This theorem is automatically proved
       from the applicability conditions."))

    (xdoc::desc
     "@(':beta-injective')"
     (xdoc::p
      "The isomorphism @($\\beta$)
       is injective over the domain @($B$):")
     (xdoc::codeblock
      ";; when :unconditional is nil:"
      "(defthmr name.beta-injective"
      "  (implies (and (domb b1 ... bm)"
      "                (domb bb1 ... bbm))"
      "           (equal (equal (beta b1 ... bm)"
      "                         (beta bb1 ... bbm))"
      "                  (and (equal b1 bn1)"
      "                       ..."
      "                       (equal bm bbm)))))"
      ""
      ";; when :unconditional is t:"
      "(defthmr name.beta-injective"
      "  (equal (equal (beta b1 ... bm)"
      "                (beta bb1 ... bbm))"
      "         (and (equal b1 bn1)"
      "              ..."
      "              (equal bm bbm))))")
     (xdoc::p
      "This corresponds to @($\\beta{}i$) or @($\\beta{}i'$) in the "
      *defiso-design-notes*
      ".")
     (xdoc::p
      "This theorem is automatically proved
       from the applicability conditions.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy defiso)))
