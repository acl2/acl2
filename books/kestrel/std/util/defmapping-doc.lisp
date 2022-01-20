; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

; (depends-on "design-notes/defmapping.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *defmapping-design-notes*
  (xdoc::a
   :href "res/kestrel-std-util-design-notes/defmapping.pdf"
   "design notes"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defmapping

  :parents (std::std/util-extensions std/util)

  :short "Establish a mapping between two domains."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "A mapping between two domains (i.e. predicates) @($A$) and @($B$)
      consists of two conversions (i.e. functions) @($\\alpha$) and @($\\beta$).
      The domains and conversions are illustrated in these "
     *defmapping-design-notes*
     ", which use this "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "notation")
     ". Each of the conversions may be
      injective, surjective, both (i.e. bijective), or neither.")

    (xdoc::p
     "This macro attempts to verify that
      two specified conversions are mappings between two specified domains
      i.e. that they map values in one domain to values in the other domain.
      Optionally, the macro also attempts to verify
      additional properties of the conversions
      that imply injectivity and/or surjectivity.
      The verification amounts to
      proving the applicability conditions below as theorems,
      from which additional theorems are automatically proved.")

    (xdoc::p
     "The domains, conversions, and theorems
      are recorded in the ACL2 @(see world),
      under a specified name that can be referenced from other tools
      (e.g. " (xdoc::seetopic "apt::apt" "APT") " transformations).")

    (xdoc::p
     "The domains may have multiple arguments,
      and the conversions may have multiple arguments and results.
      In this case, the domains are subsets of
      cartesian products of the ACL2 universe of values,
      and the conversions map tuples to tuples,
      as shown in the `Generalization to Tuples' page of the design notes."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defmapping name"
     "            doma"
     "            domb"
     "            alpha"
     "            beta"
     "            :beta-of-alpha-thm ..."
     "            :alpha-of-beta-thm ..."
     "            :guard-thms ..."
     "            :unconditional ..."
     "            :thm-names ..."
     "            :thm-enable ..."
     "            :hints ..."
     "            :print ..."
     "            :show-only ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name under which the domains, conversions, and theorems
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
       the conversion @($\\alpha$) from @($A$) to @($B$), and
       the conversion @($\\beta$) from @($B$) to @($A$).")
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
     "@(':beta-of-alpha-thm') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether
       the @(':beta-of-alpha') applicability condition is generated or not,
       which in turn determines whether certain theorems are generated or not.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to generate them.")
      (xdoc::li
       "@('nil'), to not generate them.")))

    (xdoc::desc
     "@(':alpha-of-beta-thm') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether
       the @(':alpha-of-beta') applicability condition is generated or not,
       which in turn determines whether certain theorems are generated or not.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to generate them.")
      (xdoc::li
       "@('nil'), to not generate them.")))

    (xdoc::desc
     "@(':guard-thms') &mdash; default @('t')"
     (xdoc::p
      "Determines whether the @('...-guard') applicability conditions
       are present or not, and generated as theorems.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to check and generate them.")
      (xdoc::li
       "@('nil'), to not check and generate them.")))

    (xdoc::desc
     "@(':unconditional') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether some of the applicability conditions
       and generated theorems are unconditional, i.e. without hypotheses
       (see the `Variant: Unconditional Theorems' page of the "
      *defmapping-design-notes*
      ", and the `Applicability Conditions' and `Generated Events' sections
       below).")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), for unconditional (i.e. stronger) theorems.")
      (xdoc::li
       "@('nil'), for conditional (i.e. normal) theorems."))
     (xdoc::p
      "It may be @('t') only if
       @(':beta-of-alpha-thm') is @('t') or
       @(':alpha-of-beta-thm') is @('t')."))

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

    (xdoc::desc
     "@(':thm-enable') &mdash; default @('nil')"
     (xdoc::p
      "Determines which of the generated theorems must be enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('nil'), to enable none of them.")
      (xdoc::li
       "@(':all'), to enable all of them.")
      (xdoc::li
       "@(':all-nonguard'), to enable all of them
        except for the @('...-guard') theorems.")
      (xdoc::li
       "A non-empty list @('(thm1 ... thmp)'),
        where each @('thmk') is a keyword
        that identifies one of the generated theorems below,
        to enable the theorems identified by the keywords.
        Only keywords for theorems that are generated
        (based on the @(':beta-of-alpha-thm'), @(':alpha-of-beta-thm'), and
        @(':guard-thms') inputs)
        may be in this list."))
     (xdoc::p
      "As explained under `" xdoc::*evmac-section-generated-title* "',
       the theorems are generated as rewrite rules,
       if they are valid rewrite rules.
       The enablement specified by @(':thm-enable') applies
       only to those theorems that are rewrite rules;
       it is ignored for theorems that are not rewrite rules.")
     (xdoc::p
      "Note that the first and last option could be described as a single one,
       namely as a possibly empty list of theorem keywords,
       where the empty list @('nil') enables no theorem.
       The @(':all') option is provided for completeness,
       but the @(':all-nonguard') may be more useful:
       in general, the @('...-guard') theorems
       do not look like useful rewrite rules,
       while the other theorems generally do.")
     (xdoc::p
      "If @(':guard-thms') is ('nil'),
       then the @(':all') and @(':all-nonguard') options are equivalent."))

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print defmapping)

    (xdoc::evmac-input-show-only defmapping))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    defmapping

    (xdoc::evmac-appcond
     ":alpha-image"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\alpha$) maps
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($\\alpha{}A$)")

    (xdoc::evmac-appcond
     ":beta-image"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\beta$) maps
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($\\beta{}B$)")

    (xdoc::evmac-appcond
     ":beta-of-alpha"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\beta$) is left inverse of @($\\alpha$), i.e.
        the conversion @($\\alpha$) is right inverse of @($\\beta$):")
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($\\beta{}\\alpha$) or @($\\beta{}\\alpha'$)"
     :presence "@(':beta-of-alpha-thm') is @('t')")

    (xdoc::evmac-appcond
     ":alpha-of-beta"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\alpha$) is left inverse of @($\\beta$), i.e.
        the conversion @($\\beta$) is right inverse of @($\\alpha$):")
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($\\alpha{}\\beta$) or @($\\alpha{}\\beta'$)"
     :presence "@(':alpha-of-beta-thm') is @('t')")

    (xdoc::p
     "The @(':beta-of-alpha') applicability condition (when present)
      implies the injectivity of @($\\alpha$).
      See the @($\\alpha{}i$) and @($\\alpha{}i'$) theorems in the "
     *defmapping-design-notes*
     ", and the generated theorem @(':alpha-injective') below.")

    (xdoc::p
     "The @(':alpha-of-beta') applicability condition (when present)
      implies the injectivity of @($\\beta$).
      See the @($\\beta{}i$) and @($\\beta{}i'$) theorems in the "
     *defmapping-design-notes*
     ", and the generated theorem @(':beta-injective') below.")

    (xdoc::p
     "The @(':alpha-image') applicability condition (always present)
      and the @(':alpha-of-beta') applicabilty condition (when present)
      imply the surjectivity of @($\\alpha$).
      See the @($\\alpha{}s$) and @($\\alpha{}s'$) theorems in the "
     *defmapping-design-notes*
     ".")

    (xdoc::p
     "The @(':beta-image') applicability condition (always present)
      and the @(':beta-of-alpha') applicabilty condition (when present)
      imply the surjectivity of @($\\beta$).
      See the @($\\beta{}s$) and @($\\beta{}s'$) theorems in the "
     *defmapping-design-notes*
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
     :design-notes *defmapping-design-notes*
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($G{}B$)"
     :presence "@(':guard-thms') is @('t')")

    (xdoc::evmac-appcond
     ":alpha-guard"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\alpha$) is well-defined
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($G{}\\alpha$)"
     :presence "@(':guard-thms') is @('t')")

    (xdoc::evmac-appcond
     ":beta-guard"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\beta$) is well-defined
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
     :design-notes *defmapping-design-notes*
     :design-notes-appcond "@($G{}\\beta$)"
     :presence "@(':guard-thms') is @('t')"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "Unless overridden via the @(':thm-names') input,
      the name of each generated theorem consists of
      the input @('name') of @('defmapping'),
      followed by @('.'),
      followed by the identifying keyword (without @(':')) below.")

    (xdoc::p
     "The theorems are generated as rewrite rules
      if they are valid rewrite rules;
      otherwise, they are generated with no rule classes.
      The macros @(tsee defthmr) and @('defthmdr')
      are used to generate the theorems.")

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
       The @(':beta-of-alpha') theorem is generated if and only if
       the @(':beta-of-alpha-thm') input is @('t').
       The @(':alpha-of-beta') theorem is generated if and only if
       the @(':alpha-of-beta-thm') input is @('t').
       The @('...-guard') theorems are generated if and only if
       the @(':guard-thms') input is @('t')."))

    (xdoc::desc
     "@(':alpha-injective')"
     (xdoc::p
      "The conversion @($\\alpha$) is injective:")
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
      *defmapping-design-notes*
      ".")
     (xdoc::p
      "This theorem is automatically proved
       from the applicability conditions.")
     (xdoc::p
      "This theorem is generated if and only if
       the @(':beta-of-alpha-thm') input is @('t')."))

    (xdoc::desc
     "@(':beta-injective')"
     (xdoc::p
      "The conversion @($\\beta$)
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
      *defmapping-design-notes*
      ".")
     (xdoc::p
      "This theorem is automatically proved
       from the applicability conditions.")
     (xdoc::p
      "This theorem is generated if and only if
       the @(':alpha-of-beta-thm') input is @('t').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy defmapping)))
