; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defsurj")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

; (depends-on "design-notes/defsurj.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *defsurj-design-notes*
  (xdoc::a :href "res/kestrel-std-util-design-notes/defsurj.pdf" "design notes"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defsurj

  :parents (std/util-extensions std/util)

  :short "Establish a surjective mapping between two domains."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "A surjective mapping between two domains (i.e. predicates)
      @($A$) and @($B$)
      consists of a surjective conversion (i.e. function)
      @($\\alpha$) from @($A$) to @($B$)
      and a right inverse conversion (i.e. function)
      @($\\beta$) from @($B$) to @($A$)
      that witnesses the surjectivity.
      The domains and conversions are illustrated in these "
     *defsurj-design-notes*
     ", which use this "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "notation")
     ". The right inverse @($\\beta$)
      is not necessarily uniquely determined,
      i.e. there may exist more than one,
      unless the surjection @($\\alpha$) is also injective.")

    (xdoc::p
     "This macro attempts to verify that
      a specified conversion is a surjection
      between two specified domains,
      and that another specified conversion is
      a right inverse of the surjection.
      The verification amounts to
      proving the applicability conditions below as theorems.")

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
      as shown in the design notes."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto defsurj)

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
      "@('(thm1 name1 ... thmp namep)'),
       where each @('thmk') is a keyword
       that identifies one of the generated theorems below,
       and each @('namek') is a valid fresh theorem name."))

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print defsurj)

    (xdoc::evmac-input-show-only defsurj))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    defsurj

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
     :design-notes *defsurj-design-notes*
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
     :design-notes *defsurj-design-notes*
     :design-notes-appcond "@($\\beta{}B$)")

    (xdoc::evmac-appcond
     ":alpha-of-beta"
     (xdoc::&&
      (xdoc::p
       "The conversion @($\\alpha$) is left inverse of @($\\beta$), i.e.
        the conversion @($\\beta$) is right inverse of @($\\alpha$):")
      (xdoc::codeblock
       ";; when n = m = 1:"
       "(implies (domb b)"
       "         (equal (alpha (beta b))"
       "                b))"
       ""
       ";; when n = 1 and m > 1:"
       "(implies (domb b1 ... bm)"
       "         (mv-let (bb1 ... bbm) (alpha (beta b1 ... bm))"
       "           (and (equal bb1 b1)"
       "                ..."
       "                (equal bbm bm))))"
       ""
       ";; when n > 1 and m = 1:"
       "(implies (domb b)"
       "         (mv-let (a1 ... an) (beta b)"
       "           (equal (alpha a1 ... an)"
       "                  b)))"
       ";; when n > 1 and m > 1:"
       "(implies (domb b1 ... bm)"
       "         (mv-let (a1 ... an) (beta b1 ... bm)"
       "           (mv-let (bb1 ... bbm) (alpha a1 ... an)"
       "             (and (equal bb1 b1)"
       "                  ..."
       "                  (equal bbm bm)))))"))
     :design-notes *defsurj-design-notes*
     :design-notes-appcond "@($\\alpha{}\\beta$)")

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
     :design-notes *defsurj-design-notes*
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
     :design-notes *defsurj-design-notes*
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
     :design-notes *defsurj-design-notes*
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
     :design-notes *defsurj-design-notes*
     :design-notes-appcond "@($G{}\\beta$)"
     :presence "@(':guard-thms') is @('t')"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "Unless overridden via the @(':thm-names') input,
      the name of each generated theorem consists of
      the input @('name') of @('defsurj'),
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
      "@(':alpha-of-beta')"
      "@(':doma-guard')"
      "@(':domb-guard')"
      "@(':alpha-guard')"
      "@(':beta-guard')")
     (xdoc::p
      "A theorem for each applicability condition.
       The @('...-guard') theorems are generated if and only if
       @(':guard-thms') is @('t').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy defsurj)))
