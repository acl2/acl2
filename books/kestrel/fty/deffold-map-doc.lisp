; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

; Based on deffold-reduce-doc.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc deffold-map

  :parents (fold)

  :short "Mapping folds for fixtypes."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro automates the creation of
      the `mapping' class of folds on fixtypes
      described in @(see fold).
      The user specifies any number of overrides of the boilerplate code
      for specific cases of the fixtypes
      in the same manner as @(see deffold-reduce).")
    (xdoc::p))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(deffold-map suffix"
     "             :types      ...  ; no default"
     "             :extra-args ...  ; default nil"
     "             :override   ...  ; default nil"
     "             :parents    ...  ; no default"
     "             :short      ...  ; no default"
     "             :long       ...  ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('suffix')"
     (xdoc::p
      "Suffix for the generated function names.
       The name of each generated function is @('<type>-<suffix>'),
       where @('<type>') is the type that the function operates on,
       and @('<suffix>') is the value of this input,
       which must be a symbol.
       The function name is interned in the same package as @('<suffix>')."))

    (xdoc::desc
     "@(':types') &mdash; no default"
     (xdoc::p
      "Fixtype for which map functions must be generated.")
     (xdoc::p
      "This must be a list of symbols, which is not evaluated by the macro,
       where each symbols must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "The name of an existing fixtype,
        if the fixtype is not recursive or singly recursive:
        this specifies the fixtype itself.")
      (xdoc::li
       "The name of an existing clique
        of two or more mutually recursive fixtypes:
        this specifies the fixtypes in the clique."))
     (xdoc::p
      "These symbols must be listed in bottom-up order,
       i.e. according to the order in which they are defined.")
     (xdoc::p
      "The following fixtypes can be specified
       (i.e. are currently supported by this tool):")
     (xdoc::ul
      (xdoc::li
       "@(tsee defprod) fixtypes.")
      (xdoc::li
       "@(tsee deftagsum) fixtypes.")
      (xdoc::li
       "@(tsee deflist) fixtypes.
        In this case, the element fixtype
        must be specified by the @(':types') input too.")
      (xdoc::li
       "@(tsee defoption) fixtypes.
        In this case, the base fixtype
        must be specified by the @(':types') input too.")
      (xdoc::li
       "@(tsee defomap) fixtypes.
        In this case,
        the value fixtype
        must be specified by the @(':types') input too,
        while the key fixtype must not.")))

    (xdoc::desc
     "@(':extra-args') &mdash; default @('nil')"
     (xdoc::p
      "Extra arguments of the functions,
       which are passed unchanged to the recursive calls.")
     (xdoc::p
      "This must be a list of "
      (xdoc::seetopic "std::extended-formals" "extended formals")
      " which @('deffold-map') puts into the generated @(tsee define)s."))

    (xdoc::desc
     "@(':override') &mdash; default @('nil')"
     (xdoc::p
      "Specifies which boilerplate results should be overridden.
       It is used as described in the Section `Generated Events' below.")
     (xdoc::p
      "This must be a parenthesized list @('(ovrd1 ... ovrd<n>)'),
       with @('<n> >= 0'),
       where each @('ovrd<i>') has one of two possible forms:")
     (xdoc::ul
      (xdoc::li
       "A pair @('(<type> <term>)'),
        where @('<type>') is a @(tsee defprod) or @(tsee deftagsum),
        and @('<term>') is an (untranslated) term
        whose only free variables may be @('<type>')
        and the formals specified in @(':extra-args').")
      (xdoc::li
       "A triple @('(<type> <kind> <term>)'),
        where @('<type>') is a @(tsee deftagsum),
        @('<kind>') is a keyword identifying one of the summands of the type,
        and @('<term>') is an (untranslated) term
        whose only free variables may be @('<type>')
        and the formals specified in @(':extra-args').")))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are added to the generated XDOC topic
       described in the Section `Generated Events' below.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('abstract-syntax-<suffix>')"
     (xdoc::p
      "An XDOC topic whose name is obtained by adding,
       at the end of the symbol @('abstract-syntax-'),
       the symbol specified by the @('suffix') input.
       If any of the @(':parents'), @(':short'), or @(':long') inputs
       are provided, they are added to this XDOC topic.
       This XDOC topic is generated with @(tsee acl2::defxdoc+),
       with @(':order-topics t'),
       so that the other generated events (described below),
       which all have this XDOC topic as parent,
       are listed in order as subtopics."))

    (xdoc::desc
     "@('<type>-<suffix>')"
     (xdoc::p
      "For each type @('<type>') specified by the @(':types') input,
       a map function for that type, defined as follows:")
     (xdoc::ul
      (xdoc::li
       "If @('<type>') is a @(tsee defprod):"
       (xdoc::ul
        (xdoc::li
         "If the @(':override') input includes
          an element @('(<type> <term>')),
          the function is defined to return @('<term>').")
        (xdoc::li
         "If the @(':override') input does not include
          an element of the form @('(<type> <term>')),
          the function is defined to return the following:")
        (xdoc::ul
         (xdoc::li
          "If @('<type>') has no components whose type
           is specified by the @(':types') input,
           the function is defined to return
           the fixed input.")
         (xdoc::li
          "If @('<type>') has one or more components whose types
           are specified by the @(':types') input,
           the function is defined to return
           the map over the product fields."))))
      (xdoc::li
       "If @('<type>') is a @(tsee deftagsum):"
       (xdoc::ul
        (xdoc::li
         "If the @(':override') input includes
          an element @('(<type> <term>')),
          the function is defined to return @('<term>').")
        (xdoc::li
         "Otherwise, the function is defined via @('<type>-case'),
          and the case for each keyword @('<kind>') is as follows:"
         (xdoc::ul
          (xdoc::li
           "If the @(':override') input includes
            an element @('(<type> <kind> <term>')),
            the case is defined to return @('<term>').")
          (xdoc::li
           "If the @(':override') input does not include
            any element of the form @('(<type> <kind> <term>')):"
           (xdoc::ul
            (xdoc::li
             "If the summand corresponding to @('<kind>')
              has no components whose type
              is specified by the @(':types') input,
              the case is defined to return
              the term specified by the @(':default') input.")
            (xdoc::li
             "If the summand corresponding to @('<kind>')
              has one or more components whose types
              are specified by the @(':types') input,
              the case is defined to return
              the map over the product fields.")))))))
      (xdoc::li
       "If @('<type>') is a @(tsee deflist):"
       (xdoc::ul
        (xdoc::li
         "If the list is empty,
          the function is defined to return @('nil').")
        (xdoc::li
         "If the list is not empty,
          the function is defined to return
          the @(tsee cons) of the mapped @(tsee car)
          to the recursively mapped @(tsee cdr).")))
      (xdoc::li
       "If @('<type>') is a @(tsee defoption):"
       (xdoc::ul
        (xdoc::li
         "If the option value is @('nil'),
          the function is defined to return @('nil').")
        (xdoc::li
         "If the option value is not @('nil'),
          the function is defined to return
          the map function of the base type applied to the value.")))
      (xdoc::li
       "If @('<type>') is a @(tsee defomap):"
       (xdoc::ul
        (xdoc::li
         "If the map is empty,
          the function is defined to return @('nil').")
        (xdoc::li
         "If the map is not empty,
          the function is defined to return
          the @(tsee omap::update) of the @(tsee head) key
          and the mapped value
          to the recursively mapped @('omap::tail').")))))

    (xdoc::desc
     "Accompanying list theorems."
     (xdoc::p
      "For each @(tsee deflist) type specified by the @(':types') input,
       we generate the following theorems,
       whose exact form can be inspected with @(tsee pe) or similar command:")
     (xdoc::ul
      (xdoc::li
       "@('<type>-<suffix>-type-prescription')")
      (xdoc::li
       "@('<type>-<suffix>-when-atom')")
      (xdoc::li
       "@('<type>-<suffix>-of-cons')")
      (xdoc::li
       "@('<type>-<suffix>-of-append')")
      (xdoc::li
       "@('consp-of-<type>-<suffix>')")
      (xdoc::li
       "@('len-of-<type>-<suffix>')")
      (xdoc::li
       "@('nth-of-<type>-<suffix>')")
      (xdoc::li
       "@('<type>-<suffix>-of-revappend')")
      (xdoc::li
       "@('<type>-<suffix>-of-reverse')"))
     (xdoc::p
      "These theorems are disabled,
       and added to the generated ruleset described below."))

    (xdoc::desc
     "Accompanying option theorems."
     (xdoc::p
      "For each @(tsee defoption) type specified by the @(':types') input,
       we generate the following theorems,
       whose exact form can be inspected with @(tsee pe) or similar command:")
     (xdoc::ul
      (xdoc::li
       "@('<type>-<suffix>-under-iff')"))
     (xdoc::p
      "These theorems are disabled,
       and added to the generated ruleset described below."))

    (xdoc::desc
     "Accompanying omap type theorems."
     (xdoc::p
      "For each @(tsee defomap) type specified by the @(':types') input,
       we generate the following theorems,
       whose exact form can be inspected with @(tsee pe) or similar command:")
     (xdoc::ul
      (xdoc::li
       "@('<type>-<suffix>-type-prescription')")
      (xdoc::li
       "@('<type>-<suffix>-when-emptyp')")
      (xdoc::li
       "@('emptyp-of-<type>-<suffix>')")
      (xdoc::li
       "@('keys-of-<type>-<suffix>')")
      (xdoc::li
       "@('assoc-of-<type>-<suffix>')"))
     (xdoc::p
      "These theorems are disabled,
       and added to the generated ruleset described below."))

    (xdoc::desc
     "@('abstract-syntax-<suffix>-rules')"
     (xdoc::p
      "A "
      (xdoc::seetopic "acl2::rulesets" "ruleset")
      " with the theorems that accompany the fold functions."))

    (xdoc::p
     "The theorems that accompany the predicates
      are generated as part of the @(tsee define) and @(tsee defines)
      that define the predicates, after the @('///')."))))
