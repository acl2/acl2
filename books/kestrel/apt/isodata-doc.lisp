; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/apt/utilities/xdoc-constructors" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "isodata")

; (depends-on "design-notes/isodata.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *isodata-design-notes*
  (xdoc::ahref "res/kestrel-apt-design-notes/isodata.pdf" "design notes"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc isodata

  :parents (apt)

  :short "APT isomorphic data transformation:
          change function arguments into isomorphic representations."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This transformation changes the representation of
      one or more of a function's arguments
      into an isomorphic representation.
      This transformation is useful
      to carry out certain data type refinements
      (when synthesizing programs),
      or to raise the level of abstraction of certain types
      (when analyzing programs).")

    (xdoc::p
     "By regarding the remaining arguments
      as being changed via an indentity isomorphism,
      we can say that this transformation changes the representation of
      (the tuple of) all the function's arguments
      into a new representation that is element-wise isomorphic.")

    (xdoc::p
     "There are two variants of this transformation:")
    (xdoc::ul
     (xdoc::li
      "When the function operates only on argument tuples
       in the old representation
       (i.e. when the function's guard is a subset of the old representation),
       the function is transformed to operate in the same way on
       exactly the argument tuples in the new representation
       that are isomorphic to the old guard.")
     (xdoc::li
      "When the function operates on
       at least all tuples in the old representation (and possibly more)
       (i.e. the function's guard is a superset of the old representation),
       and is used as a predicate to recognize
       a subset of argument tuples all of which are in the old representation,
       the function is transformed to recognize
       exactly the argument tuples in the new representation
       that are isomorphic to the ones recognized by the old function."))
    (xdoc::p
     "These two variants involve slightly different applicability conditions
      and produce slightly different results.
      These two variants are selected
      via the @(':predicate') input (see below).")

    (xdoc::p
     "These " *isodata-design-notes* ", which use "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "notation")
     ", provide the mathematical concepts and (meta) proofs
      upon which this transformation is based.
      These notes should be read alongside this reference documentation,
      which refers to the them in numerous places.")

    (xdoc::p
     "The " *isodata-design-notes* " cover
      isomorphic transformations of both arguments and results,
      compositionally established
      by partitioning arguments and results of old and new functions
      and by establishing sub-mappings between the partitions
      (see the `Compositional Establishment of Isomorphic Mappings on Tuples'
      section in the design notes).
      The current implementation is more limited,
      supporting only the transformation of arguments (not results),
      and only a limited form of partition of the arguments (see below).
      There are plans to extend the implementation
      to match the coverage of the design notes,
      mamely transforming results
      and allowing arbitrary partiions of arguments and results."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto isodata)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must
       be in logic mode,
       be defined,
       have at least one argument, and
       have no input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
       If the @(':predicate') input (see below) is @('t'),
       @('old') must return a non-<see topic='@(url mv)'>multiple</see> value.
       If @('old') is recursive, it must
       be singly (not mutually) recursive,
       not have a @(':?') measure, and
       not occur in its own <see topic='@(url tthm)'>termination theorem</see>
       (i.e. not occur in the tests and arguments of its own recursive calls).
       If the @(':verify-guards') input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "In the rest of this documentation page:")
     (xdoc::ul
      (xdoc::li
       "Let @('x1'), ..., @('xn') be the arguments of @('old'),
        where @('n') &gt; 0.")
      (xdoc::li
       "Let @('old-guard<x1,...,xn>') be the guard term of @('old').")
      (xdoc::li
       "If @('old') is not recursive, let
        @({
          old-body<x1,...,xn>
        })
        be the body of @('old').")
      (xdoc::li
       "If @('old') is recursive, let
        @({
          old-body<x1,...,xn,
                   (old update1-x1<x1,...,xn>
                        ...
                        update1-xn<x1,...,xn>)
                   ...
                   (old updatem-x1<x1,...,xn>
                        ...
                        updatem-xn<x1,...,xn>)>
        })
        be the body of @('old'),
        where @('m') &gt; 0 is the number of recursive calls
        in the body of @('old')
        and each @('updatej-xi<x1,...,xn>') is
        the @('i')-th actual argument passed to the @('j')-th recursive call.
        Furthermore,
        let @('contextj<x1,...,xn>') be the context (i.e. controlling tests)
        in which the @('j')-th recursive call occurs,
        and let @('measure<x1,...,xn>') be the measure term of @('old')."))
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('old') is denoted by
       @($f$) when @(':predicate') is @('nil'),
       and @($p$) when @(':predicate') is @('t')."))

    (xdoc::desc
     "@('args-iso')"
     (xdoc::p
      "Specifies the arguments of @('old') that are transformed
       and the way in which they are transformed.")
     (xdoc::p
      "It must be a singleton list of doublets "
      (xdoc::tt "(args iso)")
      " (future versions of @('isodata') will allow non-singleton lists),
       where:")
     (xdoc::ul
      (xdoc::li
       (xdoc::p
        "@('args') denotes the arguments of @('old')
         whose representation is transformed.")
       (xdoc::p
        "It must be one of the following:")
       (xdoc::ul
        (xdoc::li
         "A non-empty list without duplicates of elements of @('(x1 ... xn)'),
          in any order.")
        (xdoc::li
         "A single element @('xi') of @('(x1 ... xn)'),
          abbreviating the singleton list @('(xi)')."))
       (xdoc::p
        "In the rest of the documentation page, for expository convenience,
         it is assumed that @('args') is @('(y1 ... yp)')
         and that they are in the same order as in @('(x1 ... xn)')."))
      (xdoc::li
       (xdoc::p
        "@('iso') denotes the old and new isomorphic representations
         and the isomorphisms between them.")
       (xdoc::p
        "It must be one of the following:")
       (xdoc::ul
        (xdoc::li
         "A symbol that references
          a previous successful call of @(tsee defiso),
          i.e. the symbol must be the @('name') input of that call.
          The domains and isomorphisms recorded under that name specify:
          the recognizer of the old representation (@('doma')),
          which we call @('oldp') in the rest of this documentation page;
          the recognizer of the new representation (@('domb')),
          which we call @('newp') in the rest of this documentation page;
          the conversion from the old to the new representation (@('alpha')),
          which we call @('forth') in the rest of this documentation page; and
          the conversion from the new to the old representation (@('beta')),
          which we call @('back') in the rest of this documentation page.
          Both @('oldp') and @('newp') must be unary.
          If the generated function is guard-verified
          (which is determined by the @(':verify-guards') input; see below),
          the call of @(tsee defiso)
          must have @(':guard-thms') equal to @('t'),
          i.e. it must have proved and recorded the guard-related theorems.")
        (xdoc::li
         "A list @('(oldp newp forth back :hints hints)')
          such that the call
          @('(defiso name oldp newp forth back
               :guard-thms guard-thms :thm-names thm-names :hints hints)')
          is successful,
          where @('name') and @('thm-names') consist of suitably fresh names,
          and where @('guard-thms') is
          @('t') if the generated function is guard-verified
          (which is determined by the @(':verify-guards') input; see below)
          and @('nil') otherwise.
          A list @('(oldp newp forth back)')
          abbreviates @('(oldp newp forth back :hints nil)').
          The @('isodata') transformation generates
          this call of @(tsee defiso),
          and uses it in the same way as it uses a call referenced by @('iso')
          when @('iso') is a symbol;
          however, this generated @(tsee defiso) call
          is local to the @(tsee encapsulate) generated by @('isodata'),
          and cannot be therefore referenced
          after the call of @('isodata')."))))
     (xdoc::p
      "In the " *isodata-design-notes* ", the section
       `Compositional Establishment of Isomorphic Mappings on Tuples'
       describes the compositional establishment of an isomorphic mapping
       between the inputs of old and new function.
       The @('args-iso') input currently supported by this transformation
       amounts to the following partitioning and sub-mappings:"
      (xdoc::ul
       (xdoc::li
        "The new function's arguments are the same (i.e. have the same names)
         as the old function's arguments, i.e. @('x1'), ..., @('xn').")
       (xdoc::li
        "The arguments are partitioned into @('n') singleton partitions.")
       (xdoc::li
        "The (unary) isomorphic mapping specified in @('args-iso')
         is used for each of the @('y1'), ..., @('yp') partitions.")
       (xdoc::li
        "An implicit identity isomorphism over all ACL2 values
         is used for the remaining partitions.")))
     (xdoc::p
      "In the design notes,
       the resulting isomorphic mapping over all function arguments
       is denoted as consisting of
       the domains @($A$) and @($A'$) and
       the isomorphisms @($\\alpha$) and @($\\alpha'$).")
     (xdoc::p
      "The transformation of results,
       and the establishment of isomorphic mappings between results,
       is not supported yet."))

    (xdoc::desc
     "@(':predicate') &mdash; default @('nil')"
     (xdoc::p
      "Selects between the two variants of this transformation:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to select the variant in which @('old')
        is treated like a predicate that recognizes
        argument tuples that are all in the old representation.")
      (xdoc::li
       "@('nil'), to select the variant in which @('old')
        is treated as a function that operates
        only on argument tuples that are all in the old representation."))
     (xdoc::p
      "In the " *isodata-design-notes* ",
       the sections with `Function' in their title
       refer to the case in which @(':predicate') is @('nil'),
       while the sections with `Predicate' in their title
       refer to the case in which @(':predicate') is @('t')."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-thm-name :never)

    (xdoc::desc-apt-input-thm-enable :never)

    (xdoc::desc-apt-input-non-executable :never)

    (xdoc::desc
     "@(':normalize') &mdash; default @('t')"
     (xdoc::p
      "Determines whether @('new') is normalized:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to normalize it.")
      (xdoc::li
       "@('nil'), to not normalize it.")))

    (xdoc::desc-apt-input-verify-guards :never)

    (xdoc::desc-apt-input-untranslate)

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print isodata)

    (xdoc::evmac-input-show-only isodata))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    isodata

    (xdoc::p
     "The following conditions must be proved
      in order for the transformation to apply.")

    (xdoc::evmac-appcond
     ":oldp-when-old"
     (xdoc::&&
      (xdoc::p
       "@('old') holds only on argument tuples
        such that @('y1'), ..., @('yp') are all in @('oldp'):")
      (xdoc::codeblock
       "(implies (old x1 ... xn)"
       "         (and (oldp y1)"
       "              ..."
       "              (oldp yp)))"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($pA$)"
     :presence "@(':predicate') is @('t')")

    (xdoc::evmac-appcond
     ":oldp-of-rec-calls"
     (xdoc::&&
      (xdoc::p
       "@('oldp') is preserved on @('y1'), ..., @('yp')
        in the recursive calls of @('old'):")
      (xdoc::codeblock
       "(implies (and (oldp y1)"
       "              ..."
       "              (oldp yp))"
       "         (and (implies context1<x1,...,xn>"
       "                       (and (oldp update1-y1<x1,...,xn>)"
       "                            ..."
       "                            (oldp update1-yp<x1,...,xn>)))"
       "              ..."
       "              (implies contextm<x1,...,xn>"
       "                       (and (oldp updatem-y1<x1,...,xn>)"
       "                            ..."
       "                            (oldp updatem-yp<x1,...,xn>)))))"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($Ad$)"
     :presence "@('old') is recursive")

    (xdoc::evmac-appcond
     ":old-guard"
     (xdoc::&&
      (xdoc::p
       "@('old') is well-defined (according to its guard)
        only on tuples in the old representation:")
      (xdoc::codeblock
       "(implies old-guard<x1,...,xn>"
       "         (and (oldp y1)"
       "              ..."
       "              (oldp yp)))"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($Gf$)"
     :presence "the generated function is guard-verified
                (which is determined by the @(':verify-guards') input;
                see above)
                and @(':predicate') is @('nil')")

    (xdoc::evmac-appcond
     ":old-guard-pred"
     (xdoc::&&
      (xdoc::p
       "@('old') is well-defined (according to its guard)
        on all tuples in the old representation:")
      (xdoc::codeblock
       "(implies (and (oldp y1)"
       "              ..."
       "              (oldp yp))"
       "         old-guard<x1,...,xn>)"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($Gp$)"
     :presence "the generated function is guard-verified
                (which is determined by the @(':verify-guards') input;
                see above)
                and @(':predicate') is @('t')")

    (xdoc::p
     "Unless @('iso') is a name,
      there are additional applicability conditions
      that pertain to @(tsee defiso).
      These additional applicability conditions are described
      in the documentation of @(tsee defiso)."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Isomorphic version of @('old'):")
     (xdoc::codeblock
      ";; when old is not recursive:"
      "(defun new (x1 ... xn)"
      "  old-body<...,(back y1),...,(back yp),...>)"
      ""
      ";; when old is recursive and the :predicate input is nil:"
      "(defun new (x1 ... xn)"
      "  (if (and (newp y1)"
      "           ..."
      "           (newp yp))"
      "      old-body<...,(back y1),...,(back yp),...,"
      "               (new ..."
      "                    (forth update1-y1<...,"
      "                                      (back y1),"
      "                                      ...,"
      "                                      (back yp),"
      "                                      ...>)"
      "                    ..."
      "                    (forth update1-yp<...,"
      "                                      (back y1),"
      "                                      ...,"
      "                                      (back yp),"
      "                                      ...>),"
      "                    ...),"
      "               ..."
      "               (new ..."
      "                    (forth updatem-y1<...,"
      "                                      (back y1),"
      "                                      ...,"
      "                                      (back yp),"
      "                                      ...>)"
      "                  ..."
      "                  (forth updatem-yp<...,"
      "                                    (back y1),"
      "                                    ...,"
      "                                    (back yp),"
      "                                    ...>),"
      "                  ...)>"
      "  nil)) ; or (mv nil ... nil)"
      ""
      ";; when old is recursive and the :predicate input is t:"
      "(defun new (x1 ... xn)"
      "  old-body<...,(back y1),...,(back yp),...,"
      "           (new ..."
      "                (forth update1-y1<...,"
      "                                  (back y1),"
      "                                  ...,"
      "                                  (back yp),"
      "                                  ...>)"
      "                ..."
      "                (forth update1-yp<...,"
      "                                  (back y1),"
      "                                  ...,"
      "                                  (back yp),"
      "                                  ...>),"
      "                ...),"
      "           ..."
      "           (new ..."
      "                (forth updatem-y1<...,"
      "                                  (back y1),"
      "                                  ...,"
      "                                  (back yp),"
      "                                  ...>)"
      "                ..."
      "                (forth updatem-yp<...,"
      "                                  (back y1),"
      "                                  ...,"
      "                                  (back yp),"
      "                                  ...>),"
      "                ...)>)")
     (xdoc::p
      "Note that:")
     (xdoc::ul
      (xdoc::li
       (xdoc::p
        "When @(':predicate') is @('nil'),
         @('new') is defined to map
         each argument tuple in the new representation
         to the same value that @('old') maps
         the isomorphic argument tuple in the old representation.
         The following is a theorem:")
       (xdoc::codeblock
        "(implies (and (newp y1)"
        "              ..."
        "              (newp yp))"
        "         (equal (new x1 ... xn)"
        "                (old ... (back y1 ... (back yp) ...))))"))
      (xdoc::li
       (xdoc::p
        "When @(':predicate') is @('t'),
         @('new') is defined to hold exactly
         on the argument tuples in the new representation
         that are isomorphic the argument tuples in the old representation
         on which @('old') holds.
         The following is a theorem:")
       (xdoc::codeblock
        "(equal (new x1 ... xn)"
        "       (and (newp y1)"
        "            ..."
        "            (newp yp)"
        "            (old ... (back y1) ... (back yp) ...)))")))
     (xdoc::p
      "If @('old') is recursive,
       the measure term of @('new') is
       @('measure<...,(back y1),...,(back yp),...>')
       and the well-founded relation of @('new') is
       the same as @('old').")
     (xdoc::p
      "When @(':predicate') is @('t'),
       the guard of @('new') consists of the argument tuples
       in the new representation:")
     (xdoc::codeblock
      "(and (newp y1) ... (newp yp))")
     (xdoc::p
      "When @(':predicate') is @('nil'),
       the guard of @('new') consists of the argument tuples
       that are isomorphic to the ones in the guard of @('old'):")
     (xdoc::codeblock
      "(and (newp y1) ... (newp yp)"
      "     old-guard<...,(back y1),...,(back yp),...>)")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('new') is denoted by
       @($f'$) when @(':predicate') is @('nil'),
       and @($p'$) when @(':predicate') is @('t')."))

    (xdoc::desc
     "@('old-to-new')"
     (xdoc::p
      "Theorem that relates @('old') to @('new'):")
     (xdoc::codeblock
      ";; when the :predicate input is nil:"
      "(defthm old-to-new"
      "  (implies (and (oldp y1)"
      "                ..."
      "                (oldp yp))"
      "           (equal (old x1 ... xn)"
      "                  (new ... (forth y1) ... (forth yp) ...))))"
      ""
      ";; whem the :predicate input is t:"
      "(defthm old-to-new"
      "  (equal (old x1 ... xn)"
      "         (and (oldp y1)"
      "              ..."
      "              (oldp yp)"
      "              (new ... (forth y1) ... (forth yp) ...))))")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('old-to-new') is denoted by
       @($ff'$) when @(':predicate') is @('nil'),
       and @($pp'$) when @(':predicate') is @('t').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy isodata)))
