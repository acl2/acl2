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

; (depends-on "design-notes/isodata.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *isodata-design-notes*
  (xdoc::&& "@('isodata') "
            (xdoc::ahref "res/kestrel-apt-design-notes/isodata.pdf"
                         "design notes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc isodata

  :parents (apt)

  :short "APT isomorphic data transformation:
          change function arguments and results
          into isomorphic representations."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This transformation changes the representation of
      one or more of a function's arguments and results
      into an isomorphic representation.
      This transformation is useful
      to carry out certain data type refinements
      (when synthesizing programs),
      or to raise the level of abstraction of certain types
      (when analyzing programs).")

    (xdoc::p
     "When at least one argument's representation is being changed,
      then by regarding the arguments whose representation is not changed
      as being changed via an indentity isomorphism,
      we can say that this transformation changes the representation of
      (the tuple of) all the function's arguments
      into a new representation that consists of
      (the tuple of) all the new function's arguments.
      In this case, there are two variants of this transformation:")
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
       at least all the tuples in the old representation (and possibly more)
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
     "If only the representation of some results (and of no arguments)
      is changed, then there is a single variant of this transformation,
      namely one that operates on the same tuples as the old function
      but returns isomorphic results in the new representation.")

    (xdoc::p
     "These " *isodata-design-notes* ", which use "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
     ", provide the mathematical concepts and template proofs
      upon which this transformation is based.
      These notes should be read alongside this reference documentation,
      which refers to the them in numerous places.")

    (xdoc::p
     "The " *isodata-design-notes* " cover
      isomorphic transformations compositionally established
      by partitioning arguments and results of old and new function
      and by establishing sub-mappings between the partitions
      (see the `Compositional Establishment of Isomorphic Mappings on Tuples'
      section in the design notes).
      The current implementation is more limited,
      supporting only a limited form of partition of the arguments (see below).
      There are plans to extend the implementation
      to match the coverage of the design notes,
      namely allowing arbitrary partitions of arguments and results."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(isodata old"
     "         isomaps"
     "         :predicate           ; default nil"
     "         :new-name            ; default :auto"
     "         :new-enable          ; default :auto"
     "         :old-to-new-name     ; default from table"
     "         :old-to-new-enable   ; default from table"
     "         :new-to-old-name     ; default from table"
     "         :new-to-old-enable   ; default from table"
     "         :newp-of-new-name    ; default :auto"
     "         :newp-of-new-enable  ; default t"
     "         :verify-guards       ; default :auto"
     "         :untranslate         ; default :nice"
     "         :hints               ; default nil"
     "         :print               ; default :result"
     "         :show-only           ; default nil"
     "         :compatibility       ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must
       be in logic mode,
       be " (xdoc::seetopic "acl2::function-definedness" "defined") ", and
       have no input or output "
      (xdoc::seetopic "acl2::stobj" "stobjs")
      ". If the @(':predicate') input (see below) is @('t'),
       then @('old') must return
       a non-" (xdoc::seetopic "mv" "multiple") " value.
       If @('old') is recursive, it must
       be singly (not mutually) recursive,
       not have a @(':?') measure, and
       not occur in its own "
      (xdoc::seetopic "tthm" "termination theorem")
      " (i.e. not occur in the tests and arguments of its own recursive calls).
       If the @(':verify-guards') input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "In the rest of this documentation page:")
     (xdoc::ul
      (xdoc::li
       "Let @('x1'), ..., @('xn') be the arguments of @('old'),
        where @('n') &gt; 0.")
      (xdoc::li
       "Let @('m') &gt; 0 be the number of results of @('old').")
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
                   (old updater-x1<x1,...,xn>
                        ...
                        updater-xn<x1,...,xn>)>
        })
        be the body of @('old'),
        where @('r') &gt; 0 is the number of recursive calls
        in the body of @('old')
        and each @('updatek-xi<x1,...,xn>') is
        the @('i')-th actual argument passed to the @('k')-th recursive call.
        Furthermore,
        let @('contextk<x1,...,xn>') be the context (i.e. controlling tests)
        in which the @('k')-th recursive call occurs,
        and let @('measure<x1,...,xn>') be the measure term of @('old')."))
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('old') is denoted by
       @($f$) when @(':predicate') is @('nil'),
       and @($p$) when @(':predicate') is @('t')."))

    (xdoc::desc
     "@('isomaps')"
     (xdoc::p
      "Specifies the arguments and results of @('old') that are transformed
       and the way in which they are transformed.")
     (xdoc::p
      "It must be a non-empty list of doublets
       @('((arg/res-list1 iso1) ... (arg/res-listq isoq))'),
       where:")
     (xdoc::ul
      (xdoc::li
       (xdoc::p
        "Each @('arg/res-listk') denotes
         the subset of the arguments and results of @('old')
         whose representation is transformed according to @('isok').")
       (xdoc::p
        "It must be one of the following:")
       (xdoc::ul
        (xdoc::li
         "A non-empty list without duplicates of elements among
          @('x1'), ... @('xn'), @(':result1'), ..., @(':resultm'),
          in any order.")
        (xdoc::li
         "A single element among
          @('x1'), ... @('xn'), @(':result1'), ..., @(':resultm'),
          abbreviating the singleton list with that element.")
        (xdoc::li
         "The single element @(':result'),
          abbreviating the singleton list @(':result1').
          This is allowed only if @('m') is 1.")))
      (xdoc::li
       (xdoc::p
        "Each @('isok') denotes the isomorphic mapping
         to apply to the arguments and results in @('arg/res-listk').
         Each @('isok') specifies
         old and new representations
         and the conversions between them.")
       (xdoc::p
        "It must be one of the following:")
       (xdoc::ul
        (xdoc::li
         "A symbol that references
          a previous successful call of @(tsee defiso),
          i.e. the symbol must be the @('name') input of that call.
          The domains and conversions recorded under that name specify:
          the recognizer of the old representation (@('doma')),
          which we call @('oldp') here;
          the recognizer of the new representation (@('domb')),
          which we call @('newp') here;
          the conversion from the old to the new representation (@('alpha')),
          which we call @('forth') here; and
          the conversion from the new to the old representation (@('beta')),
          which we call @('back') here.
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
          after the call of @('isodata').")))
      (xdoc::li
       (xdoc::p
        "The lists @('arg/res-list1'), ..., @('arg/res-listq')
         are pairwise disjoint,
         i.e. each @('xi') and @(':result') appears
         in at most one of those lists.")))
     (xdoc::p
      "In the rest of this documentation page,
       for each @('i') from 1 to @('n'),
       let @('oldpi'), @('newpi'), @('forthi'), and @('backi') be:")
     (xdoc::ul
      (xdoc::li
       "The @('oldp'), @('newp'), @('forth'), and @('back')
        of the (pre-existing or locally generated) @(tsee defiso)
        specified by @('isok'),
        if @('xi') is in @('arg/res-listk').")
      (xdoc::li
       "The functions
        @('(lambda (x) t)'),
        @('(lambda (x) t)'),
        @('(lambda (x) x)'), and
        @('(lambda (x) x)')
        that form the identity isomorphic mapping over all values,
        if @('xi') is not in any @('arg/res-listk')."))
     (xdoc::p
      "Furthermore,
       for each @('j') from 1 to @('m'),
       let @('oldp_rj'), @('newp_rj'), @('forth_rj'), and @('back_rj') be:")
     (xdoc::ul
      (xdoc::li
       "The @('oldp'), @('newp'), @('forth'), and @('back')
        of the (pre-existing or locally generated) @(tsee defiso)
        specified by @('isok'),
        if @(':resultj') is in @('arg/res-listk').")
      (xdoc::li
       "The functions
        @('(lambda (x) t)'),
        @('(lambda (x) t)'),
        @('(lambda (x) x)'), and
        @('(lambda (x) x)')
        that form the identity isomorphic mapping over all values,
        if @(':resultj') is not in any @('arg/res-listk')."))
     (xdoc::p
      "In the " *isodata-design-notes* ", the section
       `Compositional Establishment of Isomorphic Mappings on Tuples'
       describes the compositional establishment of an isomorphic mapping
       between the inputs of old and new function.
       The @('isomaps') input currently supported by this transformation
       amounts to the following partitioning and sub-mappings:")
     (xdoc::ul
      (xdoc::li
       "The new function's arguments are the same (i.e. have the same names)
        as the old function's arguments, i.e. @('x1'), ..., @('xn').")
      (xdoc::li
       "The new function has the same number of results as the old function.")
      (xdoc::li
       "The arguments are partitioned into @('n') singleton partitions.")
      (xdoc::li
       "The results are partitioned into @('m') singleton partitions.")
      (xdoc::li
       "The isomorphic mapping consisting of
        @('oldpi'), @('newpi'), @('forthi'), and @('backi')
        is used for the partition consisting of argument @('xi').")
      (xdoc::li
       "The isomorphic mapping consisting of
        @('oldp_rj'), @('newp_rj'), @('forth_rj'), and @('back_rj')
        is used for the partition consisting of result @('j').")
      (xdoc::li
       "The identity isomorphic mapping
        is used for the partitions of all the results,
        if @(':result') is not in any @('arg/res-listk')."))
     (xdoc::p
      "In the design notes,
       the resulting isomorphic mapping over all function arguments
       is denoted as consisting of
       the domains @($A$) and @($A'$) and
       the conversions @($\\alpha$) and @($\\alpha'$),
       and the resulting isomorphic mapping over all function results
       is denoted as consisting of
       the domains @($B$) and @($B'$) and
       the conversions @($\\beta$) and @($\\beta'$)."))

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
      "This input may be @('t') only if @('isomaps')
       does not include @(':result').")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       the sections with `Function' in their title
       refer to the case in which @(':predicate') is @('nil'),
       while the sections with `Predicate' in their title
       refer to the case in which @(':predicate') is @('t')."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-old-to-new-name)

    (xdoc::desc-apt-input-old-to-new-enable)

    (xdoc::desc-apt-input-new-to-old-name)

    (xdoc::desc-apt-input-new-to-old-enable)

    (xdoc::desc
     "@(':newp-of-new-name') &mdash; default @(':auto')"
     (xdoc::p
      "Determines the name of the theorem asserting that @('new') maps
       arguments in the new representation
       to results in the new representation.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the concatenation of
        the name of @('new') followed by @('-new-representation'),
        in the same package as @('new').")
      (xdoc::li
       "Any other symbol, to use as the name of the theorem."))
     (xdoc::p
      "This input may be present only if
       @('isomaps') includes some @(':resultj').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('newp-of-new') be the name of this theorem."))

    (xdoc::desc
     "@(':newp-of-new-enable') &mdash; default @('t')"
     (xdoc::p
      "Determines whether @('newp-of-new') is enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable the theorem.")
      (xdoc::li
       "@('nil'), to disable the theorem."))
     (xdoc::p
      "This input may be present only if
       @('isomaps') includes some @(':resultj')."))

    (xdoc::desc-apt-input-verify-guards :plural-functions nil)

    (xdoc::desc-apt-input-untranslate)

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print isodata)

    (xdoc::evmac-input-show-only isodata)

    (xdoc::desc
     "@(':compatibility') &mdash; default @('nil')"
     (xdoc::p
      "This is a temporary option that is not documented
       because it should not be used,
       except in very specific transitional situations.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    isodata

    (xdoc::p
     "The following conditions must be proved
      in order for the transformation to apply.")

    (xdoc::evmac-appcond
     ":oldp-of-old"
     (xdoc::&&
      (xdoc::p
       "@('old') maps arguments in the old representation
        to results in the old representation:")
      (xdoc::codeblock
       ";; when m = 1:"
       "(implies (and (oldp1 x1)"
       "              ..."
       "              (oldpn xn))"
       "         (oldp_r1 (old x1 ... xn)))"
       ""
       ";; when m > 1:"
       "(implies (and (oldp1 x1)"
       "              ..."
       "              (oldpn xn))"
       "         (mv-let (y1 ... ym)"
       "           (old x1 ... xn)"
       "           (and (oldp_r1 y1)"
       "                ..."
       "                (oldp_rm ym))))"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($fAB$)"
     :presence "@('isomaps') includes some @(':resultj')")

    (xdoc::evmac-appcond
     ":oldp-when-old"
     (xdoc::&&
      (xdoc::p
       "@('old') holds only on argument tuples
        such that @('x1'), ..., @('xn') are all in the old representation:")
      (xdoc::codeblock
       "(implies (old x1 ... xn)"
       "         (and (oldp1 x1)"
       "              ..."
       "              (oldpn xn)))"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($pA$)"
     :presence "@(':predicate') is @('t')")

    (xdoc::evmac-appcond
     ":oldp-of-rec-call-args"
     (xdoc::&&
      (xdoc::p
       "The old representation is preserved on
        the arguments of the recursive calls of @('old'):")
      (xdoc::codeblock
       "(implies (and (oldp1 x1)"
       "              ..."
       "              (oldpn xn))"
       "         (and (implies context1<x1,...,xn>"
       "                       (and (oldp1 update1-x1<x1,...,xn>)"
       "                            ..."
       "                            (oldpn update1-xn<x1,...,xn>)))"
       "              ..."
       "              (implies contextr<x1,...,xn>"
       "                       (and (oldp1 updater-x1<x1,...,xn>)"
       "                            ..."
       "                            (oldpn updater-xp<x1,...,xn>)))))"))
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
       "         (and (oldp1 x1)"
       "              ..."
       "              (oldpn xn)))"))
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
       "(implies (and (oldp1 x1)"
       "              ..."
       "              (oldpn xn))"
       "         old-guard<x1,...,xn>)"))
     :design-notes *isodata-design-notes*
     :design-notes-appcond "@($Gp$)"
     :presence "the generated function is guard-verified
                (which is determined by the @(':verify-guards') input;
                see above)
                and @(':predicate') is @('t')")

    (xdoc::p
     "Unless @('iso1'), ..., @('isoq')
      are all names of pre-existing @(tsee defiso)s,
      there are additional applicability conditions
      that pertain to the locally generated @(tsee defiso)s.
      These additional applicability conditions are described
      in the documentation of @(tsee defiso)."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Isomorphic version of @('old'):")
     (xdoc::codeblock
      ";; when old is not recursive"
      ";; and :predicate is t:"
      "(defun new (x1 ... xn)"
      "  (and (mbt$ (and (newp1 x1)"
      "                  ..."
      "                  (newpn xn)))"
      "       old-body<(back1 x1),...,(backn xn)>))"
      ""
      ";; when old is not recursive,"
      ";; :predicate is nil:"
      ";; and isomaps includes no :resultj:"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ (and (newp1 x1)"
      "                 ..."
      "                 (newpn xn)))"
      "      old-body<(back1 x1),...,(backn xn)>"
      "    nil)) ; or (mv nil ... nil)"
      ""
      ";; when old is not recursive,"
      ";; :predicate is nil,"
      ";; m = 1,"
      ";; and isomaps includes :result1 (or :result):"
      ""
      "(defun new (x1 ... xn)"
      "  (if (mbt$ (and (newp1 x1)"
      "                 ..."
      "                 (newpn xn)))"
      "      (forth_r1 old-body<(back1 x1),...,(backn xn)>)"
      "    nil))"
      ""
      ";; when old is not recursive,"
      ";; :predicate is nil,"
      ";; m > 1,"
      ";; and isomaps includes some :resultj:"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ (and (newp1 x1)"
      "                 ..."
      "                 (newpn xn)))"
      "      (mv-let (y1 ... ym)"
      "        old-body<(back1 x1),...,(backn xn)>"
      "        (mv (forth_r1 y1) ... (forth_rm ym)))"
      "    (mv nil ... nil)))"
      ""
      ";; when old is recursive"
      ";; and :predicate is t:"
      "(defun new (x1 ... xn)"
      "  (and (mbt$ (and (newp1 x1)"
      "                  ..."
      "                  (newpn xn)))"
      "       old-body<(back1 x1),...,(backn xn),"
      "                (new (forth1 update1-x1<(back1 x1),"
      "                                        ...,"
      "                                        (backn xn)>)"
      "                     ..."
      "                     (forthn update1-xn<(back1 x1),"
      "                                        ...,"
      "                                        (backn xn)>)),"
      "                ..."
      "                (new (forth1 updater-x1<(back1 x1),"
      "                                        ...,"
      "                                        (backn xn)>)"
      "                     ..."
      "                     (forthn updater-xn<(back1 x1),"
      "                                        ...,"
      "                                        (backn xn)>))>))"
      ""
      ";; when old is recursive,"
      ";; :predicate is nil,"
      ";; and isomaps includes no :resultj:"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ (and (newp1 x1)"
      "                 ..."
      "                 (newpn xn)))"
      "      old-body<(back1 x1),...,(backn xn),"
      "               (new (forth1 update1-x1<(back1 x1),"
      "                                       ...,"
      "                                       (backn xn)>)"
      "                    ..."
      "                    (forthn update1-xn<(back1 x1),"
      "                                       ...,"
      "                                       (backn xn)>)),"
      "               ..."
      "               (new (forth1 updater-x1<(back1 x1),"
      "                                       ...,"
      "                                       (backn xn)>)"
      "                    ..."
      "                    (forthn updater-xn<(back1 x1),"
      "                                       ...,"
      "                                       (backn xn)>))>"
      "    nil)) ; or (mv nil ... nil)"
      ""
      ";; when old is recursive,"
      ";; :predicate is nil,"
      ";; m = 1,"
      ";; and isomaps include :result1 (or :result):"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ (and (newp1 x1)"
      "                 ..."
      "                 (newpn xn)))"
      "      (forth_r1 old-body<(back1 x1),...,(backn xn),"
      "                         (back_r1"
      "                          (new (forth1 update1-x1<(back1 x1),"
      "                                                  ...,"
      "                                                  (backn xn)>)"
      "                               ..."
      "                               (forthn update1-xn<(back1 x1),"
      "                                                  ...,"
      "                                                  (backn xn)>))),"
      "                         ..."
      "                         (back_r1"
      "                          (new (forth1 updater-x1<(back1 x1),"
      "                                                  ...,"
      "                                                  (backn xn)>)"
      "                               ..."
      "                               (forthn updater-xn<(back1 x1),"
      "                                                  ...,"
      "                                                  (backn xn)>)))>)"
      "    nil))"
      ""
      ";; when old is recursive,"
      ";; :predicate is nil,"
      ";; m > 1,"
      ";; and isomaps includes some :resultj:"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ (and (newp1 x1)"
      "                 ..."
      "                 (newpn xn)))"
      "      (mv-let (y1 ... ym)"
      "        old-body<(back1 x1),...,(backn xn),"
      "                 (mv-let (y1 ... ym)"
      "                   (new (forth1 update1-x1<(back1 x1),"
      "                                           ...,"
      "                                           (backn xn)>)"
      "                        ..."
      "                        (forthn update1-xn<(back1 x1),"
      "                                           ...,"
      "                                           (backn xn)>))"
      "                   (mv (forth_r1 y1) ... (forth_rm ym))),"
      "                 ..."
      "                 (mv-let (y1 ... ym)"
      "                   (new (forth1 updater-x1<(back1 x1),"
      "                                           ...,"
      "                                           (backn xn)>)"
      "                        ..."
      "                        (forthn updater-xn<(back1 x1),"
      "                                           ...,"
      "                                           (backn xn)>))"
      "                   (mv (forth_r1 y1) ... (forth_rm ym)))>"
      "        (mv (forth_r1 y1) ... (forth_rm ym)))"
      "    (mv nil ... nil)))")
     (xdoc::p
      "If @('old') is recursive,
       the measure term of @('new') is
       @('measure<(back1 x1),...,(backn xn)>')
       and the well-founded relation of @('new') is
       the same as @('old').")
     (xdoc::p
      "The guard of @('new') is:")
     (xdoc::codeblock
      ";; when :predicate is nil:"
      "(and (newp1 x1)"
      "     ..."
      "     (newpn xn)"
      "     old-guard<(back1 x1),...,(backn xn)>)"
      ""
      ";; when :predicate is t:"
      "(and (newp1 x1)"
      "     ..."
      "     (newpn xn))")
     (xdoc::p
      "That is, when @(':predicate') is @('t')
       the guard consists of the new representation;
       when @(':predicate') is @('nil'),
       the guard consists of the argument tuples
       that are isomorphic to the ones in the guard of @('old').")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('new') is denoted by
       @($f'$) when @(':predicate') is @('nil'),
       and @($p'$) when @(':predicate') is @('t').")
     (xdoc::p
      "Note that:")
     (xdoc::ul
      (xdoc::li
       "When @(':predicate') is @('t'),
        @('new') is defined to hold exactly
        on the argument tuples in the new representation
        that are isomorphic the argument tuples in the old representation
        on which @('old') holds.")
      (xdoc::li
       "When @(':predicate') is @('nil'),
        @('new') is defined to map
        each argument tuple in the new representation
        to the same or isomorphic value that @('old') maps
        the isomorphic argument tuple in the old representation.")))

    (xdoc::desc
     "@('new-to-old')"
     (xdoc::p
      "Theorem that relates @('new') to @('old'):")
     (xdoc::codeblock
      ";; when :predicate is t:"
      "(defthm new-to-old"
      "  (implies (and (newp1 x1)"
      "                ..."
      "                (newpn xn))"
      "           (equal (new x1 ... xn)"
      "                  (old (back1 x1) ... (backn xn)))))"
      ""
      ";; when :predicate is nil"
      ";; and isomaps includes no :resultj:"
      "(implies (and (newp1 x1)"
      "              ..."
      "              (newpn xn))"
      "         (equal (new x1 ... xn)"
      "                (old (back1 x1) ... (backn xn))))"
      ""
      ";; when :predicate is nil,"
      ";; m = 1,"
      ";; and isomaps includes :result1 (or :result):"
      "(implies (and (newp1 x1)"
      "              ..."
      "              (newp1 xn))"
      "         (equal (new x1 ... xn)"
      "                (forth_r1 (old (back1 x1) ... (backn xn)))))"
      ""
      ";; when :predicate is nil,"
      ";; m > 1,"
      ";; and isomaps includes some :resultj:"
      "(implies (and (newp1 x1)"
      "              ..."
      "              (newp1 xn))"
      "         (and (equal (mv-nth 0 (new x1 ... xn))"
      "                     (forth_r1 (mv-nth 0 (old (back1 x1)"
      "                                              ..."
      "                                              (backn xn)))))"
      "              ..."
      "              (equal (mv-nth m-1 (new x1 ... xn))"
      "                     (forth_rm (mv-nth m-1 (old (back1 x1)"
      "                                                ..."
      "                                                (backn xn)))))))")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('new-to-old') is denoted by
       @($f'f$) when @(':predicate') is @('nil'),
       and @($'pp$) when @(':predicate') is @('t')."))

    (xdoc::desc
     "@('old-to-new')"
     (xdoc::p
      "Theorem that relates @('old') to @('new'):")
     (xdoc::codeblock
      ";; when :predicate is t:"
      "(defthm old-to-new"
      "  (implies (and (oldp1 x1)"
      "                ..."
      "                (oldpn xn))"
      "           (equal (old x1 ... xn)"
      "                  (new (forth1 x1) ... (forthn xn)))))"
      ""
      ";; when :predicate is nil"
      ";; and isomaps includes no :resultj:"
      "(defthm old-to-new"
      "  (implies (and (oldp1 x1)"
      "                ..."
      "                (oldpn xn))"
      "           (equal (old x1 ... xn)"
      "                  (new (forth1 x1) ... (forthn xn)))))"
      ""
      ";; when :predicate is nil,"
      ";; m = 1,"
      ";; and isomaps includes :result1 (or :result):"
      "(defthm old-to-new"
      "  (implies (and (oldp1 x1)"
      "                ..."
      "                (oldpn xn))"
      "           (equal (old x1 ... xn)"
      "                  (back_r1 (new (forth1 x1) ... (forthn xn))))))"
      ""
      ";; when :predicate is nil,"
      ";; m > 1,"
      ";; and isomaps includes some :resultj:"
      "(defthm old-to-new"
      "  (implies (and (oldp1 x1)"
      "                ..."
      "                (oldpn xn))"
      "           (and (equal (mv-nth 0 (old x1 ... xn))"
      "                       (back_r1 (mv-nth 0 (new (forth1 x1)"
      "                                               ..."
      "                                               (forthn xn)))))"
      "                ..."
      "                (equal (mv-nth m-1 (old x1 ... xn))"
      "                       (back_rm (mv-nth m-1 (new (forth1 x1)"
      "                                                 ..."
      "                                                 (forthn xn))))))))")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('old-to-new') is denoted by
       @($ff'$) when @(':predicate') is @('nil'),
       and @($pp'$) when @(':predicate') is @('t')."))

    (xdoc::desc
     "@('newp-of-new')"
     (xdoc::p
      "Theorem asserting that @('new') maps
       arguments in the new representation
       to results in the new representation:")
     (xdoc::codeblock
      ";; when m = 1:"
      "(defthm newp-of-new"
      "  (implies (and (newp1 x1)"
      "                ..."
      "                (newpn xn))"
      "           (newp_r1 (new x1 ... xn))))"
      ""
      ";; when m > 1:"
      "(defthm newp-of-new"
      "  (implies (and (newp1 x1)"
      "                ..."
      "                (newpn xn))"
      "           (mv-let (y1 ... ym)"
      "             (new x1 ... xn)"
      "             (and (newp_r1 y1)"
      "                  ..."
      "                  (newp_rm ym)))))")
     (xdoc::p
      "In the " *isodata-design-notes* ",
       @('newp-of-new') is denoted by @($f'A'B'$).")
     (xdoc::p
      "This is generated if and only if
       @('isomaps') includes some @(':resultj')."))

    (xdoc::p
     "A theory invariant is also generated to prevent
      both @('new-to-old') and @('old-to-new')
      from being enabled at the same time."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy isodata)))
