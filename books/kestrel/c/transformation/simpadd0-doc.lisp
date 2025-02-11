; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc simpadd0

  :parents (transformation-tools)

  :short "A simple transformation to simplify @('E + 0') to @('E')."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is a very simple proof-of-concept transformation,
      which replaces expressions of the form @('E + 0') with @('E').
      Due to C's arithmetic conversions, it is not immediately clear whether
      this transformation always preserves code equivalence,
      but for now we are not concerned about this,
      as the goal of this proof-of-concept transformation
      is just to show a plausible example of C-to-C transformation;
      and there are certainly many cases (perhaps all cases) in which
      this transformation is indeed equivalence-preserving."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(simpadd0 const-old"
     "          const-new"
     "          :proofs ...  ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('const-old')"
     (xdoc::p
      "Specifies the code to the transformed.")
     (xdoc::p
      "This must be a symbol that names an existing ACL2 constant
       that contains a  validated translation unit ensemble,
       i.e. a value of type @(tsee transunit-ensemble)
       resulting from "
      (xdoc::seetopic "c$::validator" "validation")
      ", and in particular containing "
      (xdoc::seetopic "c$::validation-information" "validation information")
      ". This constant could result from @(tsee c$::input-files),
       or from some other "
      (xdoc::seetopic "transformation-tools" "transformation")
      ".")
     (xdoc::p
      "In the rest of this documentation page,
       we refer to this constant as @('*old*')."))

    (xdoc::p
     "@('const-new')"
     (xdoc::p
      "Specifies the name of the constant for the transformed code.")
     (xdoc::p
      "This must be a symbol that is valid name for a new ACL2 constant.")
     (xdoc::p
      "In the rest of this documentation page,
       we refer to this constant as @('*new*')."))

    (xdoc::p
     "@(':proofs') &mdash; default @('nil')"
     (xdoc::p
      "Specifies whether proofs of correctness should be generated or not.")
     (xdoc::p
      "This is a very preliminary proof-of-concept capability.
       It works only on very restricted forms of the code.
       This is why, for now, it is turned off by default.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('*new*')"
     (xdoc::p
      "The named constant containing the result of the transformation.
       This is a translation unit ensemble that is
       the same as the one in @('*old*'), except that:")
     (xdoc::ul
      (xdoc::li
       "Every occurrence of an expression of the form @('<E> + 0'),
        where @('<E>') is an expression
        and @('0') is the octal constant for zero
        without other leading zeros and without suffixes,
        into just the expression @('<E>').")
      (xdoc::li
       "Each file path @('<file>.<ext>') in @('*old*')
        is turned into @('<file>.simpadd0.<ext>'),
        if the path has a dot, and where @('<ext>') had no dots;
        if the path is @('<file>') without dots,
        it is turned into @('<file>.simpadd').")))

    (xdoc::desc
     "Equivalence theorems."
     (xdoc::p
      "These are generated only if @(':proofs') is @('t').")
     (xdoc::p
      "One theorem is generated for every function definition in @('*old*').")
     (xdoc::p
      "If @('<f>') is the name of a defined function in @('*old*'),
       the generated theorem has the form")
     (xdoc::codeblock
      "(defruled |<f>|-equivalence"
      "  (equal (c::exec-fun (c::ident \"<f>\")"
      "                      nil"
      "                      compst"
      "                      (c::init-fun-env"
      "                       (mv-nth"
      "                        1"
      "                        (c$::ldm-transunit"
      "                         (omap::lookup"
      "                          <path> (transunit-ensemble->unwrap *old*)))))"
      "                      1000)"
      "         (c::exec-fun (c::ident ,string)"
      "                      nil"
      "                      compst"
      "                      (c::init-fun-env"
      "                       (mv-nth"
      "                        1"
      "                        (c$::ldm-transunit"
      "                         (omap::lookup"
      "                          <path> (transunit-ensemble->unwrap *new*)))))"
      "                      1000)))")
     (xdoc::p
      "where:")
     (xdoc::ul
      (xdoc::li
       "@(tsee c::exec-fun) is part of our dynamic semantics for C.")
      (xdoc::li
       "The @('nil') passed as second argument to @(tsee c::exec-fun)
        signifies that we only generate proofs
        for C functions that take no arguments.
        (As noted above, this proof generation capability is very preliminary.")
      (xdoc::li
       "@('<path>') is the path of the translation unit that defines @('<f>').")
      (xdoc::li
       "@(tsee c$::ldm-transunit) is part of the mapping from "
       (xdoc::seetopic "c$::syntax-for-tools" "our abstract syntax for tools")
       " to the "
       (xdoc::seetopic "c::abstract-syntax"
                       "the abstract syntax of our C formalization")
       ". This is a partial mapping,
        because our C formalization only covers a subset of C.
        If any of the translation units in @('*old*')
        falls outside the domain of the mapping,
        the @('simpadd0') transformation fails,
        because proofs cannot be generated;
        in this case, the transformation must be run with @(':proofs nil').")
      (xdoc::li
       "The @('1000') passed to @(tsee c::exec-fun) is just an arbitrary limit,
        for this very preliminary proof generation capability."))
     (xdoc::p
      "Any of these generated theorems may actually fail to prove.
       Currently @('simpadd0') does not generate robust proofs,
       and does not make thorough checks to provide
       user-friendly error messages if proof generation is not possible.")))))
