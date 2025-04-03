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

  :short "A transformation to simplify @('E + 0') to @('E')."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is a simple proof-of-concept transformation,
      which replaces expressions of the form @('E + 0') with @('E'),
      when @('E') is an expression that our current @(see validator)
      annotates as having type @('int'),
      and @('0') is the octal constant for zero
      without other leading zeros and without suffixes.")
    (xdoc::p
     "The transformation also generates proofs of equivalence
      between old (original) and new (transformed) constructs,
      for a subset of the constructs.
      In particular, the transformation generates equivalence proofs
      for C functions of a certain form, detailed below."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(simpadd0 const-old"
     "          const-new"
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
       we refer to this constant as @('*new*').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('*new*')"
     (xdoc::p
      "The named constant containing the result of the transformation.
       This is a translation unit ensemble that is
       the same as the one in @('*old*'), except that
       every occurrence of an expression of the form @('E + 0'),
       when @('E') is an expression that our current @(see validator)
       annotates as having type @('int'),
       and @('0') is the octal constant for zero
       without other leading zeros and without suffixes,
       is turned into just the expression @('E').")
     (xdoc::p
      "The file paths that are the keys of translation unit map
       are unchanged by the transformation."))

    (xdoc::desc
     "Equivalence theorems."
     (xdoc::p
      "One theorem is generated for every function definition in @('*old*')
       that has all @('int') parameters and
       whose body consists of a single @('return') statement
       with an expression consisting of
       @('int') constants,
       function parameters,
       the unary operators that do not involve pointers
       (i.e. @('+'), @('-'), @('~'), @('!')),
       and the binary operators that are pure and strict
       (i.e. @('*'), @('/'), @('%'), @('+'), @('-'), @('<<'), @('>>'),
       @('<'), @('>'), @('<='), @('>='), @('=='), @('!='),
       @('&'), @('^'), @('|')).
       Note that the transformed function definition in @('*new*')
       satisfies the same restrictions.")
     (xdoc::p
      "These theorems are proved by proving a sequence of theorems,
       in a bottom-up fashion, for the sub-constructs of the functions.
       Theorems for sub-constructs in the supported subset of C
       are also generated for functions that are not in the subset.")
     (xdoc::p
      "The generated theorems are designed to always prove.
       It is a bug in the transformation
       if a generated theorem fails to prove.")
     (xdoc::p
      "The generated theorems have names of the form @('*new*-thm-<i>'),
       where @('<i>') are increasing positive integers.")))))
