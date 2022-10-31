; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defdefparse

  :parents (abnf)

  :short "Generator of tools to generate parsing functions."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro generates customized versions of "
     (xdoc::seetopic "parser-generators" "the @('def-parse-...') tools")
     ". Those tools ``hardwire'' assumptions such as
      the name of the constant that contains the grammar,
      which prevents the coexistence of
      parsing functions generated for two or more grammars
      using those tools.")

    (xdoc::p
     "The problem could be overcome by having the @('def-parse-...') tools
      take additional inputs, such as the name of the grammar constant.
      However, this approach would make the use of those tools more verbose.")

    (xdoc::p
     "Thus, we overcome the problem in a different way.
      We introduce this @('defdefparse') macro that
      takes as inputs the name of the grammar constant and other information,
      and generates specialized versions of the @('def-parse-...') tools.
      This can be regarded as a meta macro,
      because it is a macro that generates other macro,
      or as a parser generator generator,
      in the sense that it generates tools for parser generation
      (although the tools do not yet form a full parser generator
      in the commonly used sense of the word).")

    (xdoc::p
     "We plan to remove the @('def-parse-...') tools,
      i.e. the ones that hardwire the assumptions,
      because they (more precisely, specialized versions of them)
      can be generated via @('defdefparse').")

    (xdoc::p
     "Currently the implementation of this macro does not perform
      very thorough input validation.
      This will be improved in the future."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defdefparse name"
     "             :package ..."
     "             :grammar ..."
     "             :prefix ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name of the generated parsing generation tools.")
     (xdoc::p
      "It must be a symbol,
       different from the ones in other @('defdefparse') calls.")
     (xdoc::p
      "This symbol is inserted into the names of the generated macros,
       which have the form @('defparse-name-...').
       Thus, this name is used to differentiate different sets of macros,
       typically generated for different grammars."))

    (xdoc::desc
     "@(':package') &mdash; no default"
     (xdoc::p
      "Package where the generated macros are put.")
     (xdoc::p
      "It must a string that is the name of an existing package.")
     (xdoc::p
      "If @('\"P\"') is the package name,
       the generated macros have names of the form @('p::defparse-name-...')."))

    (xdoc::desc
     "@(':grammar') &mdash; no default"
     (xdoc::p
      "Grammar for which parsing functions are generated
       by the generated @('defparse-name-...') macros.")
     (xdoc::p
      "It must be the name of an existing constant
       that contains a non-empty ABNF grammar
       (i.e. a value of type @(tsee rulelist) that is not @('nil'))."))

    (xdoc::desc
     "@(':prefix') &mdash; no default"
     (xdoc::p
      "Prefix of the parsing functions generated
       by the generated @('p::defparse-name-...') macros.")
     (xdoc::p
      "This is often something like
       @('parse') or @('lex') in some package @('\"Q\"'),
       so that the generated parsing functions have names of the form
       @('q::parse-...') or @('q::lex-...').
       Note that the package @('\"Q\"') may differ from @('\"P\"').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('defparse-name-group-table')"
     (xdoc::p
      "Macro to define a table that maps
       groups in the grammar to the corresponding parsing function names.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-group-table"
      "  \"<group1>\" symbol1"
      "  ..."
      "  \"<groupN>\" symbolN"
      "  )")
     (xdoc::p
      "where each @('<groupI>') is a group written in ABNF concrete syntax
       and each @('symbolI') is the name of the function
       without the prefix specified in the @(':prefix') input.
       That is, the name of the parsing function
       for the group described by @('<groupI>') is @('prefix-symbolI').")
     (xdoc::p
      "The @('<group1>'), ..., @('<groupN>') strings
       are parsed via the verified @(tsee parse-group),
       obtaining @(tsee alternation)s that must be all distinct.")
     (xdoc::p
      "The parsing functions @('prefix-symbol1'), ..., @('prefix-symbolN')
       do not exist yet when @('defparse-name-group-table') is called.
       The call merely defines the names of these functions,
       which are created later via @('defparse-name-group') (see below)."))

    (xdoc::desc
     "@('defparse-name-option-table')"
     (xdoc::p
      "Macro to define a table that maps
       options in the grammar to the corresponding parsing function names.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-option-table"
      "  \"<option1>\" symbol1"
      "  ..."
      "  \"<optionN>\" symbolN"
      "  )")
     (xdoc::p
      "where each @('<optionI>') is an option written in ABNF concrete syntax
       and each @('symbolI') is the name of the function
       without the prefix specified in the @(':prefix') input.
       That is, the name of the parsing function
       for the option described by @('<optionI>') is @('prefix-symbolI').")
     (xdoc::p
      "The @('<option1>'), ..., @('<optionN>') strings
       are parsed via the verified @(tsee parse-option),
       obtaining @(tsee alternation)s that must be all distinct.")
     (xdoc::p
      "The parsing functions @('prefix-symbol1'), ..., @('prefix-symbolN')
       do not exist yet when @('defparse-name-option-table') is called.
       The call merely defines the names of these functions,
       which are created later via @('defparse-name-option') (see below)."))

    (xdoc::desc
     "@('defparse-name-repetition-table')"
     (xdoc::p
      "Macro to define a table that maps
       repetitions in the grammar to the corresponding parsing function names.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-repetition-table"
      "  \"<repetition>\" symbol1"
      "  ..."
      "  \"<repetitionN>\" symbolN"
      "  )")
     (xdoc::p
      "where each @('<repetitionI>') is a group written in ABNF concrete syntax
       and each @('symbolI') is the name of the function
       without the prefix specified in the @(':prefix') input.
       That is, the name of the parsing function
       for the repetition described by @('<repetition>')
       is @('prefix-symbolI').")
     (xdoc::p
      "The @('<repetition1>'), ..., @('<repetitionN>') strings
       are parsed via the verified @(tsee parse-repetition),
       obtaining @(tsee repetition)s that must be all distinct.")
     (xdoc::p
      "The parsing functions @('prefix-symbol1'), ..., @('prefix-symbolN')
       do not exist yet when @('defparse-name-repetition-table') is called.
       The call merely defines the names of these functions,
       which are created later via
       @('defparse-name-*-rulename') and @('defparse-name-*-group')
       (see below)."))

    (xdoc::desc
     "@('defparse-name-rulename')"
     (xdoc::p
      "Macro to generate a parsing function for a rule name in the grammar.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-rulename \"<rulename>\") :order ...")
     (xdoc::p
      "where @('<rulename>') is a rule name in the grammar
       and @(':order'), which is optional,
       specifies a permutation of the list @('(1 ... N)'),
       where @('N') is the number of alternatives
       that defines the rule name in the grammar.")
     (xdoc::p
      "The parsing functions for all the
       rule names, groups, options, and repetitions
       that occur in the alternatives that define the rule name
       must have already been generated when this call is made.")
     (xdoc::p
      "If present, @(':order') specifies the order in which
       the alternatives that define the rule name
       is attempted by the generated parsing function for the rule name.")
     (xdoc::p
      "The name of the generated parsing function is @('prefix-rulename')."))

    (xdoc::desc
     "@('defparse-name-*-rulename')"
     (xdoc::p
      "Macro to generate a parsing function for
       a repetition of zero or more instances of a rule name.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-*-rulename \"<rulename>\")")
     (xdoc::p
      "where @('<rulename>') is a rule name in the grammar,
       for which a parsing function must have already been generated
       when this call is made.")
     (xdoc::p
      "The repetition must be
       in the table generated via @('defparse-name-repetition-table')
       (see above).
       The name of the generated parsing function
       is the corresponding one in the table."))

    (xdoc::desc
     "@('defparse-name-group')"
     (xdoc::p
      "Macro to generate a parsing function for a group in the grammar.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-group \"<group>\") :order ...")
     (xdoc::p
      "where @('<group>') is a group in the grammar
       written in ABNF concrete syntax,
       and @(':order'), which is optional,
       specifies a permutation of the list @('(1 ... N)'),
       where @('N') is the number of alternatives
       that forms the group.")
     (xdoc::p
      "The parsing functions for all the
       rule names, groups, options, and repetitions
       that occur in the group
       must have already been generated when this call is made.")
     (xdoc::p
      "If present, @(':order') specifies the order in which
       the alternatives that form the group
       is attempted by the generated parsing function for the group.")
     (xdoc::p
      "The group must be
       in the table generated via @('defparse-name-group-table')
       (see above).
       The name of the generated parsing function
       is the corresponding one in the table."))

    (xdoc::desc
     "@('defparse-name-*-group')"
     (xdoc::p
      "Macro to generate a parsing function for
       a repetition of zero or more instances of a group.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-*-group \"<group>\")")
     (xdoc::p
      "where @('<group>') is a group in the grammar
       written in ABNF concrete syntax,
       for which a parsing function must have already been generated
       when this call is made.")
     (xdoc::p
      "The repetition must be
       in the table generated via @('defparse-name-repetition-table')
       (see above).
       The name of the generated parsing function
       is the corresponding one in the table."))

    (xdoc::desc
     "@('defparse-name-option')"
     (xdoc::p
      "Macro to generate a parsing function for an option in the grammar.")
     (xdoc::p
      "It is called as")
     (xdoc::codeblock
      "(defparse-name-option \"<option>\") :order ...")
     (xdoc::p
      "where @('<option>') is an option in the grammar
       written in ABNF concrete syntax,
       and @(':order'), which is optional,
       specifies a permutation of the list @('(1 ... N)'),
       where @('N') is the number of alternatives
       that forms the option")
     (xdoc::p
      "The parsing functions for all the
       rule names, groups, options, and repetitions
       that occur in the option
       must have already been generated when this call is made.")
     (xdoc::p
      "If present, @(':order') specifies the order in which
       the alternatives that form the option
       is attempted by the generated parsing function for the option")
     (xdoc::p
      "The group must be
       in the table generated via @('defparse-name-option-table')
       (see above).
       The name of the generated parsing function
       is the corresponding one in the table.")))))
