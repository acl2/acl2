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

(defxdoc defgrammar

  :parents (abnf)

  :short "Build an ACL2 representation of an ABNF grammar from a file."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro
      calls the "
     (xdoc::seetopic "grammar-parser" "verified grammar parser")
     " on the specified file,
      applies the "
     (xdoc::seetopic "syntax-abstraction" "abstractor")
     " on the resulting concrete syntax tree of the grammar
      to obtain an abstract syntax tree of the grammar,
      and introduces a named constant for this abstract syntax tree.
      This provides an ACL2 representation of the grammar,
      which has a formal @(see semantics)
      and which is amenable to @(see operations), "
     (xdoc::seetopic "defdefparse" "parser generation")
     ", etc.")

    (xdoc::p
     "Besides introducing the named constant,
      this macro can also (attempt to) prove certain properties of the grammar,
      under user control.")

    (xdoc::p
     "This macro also generates an XDOC topic for the named constant,
      which includes any generated events.")

    (xdoc::p
     "In addition, this macro can optionally generate predicates
      that say whether ABNF trees match ABNF abstract syntax elements.
      These are versions of the tree matching predicates
      in the formal @(see semantics) of ABNF,
      but they are specialized to the grammar,
      and are therefore more concise.")

    (xdoc::p
     "Currently the implementation of this macro does not perform
      very thorough input validation.
      This will be improved in the future."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defgrammar *name*"
     "            :file ..."
     "            :untranslate ..."
     "            :well-formed ..."
     "            :closed ..."
     "            :matchers ..."
     "            :parents ..."
     "            :short ..."
     "            :long ..."
     "  ///"
     "  <other events>"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('*name*')"
     (xdoc::p
      "Name of the named constant introduced by this macro.")
     (xdoc::p
      "It must be a valid constant name.")
     (xdoc::p
      "This is defined as the abstract syntax tree
       of the grammar read from the file specified by the @(':file') input.
       See the `"
      xdoc::*evmac-section-generated-title*
      "' section for details."))

    (xdoc::desc
     "@(':file') &mdash; no default"
     (xdoc::p
      "Path of the file that contains the grammar.")
     (xdoc::p
      "This should be normally a file with extension @('.abnf'),
       which for example is recognized and syntax-highlighted by GitHub,
       but this extension is not a requirement.
       The extension (whether @('.abnf') or not) must be specified.")
     (xdoc::p
      "The lines in the file must be terminated
       by a carriage return and line feed,
       as required by the ABNF grammar of ABNF.
       On Unix systems (e.g. Linux and macOS),
       this can be accomplished by writing the file in Emacs,
       setting the buffer's end-of-line to carriage return and line feed
       by calling @('set-buffer-file-coding-system') with @('dos'),
       and saving the file.
       If the file is under a version control system like @('git'),
       it should be forced to be treated as a text file with CRLF end-of-line
       (e.g. see @('[books]/kestrel/abnf/notation/.gitattributes')),
       to avoid turning carriage returns and line feeds into just line feeds
       across Windows and Unix platforms.")
     (xdoc::p
      "This must be an ACL2 string that is a file path.
       The path may be absolute,
       or relative to the current working directory."))

    (xdoc::desc
     "@(':untranslate') &mdash; default @('nil')"
     (xdoc::p
      "Specifies whether the constant should be untranslated in output.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to untranslate the constant in output.
        In this case, @('defgrammar') generates
        and @(tsee add-const-to-untranslate-preprocess) event,
        which modifies ACL2's untranslation to ``shrink''
        the quoted value of the named constant introduced by @('defgrammar')
        into the name of the constant.
        As the abstract syntax tree of a grammar may be relatively large,
        this keeps the ACL2 output
        more readable and efficient to print in Emacs.")
      (xdoc::li
       "@('nil'), to not untranslate the constant in output.
        In this case, @('defgrammar') does not generate
        any @(tsee add-const-to-untranslate-preprocess) event,
        and ACL2's untranslation is unmodified."))
     (xdoc::p
      "It is normally advisable to untranslate the constant in output."))

    (xdoc::desc
     "@(':well-formed') &mdash; default @('nil')"
     (xdoc::p
      "Specifies whether @('defgrammar') should generate a theorem
       saying that the grammar is "
      (xdoc::seetopic "well-formedness" "well-formed")
      ".")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to generate the theorem.")
      (xdoc::li
       "@('nil'), to not generate the theorem."))
     (xdoc::p
      "See the `"
      xdoc::*evmac-section-generated-title*
      "' section for the details of this theorem.")
     (xdoc::p
      "It is normally expected for a grammar to be well-formed."))

    (xdoc::desc
     "@(':closed') &mdash; default @('nil')"
     (xdoc::p
      "Specifies whether @('defgrammar') should generate a theorem
       saying that the grammar is "
      (xdoc::seetopic "closure" "closed")
      ".")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to generate the theorem.")
      (xdoc::li
       "@('nil'), to not generate the theorem."))
     (xdoc::p
      "See the `"
      xdoc::*evmac-section-generated-title*
      "' section for the details of this theorem.")
     (xdoc::p
      "A grammar may or may not be closed:
       it could a component of a larger grammar,
       which is closed even though not all of its components are"))

    (xdoc::desc
     "@(':matchers') &mdash; default @('nil')"
     (xdoc::p
      "Specifies whether @('defgrammar') should generate
       tree matching predicates specialized to the grammar.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "Any non-@('nil') symbol, to generate the predicates.
        In this case, the symbol is used as prefix of the names.")
      (xdoc::li
       "@('nil'), to not generate the predicates."))
     (xdoc::p
      "See the `"
      xdoc::*evmac-section-generated-title*
      "' section for the details of these predicates,
       including the role of the prefix symbol in their names."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are added to
       the XDOC topic generated by @('defgrammar').")
     (xdoc::p
      "These are evaluated by @('defgrammar'), making it possible to use "
      (xdoc::seetopic "xdoc::constructors" "XDOC constructors")
      "."))

    (xdoc::desc
     "@('<other-events>')"
     (xdoc::p
      "Optionally, the @('defgrammar') can include other events
       preceded by @('///'), which must follow all the above inputs.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('*name*')"
     (xdoc::p
      "The named constant.")
     (xdoc::p
      "This uses @(tsee make-event) to
       call @(tsee parse-grammar-from-file)
       and then @(tsee abstract-rulelist),
       obtaining a value that is used as a quoted constant
       to define the named constant."))

    (xdoc::desc
     "The @(tsee add-const-to-untranslate-preprocess) event."
     (xdoc::p
      "This is generated iff the @(':untranslate') input is @('t')."))

    (xdoc::desc
     "@('rulelist-wfp-of-*name*')"
     (xdoc::p
      "The theorem asserting that the grammar is well-formed:")
     (xdoc::codeblock
      "(rulelist-wfp *name*)")
     (xdoc::p
      "This is generated iff the @(':well-formed') input is @('t')."))

    (xdoc::desc
     "@('rulelist-closedp-of-*name*')"
     (xdoc::p
      "The theorem asserting that the grammar is closed:")
     (xdoc::codeblock
      "(rulelist-closedp *name*)")
     (xdoc::p
      "This is generated iff the @(':closed') input is @('t')."))

    (xdoc::desc
     (list
      "@('cst-matchp')"
      "@('cst-list-elem-matchp')"
      "@('cst-list-rep-matchp')"
      "@('cst-list-list-conc-matchp')"
      "@('cst-list-list-alt-matchp')")
     (xdoc::p
      "The tree matching predicates,
       if the @(':matchers') input is the symbol @('cst').
       Any symbol may be used,
       but @('cst') (for Concrete Syntax Tree)
       may be often a good choice,
       in a package related to the language that the grammar refers to
       (e.g. @('java::cst') for Java).
       A longer prefix may be used when, in the same package,
       there are multiple languages and grammars of interest,
       e.g. @('pkg::lang1-cst') for one and @('pkg::lang2-cst') for the other.
       The predicates are put in the same package as the prefix symbol.")
     (xdoc::p
      "Each predicate takes two arguments:")
     (xdoc::ol
      (xdoc::li
       "A tree (for the first one),
        or a list of trees (for the second and third one),
        or a list of lists of trees (for the fourth and fifth one).")
      (xdoc::li
       "An ACL2 string, which must be an ABNF concrete syntax representation of
        an element (for the first and second one),
        or a repetition (for the third one),
        or a concatenation (for the fourth one),
        or an alternation (for the fifth one)."))
     (xdoc::p
      "Each predicate holds iff the (list of (list of)) tree(s)
       is terminated and
       matches the element or repetition or concatenation or alternation.
       While in the @(see semantics) it makes sense
       to include non-terminated trees as potentially matching,
       for a specific grammar it normally makes sense
       to consider only terminated trees:
       this motivates the extra condition.")
     (xdoc::p
      "These generated predicates are actually macros,
       which use (subroutines of) the "
      (xdoc::seetopic "grammar-parser" "verified grammar parser")
      " to parse the ACL2 strings passed as second arguments
       into their ABNF abstract syntactic representation,
       and then expand to calls of the appropriate
       generic tree matching predicates in the @(see semantics),
       passing the grammar as argument to them;
       the dependency on the grammar is implicit in the generated predicates.
       Note that the parsing of the strings happens
       at macro expansion time (i.e. at compile time),
       not at predicate call time (i.e. at run time).")
     (xdoc::p
      "There are some generated internal intermediate predicates
       that these macros expand into calls of,
       and it is these intermediate predicates that call
       the generic tree matching predicates from the @(see semantics).
       These intermediate predicates are actual ACL2 functions,
       whose names are identical to the macros but with @('$') at the end. "
      (xdoc::seetopic "acl2::macro-aliases-table" "Macro aliases")
      " are also generated that link the macro names to the function names:
       this way, the predicates can be opened (in proofs)
       via their macro names."))

    (xdoc::desc
     "@('<other-events>')"
     (xdoc::p
      "If specified, these are put after all the above events."))

    (xdoc::p
     "All these events are inside a @(tsee defsection)
      whose name is @('*name*')
      and whose parent list, short string, and long string
      are the ones specified in the respective inputs."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    xdoc::*evmac-section-redundancy-title*

    (xdoc::p
     "A call of @('defgrammar') is redundant if and only if
      it is identical to a previous successful call of @('defgrammar')
      with the exact same arguments."))))
