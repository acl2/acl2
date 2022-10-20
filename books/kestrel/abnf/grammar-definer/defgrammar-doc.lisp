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
     " on the specific file,
      applies the "
     (xdoc::seetopic "syntax-abstraction" "abstractor")
     " on the resulting concrete syntax tree of the grammar
      to obtain an abstract syntax tree of the grammar,
      and introduces a named constant for this abstract syntax tree.
      This provides an ACL2 representation of the grammar,
      which has a formal @(see semantics)
      and which is amenable to @(see operations), "
     (xdoc::seetopic "parser-generators" "parser generators")
     ", etc.")

    (xdoc::p
     "Besides introducing the named constant,
      this macro can also (attempt to) prove certain properties of the grammar,
      under user control.")

    (xdoc::p
     "This macro also generates an XDOC topic for the named constant,
      which includes any generated theorem event.")

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
     "            :well-formedness ..."
     "            :closure ..."
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
     "@(':untranslate') &mdash; default @('t')"
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
      "This input is @('t') by default because
       it is normally advisable to untranslate the constant in output."))

    (xdoc::desc
     "@(':well-formedness') &mdash; default @('t')"
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
      "This input is @('t') by default because
       it is normally expected for a grammar to be well-formed."))

    (xdoc::desc
     "@(':closure') &mdash; default @('nil')"
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
      "This input is @('nil') by default because
       a grammar may or may not be closed:
       it could a component of a larger grammar,
       which is closed even though not all of its components are"))

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
      "This is generated iff the @(':well-formedness') input is @('t')."))

    (xdoc::desc
     "@('rulelist-closedp-of-*name*')"
     (xdoc::p
      "The theorem asserting that the grammar is closed:")
     (xdoc::codeblock
      "(rulelist-closedp *name*)")
     (xdoc::p
      "This is generated iff the @(':closure') input is @('t')."))

    (xdoc::desc
     "@('<other-events>')"
     (xdoc::p
      "If specified, these are put after all the above events."))

    (xdoc::p
     "All these events are inside a @(tsee defsection)
      whose name is @('*name*')
      and whose parent list, short string, and long string
      are the ones specified in the respective inputs."))))
