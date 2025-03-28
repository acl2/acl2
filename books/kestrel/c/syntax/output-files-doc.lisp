; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc output-files

  :parents (syntax-for-tools)

  :short "Write C files to the file system from an ACL2 representation."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "In the name of this macro,
      @('output') is best read as a verb:
      the macro outputs files from ACL2.")

    (xdoc::p
     "This macro takes as input an ACL2 representation of C code
      and writes that C code to the file system.
      The ACL2 representation of the C code could be
      the result of applying transformations to
      code obtained via @(tsee input-files);
      so this @('output-files') macros can provide
      the final step in that process.")

    (xdoc::p
     "The (non-event) macro @(tsee output-files-prog) provides
      a programmatic interface to the functionality of @('output-files')."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(output-files :const           ...  ; required"
     "              :path            ...  ; default \".\""
     "              :printer-options ...  ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':const')"
     (xdoc::p
      "Name of the existing ACL2 constant that contains
       the representation of the C code to write to the file system.")
     (xdoc::p
      "This constant must contain an "
      (xdoc::seetopic "unambiguity" "unambiguous")
      " translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble)
       that additionally satisfies @(tsee transunit-ensemble-unambp)).
       The translation unit is printed to a file set,
       whose files are written to the file system.
       The keys of the file set map are the same as
       the keys of the translation unit ensemble map.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const*') be the name of this constant."))

    (xdoc::desc
     "@(':path') &mdash; default @('\".\"')"
     (xdoc::p
      "Path that the files are written into.")
     (xdoc::p
      "This must be a non-empty string that is a valid path name in the system.
       It may or may not end with a slash.
       A non-absolute path is relative to
       the connected book directory (see @(tsee cbd)).
       In particular, the @('\".\"') path (which is the default)
       specifies the connected book directory.")
     (xdoc::p
      "Each file in the file set obtained from the translation unit ensemble
       is written to the path resulting from
       prepending the corresponding key in the file set map
       with the path specified by the @(':path') input."))

    (xdoc::desc
     "@(':printer-options') &mdash; default @('nil')"
     (xdoc::p
      "Specifies options for various aspects of how the C code is printed.")
     (xdoc::p
      "This must be a "
      (xdoc::seetopic "acl2::keyword-value-listp" "keyword-value list")
      " @('(opt-name1 opt-value1 opt-name2 opt-value2 ...)')
       where each @('opt-namek') is a keyword among the ones described below,
       and each @('opt-valuek') is one of the allowed values
       for the corresponding keyword as described below.")
     (xdoc::p
      "The following options are supported:")
     (xdoc::ul
      (xdoc::li
       "@(':indentation-size <posint>'),
        where @('<posint>') is a positive integer.
        This specifies the size of each indentation level,
        measured in number of spaces.
        If this option is not supplied, it defaults to 2.")
      (xdoc::li
       "@(':parenthesize-nested-conditionals <t/nil>'),
        where @('<t/nil>') is a boolean.
        This specifies whether
        conditional expressions that are `then' or `else' sub-expressions
        of outer conditional expressions
        should be parenthesized or not.
        For instance, whether the expression"
       (xdoc::codeblock "a ? b ? c : d : e ? f g")
       "should be printed as"
       (xdoc::codeblock "a ? (b ? c : e) : (e ? f : g)")
       "The two expressions are equivalent due to the precedence rules of C,
        but the second one is more readable.
        If this option is @('t'), the printer adds the parentheses;
        if thie option is @('nil'), no extra parentheses are added.
        If this option is not supplied, it defaults to @('nil')."))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "This macro generates one file in the file system
      for each element of the translation unit ensemble in @('*const*'),
      at the paths that are obtained by prepending the keys of the maps
      with the path specified by the @(':path') input."))))
