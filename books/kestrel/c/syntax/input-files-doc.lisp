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

(defxdoc input-files

  :parents (syntax-for-tools)

  :short "Read C files from the file system into an ACL2 representation."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "In the name of this macro,
      @('input') is best read as a verb:
      the macro inputs files into ACL2.")

    (xdoc::p
     "This macro takes as input a list of file paths
      (which must contain C code),
      reads those files from the file system,
      and performs a user-specified level of processing on them,
      yielding a representation in ACL2 of that C code.
      This representation can be further processed,
      e.g. to perform code transformations,
      after which the macro @(tsee output-files)
      can be used to write the transformed code to the file system.")

    (xdoc::p
     "The (non-event) macro @(tsee input-files-prog) provides
      a programmatic interface to the functionality of @('input-files')."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(input-files :files             ...  ; required"
     "             :path              ...  ; default \".\""
     "             :preprocess        ...  ; default nil"
     "             :preprocess-args   ...  ; no default"
     "             :process           ...  ; default :validate"
     "             :const             ...  ; required"
     "             :gcc               ...  ; default nil"
     "             :short-bytes       ...  ; default 2"
     "             :int-bytes         ...  ; default 4"
     "             :long-bytes        ...  ; default 8"
     "             :long-long-bytes   ...  ; default 8"
     "             :plain-char-signed ...  ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':files')"
     (xdoc::p
      "List of one or more file paths that specify the files to be read.")
     (xdoc::p
      "These paths are relative to
       the path specified by the @(':path') input.")
     (xdoc::p
      "This input to this macro is not evaluated."))

    (xdoc::desc
     "@(':path') &mdash; default @('\".\"')"
     (xdoc::p
      "Path that the file paths in @(':files') are relative to.")
     (xdoc::p
      "This must be a non-empty string that is a valid path name in the system.
       It may or may not end with a slash.
       A non-absolute path is relative to
       the connected book directory (see @(tsee cbd)).
       In particular, the @('\".\"') path (which is the default)
       specifies the connected book directory."))

    (xdoc::desc
     "@(':preprocess') &mdash; default @('nil')"
     (xdoc::p
      "Specifies the preprocessor to use, if any,
       on the files specified by the @(':files') and @(':path') inputs.")
     (xdoc::p
      "This input must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('nil') (the default),
        in which case no preprocessing is done.
        In this case, the files must be already in preprocessed form.")
      (xdoc::li
       "A string,
        which names the preprocessor to use,
        which must be in the current system path for executables.")
      (xdoc::li
       "@(':auto'),
        which implicitly names the preprocessor @('\"cpp\"')
        (a common default),
        which must be in the current system path for executables."))
     (xdoc::p
      "The preprocessing (if this input is not @('nil')),
       is performed via the @(tsee preprocess-file) tool."))

    (xdoc::desc
     "@(':preprocess-args') &mdash; no default"
     (xdoc::p
      "Specifies arguments to pass to the preprocessor.")
     (xdoc::p
      "This must be either absent or a list of zero or more strings,
       each of which is an argument to pass, e.g. @('-I').")
     (xdoc::p
      "If @(':preprocess') is @('nil'),
       the @(':preprocess-args') input must be absent.")
     (xdoc::p
      "If @(':preprocess') is not @('nil'),
       and the @(':preprocess-args') input is absent,
       the arguments @('-E') and @('-P') are passed to the preprocessor,
       in that order.")
     (xdoc::p
      "If @(':preprocess') is not @('nil'),
       and @(':preprocess-args') input is present,
       the argument @('-E') is passed to the preprocessor,
       followed by the arguments in the list, in that order.")
     (xdoc::p
      "See the preprocessor documentation for information about
       the arguments mentioned above."))

    (xdoc::desc
     "@(':process') &mdash; default @(':validate')"
     (xdoc::p
      "Specifies the processing to perform
       on the files specified by the @(':files') and @(':path') inputs
       (if @(':preprocess') is @('nil'))
       or on the result of preprocessing those files
       (if @(':preprocess') is not @('nil')).")
     (xdoc::p
      "This input must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':parse'),
        to "
       (xdoc::seetopic "parser" "parse")
       " the files into an "
       (xdoc::seetopic "abstract-syntax" "abstract syntax")
       " representation, which may contain ambiguous constructs.")
      (xdoc::li
       "@(':disambiguate'),
        to parse the files, and then to "
       (xdoc::seetopic "disambiguator" "disambiguate")
       " the possibly ambiguous abstract syntax representation
        obtained from the parser
        into a non-ambiguous abstract syntax representation.")
      (xdoc::li
       "@(':validate') (the default),
        to parse and disambiguate the files, and then to "
       (xdoc::seetopic "validator" "validate")
       " the disambiguated abstract syntax representation
        obtained from the disambiguator,
        which annotated the abstract syntax with "
       (xdoc::seetopic "validation-information" "validation information")
       ". Validation depends on the
        @(':short-bytes'),
        @(':int-bytes'),
        @(':long-bytes'),
        @(':long-long-bytes'), and
        @(':plain-char-signed')
        inputs, which determine an "
       (xdoc::seetopic "implementation-environments"
                       "implementation environment")
       "."))
     (xdoc::p
      "These levels of processing are ordered as")
     (xdoc::codeblock
      ":parse < :disambiguate < :validate")
     (xdoc::p
      "where a larger level includes and extends
       the processing of smaller levels.
       These processing levels are orthogonal to
       the preprocessing specified by @(':preprocess'),
       since they apply equally to
       either the original or the preprocessed files."))

    (xdoc::desc
     "@(':const')"
     (xdoc::p
      "Name of the generated ACL2 constant whose value is
       the final result of processing (and preprocessing)
       the files specified in the @(':files') and @(':path') inputs.")
     (xdoc::p
      "If @(':process') is @(':parse'),
       the value of the constant named by @(':const') is
       a translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble)),
       containing the abstract syntax representation of the code
       resulting from the parser.
       Since the parser captures ambiguous constructs without resolving them,
       this representation may include ambiguous constructs.")
     (xdoc::p
      "If @(':process') is @(':disambiguate'),
       the value of the constant named by @(':const') is
       a translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble)),
       containing the abstract syntax representation of the code
       obtained by disambiguating the one resulting from the parser.")
     (xdoc::p
      "If @(':process') is @(':validate'),
       the value of the constant named by @(':const') is
       a translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble)),
       containing the abstract syntax representation of the code
       obtained by disambiguating the one resulting from the parser,
       and such that the abstract syntax representation passed validation;
       this abstract syntax is annotated with validation information.")
     (xdoc::p
      "In all cases, the keys of the translation unit ensemble map
       are the file paths specified in the @(':files') input,
       without the @(':path') prefix.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const*') be the name of this constant."))

    (xdoc::desc
     "@(':gcc') &mdash; default @('nil')"
     (xdoc::p
      "Boolean flag saying whether certain GCC extensions
       should be accepted or not."))

    (xdoc::desc
     "@(':short-bytes') &mdash; default 2"
     (xdoc::p
      "Positive integer saying how many bytes are used to represent
       @('signed short int') and @('unsigned short int').")
     (xdoc::p
      "This must be at least 2."))

    (xdoc::desc
     "@(':int-bytes') &mdash; default 4"
     (xdoc::p
      "Positive integer saying how many bytes are used to represent
       @('signed int') and @('unsigned int').")
     (xdoc::p
      "This must be at least 4,
       and not less than @(':short-bytes')."))

    (xdoc::desc
     "@(':long-bytes') &mdash; default 8"
     (xdoc::p
      "Positive integer saying how many bytes are used to represent
       @('signed long int') and @('unsigned long int').")
     (xdoc::p
      "This must be at least 8,
       and not less than @(':int-bytes')."))

    (xdoc::desc
     "@(':long-long-bytes') &mdash; default 8"
     (xdoc::p
      "Positive integer saying how many bytes are used to represent
       @('signed long long int') and @('unsigned long long int').")
     (xdoc::p
      "This must be at least 8,
       and not less than @(':long-bytes')."))

    (xdoc::desc
     "@(':plain-char-signed') &mdash; default nil"
     (xdoc::p
      "Boolean saying whether the plain @('char') type consists of
       the same value as the @('signed char') or @('unsigned char') type.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('*const*')"
     (xdoc::p
      "The named constant containing the result of processing,
       as specified by @(':process'),
       the files specified by the @(':files') and @(':path') inputs
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil')).")))))
