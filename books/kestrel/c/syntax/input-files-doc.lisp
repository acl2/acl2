; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
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
     "This macro currently does not perform very thorough input validation,
      but we plan to improve that."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(input-files :files              ...  ; no default"
     "             :preprocess         ...  ; default nil"
     "             :process            ...  ; default :disambiguate"
     "             :const              ...  ; no default"
     "             :const-files        ...  ; default nil"
     "             :const-preproc      ...  ; default nil"
     "             :const-parsed       ...  ; default nil"
     "             :const-disamb       ...  ; default nil"
     "             :gcc                ...  ; default nil"
     "             :short-bytes        ...  ; default 2"
     "             :int-bytes          ...  ; default 4"
     "             :long-bytes         ...  ; default 8"
     "             :long-long-bytes    ...  ; default 8"
     "             :plain-char-signed  ... ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':files')"
     (xdoc::p
      "List of zero or more file paths that specify the files to be read.")
     (xdoc::p
      "This must be a list of strings that are valid path names in the system.
       Non-absolute paths are relative to
       the connected book directory (see @(tsee cbd)).")
     (xdoc::p
      "This input to this macro is not evaluated."))

    (xdoc::desc
     "@(':preprocess') &mdash; default @('nil')"
     (xdoc::p
      "Specifies the preprocessor to use, if any,
       on the files specified by the @(':files') input.")
     (xdoc::p
      "This input must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('nil') (the default),
        in which case no preprocessing is done.
        In this case, the files must be already in preprocessed form,
        unless the @(':process') input (see below) is @('nil').")
      (xdoc::li
       "A string,
        which names the preprocessor to use,
        which must be in the current path.")
      (xdoc::li
       "@(':auto'),
        which implicitly names the preprocessor @('\"cpp\"')
        (a common default),
        which must be in the current path."))
     (xdoc::p
      "The preprocessing (if this input is not @('nil')),
       is performed via the @(tsee preprocess-file) tool."))

    (xdoc::desc
     "@(':process') &mdash; default @(':validate')"
     (xdoc::p
      "Specifies the processing to perform
       on the files specified by the @(':files') input
       (if @(':preprocess') is @('nil'))
       or on the result of preprocessing those files
       (if @(':preprocess') is not @('nil')).")
     (xdoc::p
      "This input must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':read'),
        to perform no processing,
        i.e. just reading the files.")
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
        obtained from the disambiguator.
        Validation depends on the
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
      ":read < :parse < :disambiguate < :validate")
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
       the files specified in the @(':files') input.")
     (xdoc::p
      "This must be a valid name for a new constant.")
     (xdoc::p
      "If @(':process') is @(':read'),
       the value of the constant named by @(':const') is
       a file set (i.e. a value of type @(tsee fileset)),
       containing a representation of
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil')).")
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
       and such that the abstract syntax representation passed validation.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const*') be the name of this constant."))

    (xdoc::desc
     "@(':const-files') &mdash; default @('nil')"
     (xdoc::p
      "Name of the generated ACL2 constant whose value is
       the file set (i.e. a value of type @(tsee fileset))
       that represents the files specified by the @(':files') input,
       as read from the file system, without preprocessing.")
     (xdoc::p
      "If this input is @('nil'),
       this constant is not generated.")
     (xdoc::p
      "This input must be @('nil') if
       @(':preprocess') is @('nil') and @(':process') is @(':read'),
       because in this case the constant would contain
       the same value as the one specified by @(':const').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-files*') be the name of this constant,
       if not @('nil')."))

    (xdoc::desc
     "@(':const-preproc') &mdash; default @('nil')"
     (xdoc::p
      "Name of the generated ACL2 constant whole value is
       the file set (i.e. a value of type @(tsee fileset))
       that represents the files obtained by preprocessing
       the files specified by the @(':files') inputs.")
     (xdoc::p
      "If this input is @('nil'),
       this constant is not generated.")
     (xdoc::p
      "This input must be @('nil') if
       @(':preprocess') is @('nil'),
       because in that case there is no preprocessing.
       If a constant for the files is desired,
       the @(':const-files') input can be used for that.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-preproc*') be the name of this constant,
       if not @('nil')."))

    (xdoc::desc
     "@(':const-parsed') &mdash; default @('nil')"
     (xdoc::p
      "Name of the generated ACL2 constant whose value is
       the translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble))
       that represents the result of parsing
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil')).")
     (xdoc::p
      "If this input is @('nil'),
       this constant is not generated.")
     (xdoc::p
      "This input must be @('nil') if
       the @(':process') input is @(':read'),
       because in that case the files are not parsed.")
     (xdoc::p
      "This input must be @('nil') if
       the @(':process') input is @(':parse'),
       because in that case this constant would contain
       the same value as the constant specified by the @(':const') input.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-parsed*') be the name of this constant,
       if not @('nil')."))

    (xdoc::desc
     "@(':const-disamb') &mdash; default @('nil')"
     (xdoc::p
      "Name of the generated ACL2 constant whose value is
       the translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble))
       that represents the result of parsing and disambiguating
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil')).")
     (xdoc::p
      "If this input is @('nil'),
       this constant is not generated.")
     (xdoc::p
      "This input must be @('nil') if
       the @(':process') input is @(':read') or @(':parse'),
       because in that case the files are not parsed or disambiguated.")
     (xdoc::p
      "This input must be @('nil') if
       the @(':process') input is @(':disambiguate'),
       because in that case this constant would contain
       the same value as the constant specified by the @(':const') input.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-disamb*') be the name of this constant,
       if not @('nil').")
     (xdoc::p
      "Currently the value of this constant, if generated,
       is the same as the value of the @(':const') constant
       when @(':process') is @(':validate').
       This is because validation does not produce
       an updated translation unit ensemble.
       However, this may change soon:
       validation may enrich the abstract syntax with information."))

    (xdoc::desc
     "@(':gcc') &mdash; default @('nil')"
     (xdoc::p
      "Boolean saying whether certain GCC extensions
       should be accepted or not."))

    (xdoc::desc
     "@(:short-bytes') &mdash; default 2"
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
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil'))."))

    (xdoc::desc
     "@('*const-files*')"
     (xdoc::p
      "Optionally,
       the named constant containing the file set that represents
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil'))."))

    (xdoc::desc
     "@('*const-preproc*')"
     (xdoc::p
      "Optionally,
       the named constant containing the file set that represents
       the result of preprocessing the files specified by @(':files')."))

    (xdoc::desc
     "@('*const-parsed*')"
     (xdoc::p
      "Optionally,
       the named constant containing the abstract syntax representation,
       obtained from the parser without disambiguation, of
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil'))."))

    (xdoc::desc
     "@('*const-disamb*')"
     (xdoc::p
      "Optionally,
       the named constant containing the abstract syntax representation,
       obtained from the disambiguator, of
       the files specified by @(':files')
       (if @(':preprocess') is @('nil'))
       or the files resulting from preprocessing those
       (if @(':preprocess') is not @('nil')).")))))
