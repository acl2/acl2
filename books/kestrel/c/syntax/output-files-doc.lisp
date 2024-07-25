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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc output-files

  :parents (syntax-for-tools)

  :short "Write C files to the file system from an ACL2 representation."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro takes as input an ACL2 representation of C code
      and writes that C code to the file system.
      The ACL2 representation of the C code could be
      the result of applying transformations to
      code obtained via @(tsee input-files);
      so this @('output-files') macros can provide
      the final step in that process.")

    (xdoc::p
     "This macro currently does not perform very thorough input validation,
      but we plan to improve that."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(output-files :const ...       ; no default"
     "              :process ...     ; default nil"
     "              :const-files ... ; default nil"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':const')"
     (xdoc::p
      "Name of the existing ACL2 constant that contains
       the representation of the C code to write to the file system.")
     (xdoc::p
      "This constant must contain
       a fileset
       (i.e. a value of type @(tsee fileset))
       if the @(':process') input (see below) is @('nil'),
       or a translation unit ensemble
       (i.e. a value of type @(tsee transunit-ensemble))
       if the @(':process') input is @(':print').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const*') be the name of this constant."))

    (xdoc::desc
     "@(':process') &mdash; default @('nil')"
     (xdoc::p
      "Specifies the processing to perform
       on the ACL2 representation of the C code in @('*const*').")
     (xdoc::p
      "This must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('nil'), for no processing.
        In this case, @('*const*') must contain a file set,
        which is written to the file system as is.")
      (xdoc::li
       "@(':print'), to print the abstract syntax in @('*const*')
        to a file set that is then written to the file system.
        In this case, @('*const*') must contain a translation unit ensemble.")))

    (xdoc::desc
     "@(':const-files') &mdash; default @('nil')"
     (xdoc::p
      "Name of the generated ACL2 constant whose value is
       the file set obtained by printing @('*const*').")
     (xdoc::p
      "If this input is @('nil'),
       this constant is not generated.")
     (xdoc::p
      "This input must be @('nil') if
       @(':process') is @('nil'),
       because in that case @('*const*') already contains a file set.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-files*') be the name of this constant,
       if not @('nil').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "This macro generates one file in the file system
      for each element of the translation unit ensemble or file set
      in @('*const*'),
      at the paths that are the keys of the maps.
      Non-absolute paths are relative to
      the connected book directory (see @(tsee cbd)).")

    (xdoc::desc
     "@('*const-files*')"
     (xdoc::p
      "Optionally,
       the named constant containing the file set
       obtained by printing the abstract syntax in @('*const*').")))))
