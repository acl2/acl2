; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "files")

(include-book "kestrel/file-io-light/write-bytes-to-file-bang" :dir :system)
(include-book "kestrel/std/system/constant-value" :dir :system)
(include-book "kestrel/std/util/error-value-tuples" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "system/pseudo-event-formp" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "kestrel/std/system/w" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel all-bytep-when-byte-listp
  (implies (byte-listp x)
           (acl2::all-bytep x))
  :induct t
  :enable (byte-listp bytep unsigned-byte-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc write-files

  :parents (syntax-for-tools)

  :short "Write files to the file system from a file set constant."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro takes as input the name of a named constant
      whose value is a file set (see @(tsee fileset)),
      and writes the files to the file system,
      at the paths that are the keys of the file set map.")

    (xdoc::p
     "This macro can be used after @(tsee print-files),
      which prints a translation unit ensemble
      (which is the abstract syntax representation of a file set)
      to a file set.")

    (xdoc::p
     "This macro currently does not perform very thorough input validation,
      but we plan to improve that."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(write-files :const ...  ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':const')"
     (xdoc::p
      "Name of the existing constant that contains the file set.")
     (xdoc::p
      "This must be a symbol that names an existing named constant,
       whose value must be a file set.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "This macro generates one file in the file system
      for each element of the file set,
      at the paths that are the keys of the file set map.
      Non-absolute paths are relative to
      the connected book directory (see @(tsee cbd))."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ write-files-implementation
  :parents (write-files)
  :short "Implementation of @(tsee write-files)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *write-files-allowed-options*
  :short "Keyword options accepted by @(tsee write-files)."
  (list :const)
  ///
  (assert-event (keyword-listp *write-files-allowed-options*))
  (assert-event (no-duplicatesp-eq *write-files-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-files-process-inputs ((args true-listp) (wrld plist-worldp))
  :returns (mv erp (fileset filesetp))
  :short "Process the inputs."
  (b* (((reterr) (fileset nil))
       ;; Check and obtain options.
       ((mv erp extra options)
        (partition-rest-and-keyword-args args *write-files-allowed-options*))
       ((when erp)
        (reterr (msg "The inputs must be the options ~&0, ~
                      but instead they are ~x1."
                     *write-files-allowed-options*
                     args)))
       ((when extra)
        (reterr (msg "The only allowed inputs are the options ~&0, ~
                      but instead the extra inputs ~x1 were supplied."
                     *write-files-allowed-options*
                     extra)))
       ;; Process :CONST input.
       (const-option (assoc-eq :const options))
       ((unless const-option)
        (reterr (msg "The :CONST input must be supplied, ~
                      but it was not supplied.")))
       (const (cdr const-option))
       ((unless (symbolp const))
        (reterr (msg "The :CONST input must be a symbol, ~
                      but it is ~x0 instead."
                     const)))
       (fileset (acl2::constant-value const wrld))
       ((unless (filesetp fileset))
        (reterr (msg "The value of the ~x0 named constant ~
                      specified by the :CONST input ~
                      must satisfy FILESETP, ~
                      but instead its value is ~x1."
                     const
                     fileset))))
    (retok fileset))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-files-gen-files ((fileset filesetp) state)
  :returns (mv erp state)
  :short "Write a file set to the file system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the file set,
     and write the data of each value in the map
     to the path of the associated key in the map."))
  (write-files-gen-files-loop (fileset->unwrap fileset) state)

  :prepwork
  ((define write-files-gen-files-loop ((map filepath-filedata-mapp) state)
     :returns (mv erp state)
     :parents nil
     (b* (((reterr) state)
          ((when (omap::emptyp map)) (retok state))
          ((mv path data) (omap::head map))
          (path-string (filepath->unwrap path))
          ((unless (stringp path-string))
           (reterr (msg "File path must contain a string, ~
                         but it contains ~x0 instead."
                        path-string)))
          ((mv erp state) (acl2::write-bytes-to-file! (filedata->unwrap data)
                                                      path-string
                                                      'write-files
                                                      state))
          ((when erp)
           (reterr (msg "Writing ~x0 failed." path-string))))
       (write-files-gen-files-loop (omap::tail map) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-files-process-inputs-and-gen-files ((args true-listp) state)
  :returns (mv erp state)
  :short "Process the inputs and generate the constant event."
  (b* (((reterr) state)
       ((erp fileset) (write-files-process-inputs args (w state)))
       ((erp state) (write-files-gen-files fileset state)))
    (retok state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee write-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not really need an event, so we use @(tsee value-triple)
     with @(':invisible') to prevent any spurious printing."))
  (b* (((mv erp state)
        (write-files-process-inputs-and-gen-files args state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value '(value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write-files-definition
  :short "Definition of the @(tsee write-files) macro."
  (defmacro write-files (&rest args)
    `(make-event-terse (write-files-fn ',args 'write-files state))))
