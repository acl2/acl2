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
(include-book "printer")

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

(defxdoc print-and-write-files

  :parents (syntax-for-tools)

  :short "Print and write files to the file system
          from a translation unit ensemble constant."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro combines @(tsee print-files) and @(tsee write-files),
      but without creating a named constant for the fileset.
      It just takes a named constant for the translation unit ensemble,
      and writes the files obtained by printing the ensemble.")

    (xdoc::p
     "This macro currently does not perform very thorough input validation,
      but we plan to improve that."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(print-and-write-files :const ...  ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':const')"
     (xdoc::p
      "Name of the existing constant that contains
       the translation unit ensemble.")
     (xdoc::p
      "This must be a symbol that names an existing named constant,
       whose value must be a translation unit ensemble.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "This macro generates one file in the file system
      for each element of the translation unit ensemble,
      at the paths that are the keys of the file set map.
      Non-absolute paths are relative to
      the connected book directory (see @(tsee cbd))."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ print-and-write-files-implementation
  :parents (print-and-write-files)
  :short "Implementation of @(tsee print-and-write-files)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *print-and-write-files-allowed-options*
  :short "Keyword options accepted by @(tsee print-and-write-files)."
  (list :const)
  ///
  (assert-event (keyword-listp *print-and-write-files-allowed-options*))
  (assert-event (no-duplicatesp-eq *print-and-write-files-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-and-write-files-process-inputs ((args true-listp)
                                              (wrld plist-worldp))
  :returns (mv erp (tunits transunit-ensemblep))
  :short "Process the inputs."
  (b* (((reterr) (transunit-ensemble nil))
       ;; Check and obtain options.
       ((mv erp extra options)
        (partition-rest-and-keyword-args
         args *print-and-write-files-allowed-options*))
       ((when erp)
        (reterr (msg "The inputs must be the options ~&0, ~
                      but instead they are ~x1."
                     *print-and-write-files-allowed-options*
                     args)))
       ((when extra)
        (reterr (msg "The only allowed inputs are the options ~&0, ~
                      but instead the extra inputs ~x1 were supplied."
                     *print-and-write-files-allowed-options*
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
       (tunits (acl2::constant-value const wrld))
       ((unless (transunit-ensemblep tunits))
        (reterr (msg "The value of the ~x0 named constant ~
                      specified by the :CONST input ~
                      must satisfy TRANSUNIT-ENSEMBLEP, ~
                      but instead its value is ~x1."
                     const
                     tunits))))
    (retok tunits))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-and-write-files-gen-files ((tunits transunit-ensemblep) state)
  :returns (mv erp state)
  :short "Write a translation unit ensemble to the file system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the file set
     obtained by printing the translation unit ensemble,
     and write the data of each value in the map
     to the path of the associated key in the map."))
  (b* ((fileset (print-fileset tunits)))
    (print-and-write-files-gen-files-loop (fileset->unwrap fileset) state))

  :prepwork
  ((define print-and-write-files-gen-files-loop ((map filepath-filedata-mapp)
                                                 state)
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
                                                      'print-and-write-files
                                                      state))
          ((when erp)
           (reterr (msg "Writing ~x0 failed." path-string))))
       (print-and-write-files-gen-files-loop (omap::tail map) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-and-write-files-process-inputs-and-gen-files ((args true-listp)
                                                            state)
  :returns (mv erp state)
  :short "Process the inputs and generate the constant event."
  (b* (((reterr) state)
       ((erp fileset) (print-and-write-files-process-inputs args (w state)))
       ((erp state) (print-and-write-files-gen-files fileset state)))
    (retok state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-and-write-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee print-and-write-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not really need an event, so we use @(tsee value-triple)
     with @(':invisible') to prevent any spurious printing."))
  (b* (((mv erp state)
        (print-and-write-files-process-inputs-and-gen-files args state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value '(value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection print-and-write-files-definition
  :short "Definition of the @(tsee print-and-write-files) macro."
  (defmacro print-and-write-files (&rest args)
    `(make-event-terse
      (print-and-write-files-fn ',args 'print-and-write-files state))))
