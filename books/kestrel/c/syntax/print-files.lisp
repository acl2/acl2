; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "printer")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/std/system/constant-value" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "kestrel/std/system/w" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc print-files

  :parents (syntax-for-tools)

  :short "Print files to a file set constant
          from a translation unit ensemble constant."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro takes as input the name of a named constant
      whose value is a translation unit ensemble
      (see @(tsee transunit-ensemble)),
      uses the @(see printer) to print the translation unit ensemble,
      which is the abstract syntax representation of a file set,
      to a file set (see @(tsee fileset)),
      and generates an ACL2 @(tsee defconst)
      with the file set.")

    (xdoc::p
     "This macro can be used before @(tsee write-files),
      which writes a named constant containing a file set
      to files at the paths in the file set.")

    (xdoc::p
     "This macro currently does not perform very thorough input validation,
      but we plan to improve that."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(print-files :const-fileset    ...  ; no default"
     "             :const-transunits ...  ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':const-fileset')"
     (xdoc::p
      "Name of the generated constant that contains the file set.")
     (xdoc::p
      "This must be a symbol that is a valid name for a new named constant.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-fileset*') be this symbol."))

    (xdoc::desc
     "@(':const-transunits')"
     (xdoc::p
      "Name of the existing constant that contains
       the translation unit ensemble.")
     (xdoc::p
      "This must be a symbol that names an existing named constant,
       whose value must be a translation unit ensemble.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-transunits*') be this symbol.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('*const-fileset*')"
     (xdoc::p
      "The named constant containing the file set obtained by printing
       the translation unit ensemble in @('*const-transunits*').")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ print-files-implementation
  :parents (print-files)
  :short "Implementation of @(tsee print-files)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *print-files-allowed-options*
  :short "Keyword options accepted by @(tsee print-files)."
  (list :const-fileset
        :const-transunits)
  ///
  (assert-event (keyword-listp *print-files-allowed-options*))
  (assert-event (no-duplicatesp-eq *print-files-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-files-process-inputs ((args true-listp) (wrld plist-worldp))
  :returns (mv erp
               (const-fileset symbolp)
               (value-transunits transunit-ensemblep))
  :short "Process the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the translation unit ensemble constant name input,
     we retrieve and return the translation unit ensemble."))
  (b* (((reterr) nil (fileset nil))
       ;; Check and obtain options.
       ((mv erp extra options)
        (partition-rest-and-keyword-args args *print-files-allowed-options*))
       ((when erp)
        (reterr (msg "The inputs must be the options ~&0, ~
                      but instead they are ~x1."
                     *print-files-allowed-options*
                     args)))
       ((when extra)
        (reterr (msg "The only allowed inputs are the options ~&0, ~
                      but instead the extra inputs ~x1 were supplied."
                     *print-files-allowed-options*
                     extra)))
       ;; Process :CONST-FILESET input.
       (const-fileset-option (assoc-eq :const-fileset options))
       ((unless const-fileset-option)
        (reterr (msg "The :CONST-FILESET input must be supplied, ~
                      but it was not supplied.")))
       (const-fileset (cdr const-fileset-option))
       ((unless (symbolp const-fileset))
        (reterr (msg "The :CONST-FILESET input must be a symbol, ~
                      but it is ~x0 instead."
                     const-fileset)))
       ;; Process :CONST-TRANSUNITS input.
       (const-transunits-option (assoc-eq :const-transunits options))
       ((unless const-transunits-option)
        (reterr (msg "The :CONST-TRANSUNITS input must be supplied, ~
                      but it was not supplied.")))
       (const-transunits (cdr const-transunits-option))
       ((unless (symbolp const-transunits))
        (reterr (msg "The :CONST-TRANSUNITS input must be a symbol, ~
                      but it is ~x0 instead."
                     const-transunits)))
       (value-transunits (acl2::constant-value const-transunits wrld))
       ((unless (transunit-ensemblep value-transunits))
        (reterr (msg "The value of the ~x0 named constant ~
                      specified by the :CONST-TRANSUNITS input ~
                      must satisfy TRANSUNIT-ENSEMBLEP, ~
                      but instead its value is ~x1."
                     const-transunits
                     value-transunits))))
    (retok const-fileset value-transunits))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-files-gen-defconst ((const-fileset symbolp)
                                  (value-transunits transunit-ensemblep))
  :returns (event pseudo-event-formp)
  :short "Generate the named constant event."
  (b* ((fileset (print-fileset value-transunits))
       (event `(defconst ,const-fileset ',fileset)))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-files-process-inputs-and-gen-defconst ((args true-listp)
                                                     (wrld plist-worldp))
  :returns (mv erp
               (event pseudo-event-formp
                      :hints
                      (("Goal" :in-theory (disable pseudo-event-formp)))))
  :short "Process the inputs and generate the constant event."
  (b* (((reterr) '(_))
       ((erp const-fileset value-transunits)
        (print-files-process-inputs args wrld))
       (event
        (print-files-gen-defconst const-fileset value-transunits)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-files-fn ((args true-listp) (ctx ctxp) state)
  :short "Event expansion of @(tsee print-files) from the inputs."
  (b* (((mv erp event)
        (print-files-process-inputs-and-gen-defconst args (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection print-files-definition
  :short "Definition of the @(tsee print-files) macro."
  (defmacro print-files (&rest args)
    `(make-event-terse (print-files-fn ',args 'print-files state))))
