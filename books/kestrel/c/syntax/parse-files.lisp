; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser")

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

(defxdoc parse-files

  :parents (syntax-for-tools)

  :short "Parse files from a file set constant
          to a translation unit ensemble constant."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro takes as input the name of a named constant
      whose value is a file set (see @(tsee fileset)),
      uses the @(see parser) to parse the file set
      into a translation unit ensemble (see @(tsee transunit-ensemble)),
      which is the abstract syntax representation of the file set,
      and generates an ACL2 @(tsee defconst)
      with the translation unit ensemble.")

    (xdoc::p
     "This macro can be used after @(tsee read-files),
      which creates a named constant containing a file set
      from files at specified paths.")

    (xdoc::p
     "This macro currently does not perform very thorough input validation,
      but we plan to improve that."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(parse-files :const-transunits ...  ; no default"
     "             :const-fileset    ...  ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':const-transunits')"
     (xdoc::p
      "Name of the generated constant that contains
       the translation unit ensemble.")
     (xdoc::p
      "This must be a symbol that is a valid name for a new named constant.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-transunits*') be this symbol."))

    (xdoc::desc
     "@(':const-fileset')"
     (xdoc::p
      "Name of the existing constant that contains the file set.")
     (xdoc::p
      "This must be a symbol that names an existing named constant,
       whose value must be a file set.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const-fileset*') be this symbol.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('*const-transunits*')"
     (xdoc::p
      "The named constant containing the translation unit ensemble
       obtained by parsing the file set in @('*const-fileset*').")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parse-files-implementation
  :parents (parse-files)
  :short "Implementation of @(tsee parse-files)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *parse-files-allowed-options*
  :short "Keyword options accepted by @(tsee parse-files)."
  (list :const-transunits
        :const-fileset)
  ///
  (assert-event (keyword-listp *parse-files-allowed-options*))
  (assert-event (no-duplicatesp-eq *parse-files-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-files-process-inputs ((args true-listp) (wrld plist-worldp))
  :returns (mv erp (const-transunits symbolp) (value-fileset filesetp))
  :short "Process the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the file set constant name input,
     we retrieve and return the file set."))
  (b* (((reterr) nil (fileset nil))
       ;; Check and obtain options.
       ((mv erp extra options)
        (partition-rest-and-keyword-args args *parse-files-allowed-options*))
       ((when erp)
        (reterr (msg "The inputs must be the options ~&0, ~
                      but instead they are ~x1."
                     *parse-files-allowed-options*
                     args)))
       ((when extra)
        (reterr (msg "The only allowed inputs are the options ~&0, ~
                      but instead the extra inputs ~x1 were supplied."
                     *parse-files-allowed-options*
                     extra)))
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
       (value-fileset (acl2::constant-value const-fileset wrld))
       ((unless (filesetp value-fileset))
        (reterr (msg "The value of the ~x0 named constant ~
                      specified by the :CONST-FILESET input ~
                      must satisfy FILESETP, ~
                      but instead its value is ~x1."
                     const-fileset
                     value-fileset))))
    (retok const-transunits value-fileset))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-files-gen-defconst ((const-transunits symbolp)
                                  (value-fileset filesetp))
  :returns (mv erp (event pseudo-event-formp))
  :short "Generate the named constant event."
  (b* (((reterr) '(_))
       ((erp tunits) (parse-fileset value-fileset))
       (event `(defconst ,const-transunits ',tunits)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-files-process-inputs-and-gen-defconst ((args true-listp)
                                                     (wrld plist-worldp))
  :returns (mv erp
               (event pseudo-event-formp
                      :hints
                      (("Goal" :in-theory (disable pseudo-event-formp)))))
  :short "Process the inputs and generate the constant event."
  (b* (((reterr) '(_))
       ((erp const-transunits value-fileset)
        (parse-files-process-inputs args wrld))
       ((erp event)
        (parse-files-gen-defconst const-transunits value-fileset)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp event state)
  :short "Event expansion of @(tsee parse-files) from the inputs."
  (b* (((mv erp event)
        (parse-files-process-inputs-and-gen-defconst args (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection parse-files-definition
  :short "Definition of the @(tsee parse-files) macro."
  (defmacro parse-files (&rest args)
    `(make-event-terse (parse-files-fn ',args 'parse-files state))))
