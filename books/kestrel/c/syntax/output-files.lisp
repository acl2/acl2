; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "files")
(include-book "printer")

(include-book "kestrel/file-io-light/write-bytes-to-file-bang" :dir :system)
(include-book "std/system/constant-value" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)
(include-book "system/pseudo-event-formp" :dir :system)

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

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

(defxdoc+ output-files-implementation
  :parents (output-files)
  :short "Implementation of @(tsee output-files)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This also implements the programmatic interface @(tsee output-files-prog).
     The flag @('progp'), passed to some of the implementation functions below,
     says whether the programmatic interface has been called."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *output-files-allowed-options*
  :short "Keyword options accepted by @(tsee output-files)."
  (list :const
        :path
        :printer-options)
  ///
  (assert-event (keyword-listp *output-files-allowed-options*))
  (assert-event (no-duplicatesp-eq *output-files-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *output-files-printer-options*
  :short "Keyword options accepted in
          the @(':printer-options') of @(tsee output-files)."
  (list :indentation-size)
  ///
  (assert-event (keyword-listp *output-files-printer-options*))
  (assert-event (no-duplicatesp-eq *output-files-printer-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-const/arg (arg
                                        (options symbol-alistp)
                                        (progp booleanp)
                                        (wrld plist-worldp))
  :returns (mv erp
               (tunits transunit-ensemblep))
  :short "Process the @(':const') or @('arg') input."
  (b* (((reterr) (irr-transunit-ensemble))
       (const-option (assoc-eq :const options))
       ((erp tunits)
        (if progp
            (b* (((when const-option)
                  (reterr (msg "The :CONST input must not be supplied ~
                                to the programmatic interface."))))
              (retok arg))
          (b* (((unless const-option)
                (reterr (msg "The :CONST input must be supplied, ~
                              but it was not supplied.")))
               (const (cdr const-option))
               ((unless (symbolp const))
                (reterr (msg "The :CONST input must be a symbol, ~
                              but it is ~x0 instead."
                             const)))
               (tunits (acl2::constant-value const wrld)))
            (retok tunits))))
       (desc (if progp
                 "the required (i.e. non-keyword-option) input"
               (msg "the value of the ~x0 named constant, ~
                       specified by the :CONST input,"
                    (cdr const-option))))
       ((unless (transunit-ensemblep tunits))
        (reterr (msg "~@0 must be a translation unit ensemble, ~
                      but it is ~x1 instead."
                     desc tunits)))
       ((unless (transunit-ensemble-unambp tunits))
        (reterr (msg "The translation unit ensemble ~x0 passed as ~@1 ~
                      is ambiguous."
                     tunits desc))))
    (retok tunits))

  ///

  (defret transunit-ensemblep-when-output-files-process-tunits
    (implies (not erp)
             (transunit-ensemblep tunits)))

  (defret transunit-ensemble-unambp-when-output-files-process-tunits
    (implies (not erp)
             (transunit-ensemble-unambp tunits)))

  (in-theory
   (disable transunit-ensemblep-when-output-files-process-tunits
            transunit-ensemble-unambp-when-output-files-process-tunits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-printer-options ((options symbol-alistp))
  :returns (mv erp
               (indent-size posp)
               (paren-nested-conds booleanp))
  :short "Process the @(':printer-options') input."
  (b* (((reterr) 1 nil)
       (printer-options-option (assoc-eq :printer-options options))
       (printer-options (if printer-options-option
                            (cdr printer-options-option)
                          nil))
       ((unless (keyword-value-listp printer-options))
        (reterr (msg "The :PRINTER-OPTIONS input must be ~
                      a value-keyword list, ~
                      but it is ~x0 instead."
                     printer-options)))
       (printer-options-alist (keyword-value-list-to-alist printer-options))
       (printer-options-keywords (strip-cars printer-options-alist))
       ((unless (no-duplicatesp-eq printer-options-keywords))
        (reterr (msg "The list of keywords in the :PRINTER-OPTIONS input ~
                      must have no duplicates, ~
                      but the supplied :PRINTER-OPTIONS input ~x0 ~
                      violates that requirement."
                     printer-options)))
       ((unless (subsetp-eq printer-options-keywords
                            *output-files-printer-options*))
        (reterr (msg "The list of keywords in the :PRINTER-OPTIONS input ~
                      must be among ~&0, ~
                      but the supplied :PRINTER-OPTIONS input ~x0 ~
                      violates that requirement."
                     *output-files-printer-options*
                     printer-options)))
       ;; Process :INDENTATION-SIZE sub-input.
       (indent-size-option (assoc-eq :indentation-size
                                     printer-options-alist))
       (indent-size (if indent-size-option
                        (cdr indent-size-option)
                      2))
       ((unless (posp indent-size))
        (reterr (msg "The :INDENTATION-LEVEL option ~
                      of the :PRINTER-OPTIONS input ~
                      must be a positive integer, ~
                      but it is ~x0 instead."
                     indent-size)))
       ;; Process :PARENTHESIZE-NESTED-CONDITIONALS input.
       (paren-nested-conds-option (assoc-eq :parenthesize-nested-conditional
                                            printer-options-alist))
       (paren-nested-conds (if paren-nested-conds-option
                               (cdr paren-nested-conds-option)
                             nil))
       ((unless (booleanp paren-nested-conds))
        (reterr (msg "The :PARENTHESIZE-NESTED-CONDITIONALS option ~
                      of the :PRINTER-OPTIONS input ~
                      must be a boolean, ~
                      but it is ~x0 instead."
                     paren-nested-conds))))
    (retok indent-size paren-nested-conds)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-inputs (arg
                                     (args true-listp)
                                     (progp booleanp)
                                     (wrld plist-worldp))
  :guard (implies (not progp) (not arg))
  :returns (mv erp
               (tunits
                transunit-ensemblep
                :hints
                (("Goal"
                  :in-theory
                  (enable
                   transunit-ensemblep-when-output-files-process-tunits))))
               (path stringp)
               (indent-size posp)
               (paren-nested-conds booleanp))
  :short "Process the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('progp') is @('t'),
     @('arg') is the required (i.e. non-keyword-option) input
     of the macro that provides the programmatic interface;
     if instead @('progp') is @('nil'), @('arg') is @('nil').
     In all cases, @('args') are all the remaining inputs
     of the (event or programmatic) macro.")
   (xdoc::p
    "If @('progp') is @('nil'),
     the translation unit ensemble
     is taken from the @(':const') input, which must be present.
     If instead @('progp') is @('t'),
     the translation unit ensemble or file set
     is taken from the required input @('arg'),
     and the @(':const') input must be absent.")
   (xdoc::p
    "The @('tunits') result of this function is the translation unit ensemble.
     The other results are the homonymous inputs
     (some are sub-inputs of the @(':printer-options') input).")
   (xdoc::p
    "If the @(':path') string is not @('/') but ends with @('/'),
     we remove the ending @('/').
     This is for uniformity when concatenating this
     with the files specified in the @(':files') input."))
  (b* (((reterr) (irr-transunit-ensemble) "" 1 nil)
       ;; Check and obtain inputs.
       ((mv erp extra options)
        (partition-rest-and-keyword-args args *output-files-allowed-options*))
       (inputs-desc (msg "~s0the options ~&1"
                         (if progp
                             "a file set or translation unit ensemble and "
                           "")
                         *output-files-allowed-options*))
       ((when erp)
        (reterr (msg "The inputs must be ~@0, ~
                      but instead they are ~x1."
                     inputs-desc
                     args)))
       ((when extra)
        (reterr (msg "The inputs must be ~@0, ~
                      but instead the extra inputs ~x1 were supplied."
                     inputs-desc
                     extra)))
       ;; Process :CONST or ARG input.
       ((erp tunits) (output-files-process-const/arg arg options progp wrld))
       ;; Process :PATH input.
       (path-option (assoc-eq :path options))
       (path (if path-option
                 (cdr path-option)
               "."))
       ((unless (stringp path))
        (reterr (msg "The :PATH input must be a string, ~
                      but it is ~x0 instead."
                     path)))
       (path-chars (str::explode path))
       ((unless (consp path-chars))
        (reterr (msg "The :PATH input must be not empty, ~
                      but it is the empty string instead.")))
       (path-chars (if (and (consp (cdr path-chars))
                            (eql (car (last path-chars)) #\/))
                       (butlast path-chars 1)
                     path-chars))
       (path (str::implode path-chars))
       ;; Process :PRINTER-OPTIONS input.
       ((erp indent-size paren-nested-conds)
        (output-files-process-printer-options options)))
    (retok tunits
           path
           indent-size
           paren-nested-conds))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp
                                           msgp
                                           character-alistp)))

  ///

  (defret transunit-ensemble-unambp-of-output-files-process-inputs
    (implies (not erp)
             (transunit-ensemble-unambp tunits))
    :hints
    (("Goal"
      :in-theory
      (enable
       transunit-ensemble-unambp-when-output-files-process-tunits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-gen-files ((tunits transunit-ensemblep)
                                (path stringp)
                                (indent-size posp)
                                (paren-nested-conds booleanp)
                                state)
  :guard (transunit-ensemble-unambp tunits)
  :returns (mv erp state)
  :short "Generate the files."
  (b* (((reterr) state)
       ;; Print the abstract syntax.
       (options (make-priopt :indent-size indent-size
                             :paren-nested-conds paren-nested-conds))
       (files (print-fileset tunits options))
       ;; Write the files to the file system.
       ((erp state)
        (output-files-gen-files-loop (fileset->unwrap files) path state)))
    (retok state))
  :prepwork
  ((define output-files-gen-files-loop ((map filepath-filedata-mapp)
                                        (path stringp)
                                        state)
     :returns (mv erp state)
     :parents nil
     (b* (((reterr) state)
          ((when (omap::emptyp map)) (retok state))
          ((mv filepath data) (omap::head map))
          (file-string (filepath->unwrap filepath))
          ((unless (stringp file-string))
           (reterr (msg "File path must contain a string, ~
                         but it contains ~x0 instead."
                        file-string)))
          (path-to-write (str::cat path "/" file-string))
          ((mv erp state) (acl2::write-bytes-to-file! (filedata->unwrap data)
                                                      path-to-write
                                                      'output-files
                                                      state))
          ((when erp)
           (reterr (msg "Writing ~x0 failed." path-to-write))))
       (output-files-gen-files-loop (omap::tail map) path state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-inputs-and-gen-files (arg
                                                   (args true-listp)
                                                   (progp booleanp)
                                                   state)
  :guard (implies (not progp) (not arg))
  :returns (mv erp state)
  :short "Process the inputs and generate the files."
  (b* (((reterr) state)
       ((erp tunits
             path
             indent-size
             paren-nested-conds)
        (output-files-process-inputs arg args progp (w state)))
       ((erp state)
        (output-files-gen-files tunits
                                path
                                indent-size
                                paren-nested-conds
                                state)))
    (retok state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee output-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp) for the programmatic interface to @('nil')."))
  (b* (((mv erp state)
        (output-files-process-inputs-and-gen-files nil args nil state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value '(value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection output-files-definition
  :short "Definition of the @(tsee output-files) macro."
  (defmacro output-files (&rest args)
    `(make-event-terse
      (output-files-fn ',args 'output-files state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-files-prog
  :parents (output-files)
  :short "Programmatic interface to @(tsee output-files)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This (non-event) macro provides
     a programmatic interface to the functionality of @(tsee output-files).
     It has the form:")
   (xdoc::codeblock
    "(output-files-prog tunits"
    "                   :path            ...  ; default \".\""
    "                   :printer-options ...  ; default nil"
    "  )")
   (xdoc::p
    "This is the same as @(tsee output-files),
     except that there is no @(':const') input,
     and there is a required (i.e. non-keyword-option) input
     which must be the translation unit ensemble.
     This macro writes the files,
     and returns an "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuple")
    " consisting of @('state'), i.e. the ACL2 @(see state).")
   (xdoc::p
    "Note that the macro implicitly takes @(tsee state),
     so it must be used in a context where @(tsee state) is available."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-prog-fn (arg (args true-listp) state)
  :returns (mv erp state)
  :short "Implementation of @(tsee output-files-prog)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp') for the programmatic interface to @('t').
     We ignore the event returned as result,
     and instead return the file set."))
  (b* (((reterr) state)
       ((erp state)
        (output-files-process-inputs-and-gen-files arg args t state)))
    (retok state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection output-files-prog-definition
  :short "Definition of the @(tsee output-files-prog) macro."
  (defmacro output-files-prog (arg &rest args)
    `(output-files-prog-fn ,arg ',args state)))
