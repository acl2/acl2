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

(define tunitens/fileset-p (x)
  :returns (yes/no booleanp)
  :parents (transunit-ensemblep filesetp)
  :short "Recognize a translation unit ensemble or a file set."
  (or (transunit-ensemblep x)
      (filesetp x))

  ///

  (defruled tunitens/fileset-p-when-transunit-ensemblep
    (implies (transunit-ensemblep x)
             (tunitens/fileset-p x)))

  (defruled tunitens/fileset-p-when-filesetp
    (implies (filesetp x)
             (tunitens/fileset-p x))))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tunitens/fileset
  :short "An irrelevant translation unit ensemble or file set."
  :type tunitens/fileset-p
  :body (irr-transunit-ensemble))

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
        :process
        :const-files
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

(define output-files-process-inputp (x)
  :returns (yes/no booleanp)
  :short "Recognize valid values of the @(':process') input."
  (and (member-eq x '(:write :print)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-tunits/files (tunits/files
                                           (process output-files-process-inputp)
                                           (desc msgp))
  :returns erp
  :short "Process the input translation unit ensemble or file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be a file set
     if @(':process') is @(':write'),
     or an unambiguous translation unit ensemble
     if @(':process') is @(':print')."))
  (b* (((reterr)))
    (case process
      (:write
       (b* (((unless (filesetp tunits/files))
             (reterr (msg "Since the :PROCESS input is :WRITE, ~
                           ~@0 must be a file set, ~
                           but it is ~x1 instead."
                          desc
                          tunits/files))))
         (retok)))
      (:print
       (b* (((unless (transunit-ensemblep tunits/files))
             (reterr (msg "Since the :PROCESS input is :PRINT, ~
                           ~@0 must be a translation unit ensemble, ~
                           but it is ~x1 instead."
                          desc tunits/files)))
            ((unless (transunit-ensemble-unambp tunits/files))
             (reterr (msg "The translation unit ensemble ~x0 passed as ~@1 ~
                           is ambiguous."
                          tunits/files desc))))
         (retok)))
      (t (prog2$ (impossible) (reterr t)))))
  :guard-hints (("Goal" :in-theory (enable output-files-process-inputp)))

  ///

  (defret transunit-ensemblep-when-output-files-process-tunits/files
    (implies (and (not erp)
                  (equal process :print))
             (transunit-ensemblep tunits/files)))

  (defret transunit-ensemble-unambp-when-output-files-process-tunits/files
    (implies (and (not erp)
                  (equal process :print))
             (transunit-ensemble-unambp tunits/files)))

  (defret filesetp-when-output-files-process-tunits/files
    (implies (and (not erp)
                  (equal process :write))
             (filesetp tunits/files)))

  (in-theory
   (disable transunit-ensemblep-when-output-files-process-tunits/files
            transunit-ensemble-unambp-when-output-files-process-tunits/files
            filesetp-when-output-files-process-tunits/files)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-inputs (arg
                                     (args true-listp)
                                     (progp booleanp)
                                     (wrld plist-worldp))
  :guard (implies (not progp) (not arg))
  :returns (mv erp
               (tunits/files
                tunitens/fileset-p
                :hints
                (("Goal"
                  :in-theory
                  (enable
                   output-files-process-inputp
                   tunitens/fileset-p-when-transunit-ensemblep
                   tunitens/fileset-p-when-filesetp
                   transunit-ensemblep-when-output-files-process-tunits/files
                   filesetp-when-output-files-process-tunits/files))))
               (process output-files-process-inputp)
               (const-files symbolp)
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
     the translation unit ensemble or file set
     is taken from the @(':const') input, which must be present.
     If instead @('progp') is @('t'),
     the translation unit ensemble or file set
     is taken from the required input @('arg'),
     and the @(':const') input must be absent;
     the @(':const-files') input must be absent too.")
   (xdoc::p
    "The @('tunits/files') result of this function is
     the translation unit ensemble or file set.
     The other results are the homonymous inputs
     (some are sub-inputs of the @(':printer-options') input);
     if @('progp') is @('t'), the @('const-files') result is @('nil')."))
  (b* (((reterr) (irr-tunitens/fileset) :write nil 1 nil)
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
       ;; Process :PROCESS input.
       (process-option (assoc-eq :process options))
       (process (if process-option
                    (cdr process-option)
                  :print))
       ((unless (output-files-process-inputp process))
        (reterr (msg "The :PROCESS input must be :WRITE or :PRINT, ~
                      but it ~x0 instead."
                     process)))
       ;; Process :CONST or ARG input.
       (const-option (assoc-eq :const options))
       ((erp tunits/files)
        (b* (((reterr) (irr-tunitens/fileset)))
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
                 (tunits/files (acl2::constant-value const wrld)))
              (retok tunits/files)))))
       ((erp) (output-files-process-tunits/files
               tunits/files
               process
               (if progp
                   "the required (i.e. non-keyword-option) input"
                 (msg "the value of the ~x0 named constant, ~
                       specified by the :CONST input,"
                      (cdr const-option)))))
       ;; Process :CONST-FILES input.
       (const-files-option (assoc-eq :const-files options))
       ((erp const-files)
        (b* (((reterr) nil))
          (if progp
              (b* (((when const-files-option)
                    (reterr (msg "The :CONST-FILES input must not be supplied ~
                                  to the programmatic interface."))))
                (retok nil))
            (b* ((const-files (if const-files-option
                                  (cdr const-files-option)
                                nil))
                 ((unless (symbolp const-files))
                  (reterr (msg "The :CONST-FILES input must be a symbol, ~
                                but it is ~x0 instead."
                               const-files)))
                 ((when (and const-files
                             (not process)))
                  (reterr (msg "The :CONST-FILES input must be NIL ~
                                if the :PROCESS input is NIL, ~
                                which is the case ~
                                in this call of OUTPUT-FILES."))))
              (retok const-files)))))
       ;; Process :PRINTER-OPTIONS input.
       (printer-options-option (assoc-eq :printer-options options))
       (printer-options (if printer-options-option
                            (cdr printer-options-option)
                          nil))
       ((unless (keyword-value-listp printer-options))
        (reterr (msg "The :PRINTER-OPTIONS input must be ~
                      a value-keyword list, ~
                      but it is ~x0 instead."
                     printer-options)))
       ((when (and (not (eq process :print))
                   (consp printer-options)))
        (reterr (msg "Since the :PROCESS input is not :PRINT, ~
                      the :PRINTER-OPTIONS input must be NIL, ~
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
    (retok tunits/files
           process
           const-files
           indent-size
           paren-nested-conds))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp
                                           msgp
                                           character-alistp)))

  ///

  (defret transunit-ensemblep-of-output-files-process-inputs
    (implies (and (not erp)
                  (equal process :print))
             (transunit-ensemblep tunits/files))
    :hints (("Goal"
             :in-theory
             (enable
              transunit-ensemblep-when-output-files-process-tunits/files))))

  (defret transunit-ensemble-unamp-of-output-files-process-inputs
    (implies (and (not erp)
                  (equal process :print))
             (transunit-ensemble-unambp tunits/files))
    :hints
    (("Goal"
      :in-theory
      (enable
       transunit-ensemble-unambp-when-output-files-process-tunits/files))))

  (defret filesetp-of-output-files-process-inputs
    (implies (and (not erp)
                  (equal process :write))
             (filesetp tunits/files))
    :hints
    (("Goal"
      :in-theory (enable filesetp-when-output-files-process-tunits/files)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-gen-files+events ((tunits/files tunitens/fileset-p)
                                       (process output-files-process-inputp)
                                       (const-files symbolp)
                                       (indent-size posp)
                                       (paren-nested-conds booleanp)
                                       (progp booleanp)
                                       state)
  :guard (and (implies (equal process :write)
                       (filesetp tunits/files))
              (implies (equal process :print)
                       (and (transunit-ensemblep tunits/files)
                            (transunit-ensemble-unambp tunits/files))))
  :returns (mv erp
               (events pseudo-event-form-listp)
               (files filesetp)
               state)
  :short "Generate the files and (if any) the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "If required, we print the translation unit ensemble to a file set;
     if required, we also generate the constant for the file set.
     Then we go through the file set
     and write the data of each value in the map
     to the path of the associated key in the map.")
   (xdoc::p
    "We also return the file set that is
     either the same as the input (if @(':process') is @(':write')),
     or the result of printing (if @(':process') is @(':print'))."))
  (b* (((reterr) nil (irr-fileset) state)
       ;; Initialize list of generated events.
       (events nil)
       ;; Print the abstract syntax if required.
       (files (if (eq process :print)
                  (b* ((options (make-priopt
                                 :indent-size indent-size
                                 :paren-nested-conds paren-nested-conds)))
                    (print-fileset tunits/files options))
                (fileset-fix tunits/files)))
       ;; Generate :CONST-FILES if required.
       (events (if (and const-files
                        (not progp))
                   (cons `(defconst ,const-files ',files) events)
                 events))
       ;; Write the files to the file system.
       ((erp state) (output-files-gen-files (fileset->unwrap files) state)))
    (retok events files state))
  :guard-hints (("Goal" :in-theory (enable output-files-process-inputp)))

  :prepwork
  ((define output-files-gen-files ((map filepath-filedata-mapp) state)
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
                                                      'output-files
                                                      state))
          ((when erp)
           (reterr (msg "Writing ~x0 failed." path-string))))
       (output-files-gen-files (omap::tail map) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-process-inputs-and-gen-files+events (arg
                                                          (args true-listp)
                                                          (progp booleanp)
                                                          state)
  :guard (implies (not progp) (not arg))
  :returns (mv erp
               (event pseudo-event-formp)
               (files filesetp)
               state)
  :short "Process the inputs and generate the constant event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The event is an empty @(tsee progn) if
     this is called via the programmatic interface.
     We also return the file set that is
     either passed as input or the result of prining,
     depending on @(':process'),
     for use by the programmatic interface."))
  (b* (((reterr) '(_) (irr-fileset) state)
       ((erp tunits/files
             process
             const-files
             indent-size
             paren-nested-conds)
        (output-files-process-inputs arg args progp (w state)))
       ((erp events files state)
        (output-files-gen-files+events tunits/files
                                       process
                                       const-files
                                       indent-size
                                       paren-nested-conds
                                       progp
                                       state)))
    (retok `(progn ,@events) files state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee output-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp) for the programmatic interface to @('nil').
     We ignore the file set returned as additional result."))
  (b* (((mv erp event & state)
        (output-files-process-inputs-and-gen-files+events nil args nil state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

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
    "(output-files-prog tunits/files"
    "                   :process         ...  ; default :print"
    "                   :printer-options ...  ; default nil"
    "  )")
   (xdoc::p
    "This is the same as @(tsee output-files),
     except that there are not inputs for the constant names,
     because this macro does not generate any events,
     and there is a required (i.e. non-keyword-option) input
     which must be the translation unit ensemble or file set
     (depending on the @(':process') input.
     This macro writes the files,
     and returns an "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuple")
    " consisting of:")
   (xdoc::ul
    (xdoc::li
     "@('files'):
      the @(tsee fileset) that is
      either the same as the @('tunits/files') input
      (if @(':process') is @(':write'))
      or the result of printing the @('tunits/files') input
      (if @(':process') is @(':print')).")
    (xdoc::li
     "@('state'):
      the ACL2 @(see state)."))
   (xdoc::p
    "Note that the macro implicitly takes @(tsee state),
     so it must be used in a context where @(tsee state) is available."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-files-prog-fn (arg (args true-listp) state)
  :returns (mv erp (files filesetp) state)
  :short "Implementation of @(tsee output-files-prog)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp') for the programmatic interface to @('t').
     We ignore the event returned as result,
     and instead return the file set."))
  (b* (((reterr) (irr-fileset) state)
       ((erp & files state)
        (output-files-process-inputs-and-gen-files+events arg args t state)))
    (retok files state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection output-files-prog-definition
  :short "Definition of the @(tsee output-files-prog) macro."
  (defmacro output-files-prog (arg &rest args)
    `(output-files-prog-fn ,arg ',args state)))
