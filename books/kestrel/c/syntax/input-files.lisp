; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocess-file")
(include-book "parser")
(include-book "disambiguator")
(include-book "validator")

(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/pseudo-event-form-listp" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl byte-listp-becomes-unsigned-byte-listp-8
  (equal (byte-listp x)
         (unsigned-byte-listp 8 x))
  :enable (unsigned-byte-listp
           byte-listp
           bytep)
  :induct (byte-listp x))

;;;;;;;;;;;;;;;;;;;;

(defrulel byte-listp-of-read-file-into-byte-list
  (byte-listp (mv-nth 1 (acl2::read-file-into-byte-list filename state)))
  :enable (byte-listp-becomes-unsigned-byte-listp-8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-files-implementation
  :parents (input-files)
  :short "Implementation of @(tsee input-files)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This also implements the programmatic interface @(tsee input-files-prog).
     The flag @('progp'), passed to some of the implementation functions below,
     says whether the programmatic interface has been called."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *input-files-allowed-options*
  :short "Keyword options accepted by @(tsee input-files)."
  (list :files
        :preprocess
        :process
        :const
        :const-files
        :const-preproc
        :const-parsed
        :const-disamb
        :gcc
        :short-bytes
        :int-bytes
        :long-bytes
        :long-long-bytes
        :plain-char-signed)
  ///
  (assert-event (keyword-listp *input-files-allowed-options*))
  (assert-event (no-duplicatesp-eq *input-files-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-strings-to-paths ((strings string-listp))
  :returns (paths filepath-setp)
  :short "Turn a list of strings into a set of file paths."
  (cond ((endp strings) nil)
        (t (set::insert (filepath (car strings))
                        (input-files-strings-to-paths (cdr strings)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-preprocess-inputp (x)
  :returns (yes/no booleanp)
  :short "Recognize valid values of the @(':preprocess') input."
  (or (not x)
      (eq x :auto)
      (stringp x)))

;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputp (x)
  :returns (yes/no booleanp)
  :short "Recognize valid values of the @(':process') input."
  (and (member-eq x '(:read :parse :disambiguate :validate)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-files ((options symbol-alistp))
  :returns (mv erp (paths filepath-setp))
  :short "Process the @(':files') input."
  (b* (((reterr) nil)
       (files-option (assoc-eq :files options))
       ((unless files-option)
        (reterr (msg "The :FILES input must be supplied, ~
                      but it was not supplied.")))
       (files (cdr files-option))
       ((unless (string-listp files))
        (reterr (msg "The :FILES input must be a list of strings, ~
                      but it is ~x0 instead."
                     files)))
       ((unless (no-duplicatesp-equal files))
        (reterr (msg "The :FILES input must be a list without duplicates, ~
                      but the supplied ~x0 has duplicates."
                     files)))
       (paths (input-files-strings-to-paths files)))
    (retok paths)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-preprocess ((options symbol-alistp))
  :returns (mv erp
               (preprocessor string-optionp
                             :hints
                             (("Goal"
                               :in-theory
                               (enable input-files-preprocess-inputp)))))
  :short "Process the @(':preprocess') input."
  (b* (((reterr) nil)
       (preprocess-option (assoc-eq :preprocess options))
       (preprocess (if preprocess-option
                       (cdr preprocess-option)
                     nil))
       ((unless (input-files-preprocess-inputp preprocess))
        (reterr (msg "The :PREPROCESS input must be NIL, :AUTO, or a string, ~
                      but it is ~x0 instead."
                     preprocess)))
       (preprocessor (if (eq preprocess :auto)
                         "cpp"
                       preprocess)))
    (retok preprocessor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-process ((options symbol-alistp))
  :returns (mv erp (process input-files-process-inputp))
  :short "Process the @(':process') input."
  (b* (((reterr) :read)
       (process-option (assoc-eq :process options))
       (process (if process-option
                    (cdr process-option)
                  :validate))
       ((unless (input-files-process-inputp process))
        (reterr (msg "The :PROCESS input must be ~
                      :READ, :PARSE, :DISAMBIGUATE, or :VALIDATE ~
                      but it is ~x0 instead."
                     process))))
    (retok process)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-const-inputs ((options symbol-alistp)
                                          (preprocess string-optionp)
                                          (process input-files-process-inputp)
                                          (progp booleanp))
  :returns (mv erp
               (const symbolp)
               (const-files symbolp)
               (const-preproc symbolp)
               (const-parsed symbolp)
               (const-disamb symbolp))
  :short "Process the
          @(':const'),
          @(':const-files'),
          @(':const-preproc'),
          @(':const-parsed'), and
          @(':const-disamb')
          inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the programmatic interface has been called,
     none of these inputs may be present.
     In this case, we return @('nil') results for all of them."))
  (b* (((reterr) nil nil nil nil nil)
       ;; Retrieve the options and handle the programmatic interface.
       (const-option (assoc-eq :const options))
       (const-files-option (assoc-eq :const-files options))
       (const-preproc-option (assoc-eq :const-preproc options))
       (const-parsed-option (assoc-eq :const-parsed options))
       (const-disamb-option (assoc-eq :const-disamb options))
       ((when progp)
        (b* (((when const-option)
              (reterr (msg "The :CONST input must not be supplied ~
                            to the programmatic interface.")))
             ((when const-files-option)
              (reterr (msg "The :CONST-FILES input must not be supplied ~
                            to the programmatic interface.")))
             ((when const-preproc-option)
              (reterr (msg "The :CONST-PREPROC input must not be supplied ~
                            to the programmatic interface.")))
             ((when const-parsed-option)
              (reterr (msg "The :CONST-PARSED input must not be supplied ~
                            to the programmatic interface.")))
             ((when const-disamb-option)
              (reterr (msg "The :CONST-DISAMB input must not be supplied ~
                            to the programmatic interface."))))
          (retok nil nil nil nil nil)))
       ;; Process :CONST input.
       ((unless const-option)
        (reterr (msg "The :CONST input must be supplied, ~
                      but it was not supplied.")))
       (const (cdr const-option))
       ((unless (symbolp const))
        (reterr (msg "The :CONST input must be a symbol, ~
                      but it is ~x0 instead."
                     const)))
       ;; Process :CONST-FILES input.
       (const-files (if const-files-option
                        (cdr const-files-option)
                      nil))
       ((unless (symbolp const-files))
        (reterr (msg "The :CONST-FILES input must be a symbol, ~
                      but it is ~x0 instead."
                     const-files)))
       ((when (and const-files
                   (not preprocess)
                   (eq process :read)))
        (reterr (msg "The :CONST-FILES input must be NIL ~
                      if the :PREPROCESS input is NIL ~
                      and the :PROCESS input is :READ, ~
                      which is the case in this call of INPUT-FILES.")))
       ;; Process :CONST-PREPROC input.
       (const-preproc (if const-preproc-option
                          (cdr const-preproc-option)
                        nil))
       ((unless (symbolp const-preproc))
        (reterr (msg "The :CONST-PREPROC input must be a symbol, ~
                      but it is ~x0 instead."
                     const-preproc)))
       ((when (and const-preproc
                   (not preprocess)))
        (reterr (msg "The :CONST-PREPROC input must be NIL ~
                      if the :PREPROCESS input is NIL, ~
                      which is the case in this call of INPUT-FILES.")))
       ;; Process :CONST-PARSED input.
       (const-parsed (if const-parsed-option
                         (cdr const-parsed-option)
                       nil))
       ((unless (symbolp const-parsed))
        (reterr (msg "The :CONST-PARSED input must be a symbol, ~
                      but it is ~x0 instead."
                     const-parsed)))
       ((when (and const-parsed
                   (eq process :read)))
        (reterr (msg "The :CONST-PARSED input must be NIL ~
                      if the :PROCESS input is :READ, ~
                      which is the case in this call of INPUT-FILES.")))
       ((when (and const-parsed
                   (eq process :parse)))
        (reterr (msg "The :CONST-PARSED input must be NIL ~
                      if the :PROCESS input is :PARSE, ~
                      which is the case in this call of INPUT-FILES.")))
       ;; Process :CONST-DISAMB input.
       (const-disamb (if const-disamb-option
                         (cdr const-disamb-option)
                       nil))
       ((unless (symbolp const-disamb))
        (reterr (msg "The :CONST-DISAMB input must be a symbol, ~
                      but it is ~x0 instead."
                     const-disamb)))
       ((when (and const-disamb
                   (eq process :read)))
        (reterr (msg "The :CONST-DISAMB input must be NIL ~
                      if the :PROCESS input is :READ, ~
                      which is the case in this call of INPUT-FILES.")))
       ((when (and const-disamb
                   (eq process :parse)))
        (reterr (msg "The :CONST-DISAMB input must be NIL ~
                      if the :PROCESS input is :PARSE, ~
                      which is the case in this call of INPUT-FILES.")))
       ((when (and const-disamb
                   (eq process :disambiguate)))
        (reterr (msg "The :CONST-DISAMB input must be NIL ~
                      if the :PROCESS input is :DISAMBIGUATE, ~
                      which is the case in this call of INPUT-FILES."))))
    (retok const const-files const-preproc const-parsed const-disamb)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-gcc ((options symbol-alistp))
  :returns (mv erp (gcc booleanp))
  :short "Process the @(':gcc') input."
  (b* (((reterr) nil)
       (gcc-option (assoc-eq :gcc options))
       (gcc (if gcc-option
                (cdr gcc-option)
              nil))
       ((unless (booleanp gcc))
        (reterr (msg "The :GCC input must be a boolean, ~
                      but it is ~x0 instead."
                     gcc))))
    (retok gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-ienv ((options symbol-alistp))
  :returns (mv erp (ienv ienvp))
  :short "Process the
          @(':short-bytes'),
          @(':int-bytes'),
          @(':long-bytes'),
          @(':long-long-bytes'),
          @(':plain-char-signed')
          inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the inputs that define the implementation environment,
     which we return if the processing of these inputs is successful."))
  (b* (((reterr) (ienv-default))
       ;; Process :SHORT-BYTES input.
       (short-bytes-option (assoc-eq :short-bytes options))
       (short-bytes (if short-bytes-option
                        (cdr short-bytes-option)
                      2))
       ((unless (and (integerp short-bytes)
                     (>= short-bytes 2)))
        (reterr (msg "The :SHORT-BYTES input must be ~
                      an integer greater than or equal to 2, ~
                      but it is ~x0 instead."
                     short-bytes)))
       ;; Process :INT-BYTES input.
       (int-bytes-option (assoc-eq :int-bytes options))
       (int-bytes (if int-bytes-option
                      (cdr int-bytes-option)
                    4))
       ((unless (and (integerp int-bytes)
                     (>= int-bytes 4)
                     (>= int-bytes short-bytes)))
        (reterr (msg "The :INT-BYTES input must be ~
                      an integer greater than or equal to 4, ~
                      and greater than or equal to ~
                      the value ~x0 of :SHORT-BYTES, ~
                      but it is ~x1 instead."
                     short-bytes int-bytes)))
       ;; Process :LONG-BYTES input.
       (long-bytes-option (assoc-eq :long-bytes options))
       (long-bytes (if long-bytes-option
                       (cdr long-bytes-option)
                     8))
       ((unless (and (integerp long-bytes)
                     (>= long-bytes 8)
                     (>= long-bytes int-bytes)))
        (reterr (msg "The :LONG-BYTES input must be ~
                      an integer greater than or equal to 8, ~
                      and greater than or equal to ~
                      the value ~x0 of :INT-BYTES, ~
                      but it is ~x1 instead."
                     int-bytes long-bytes)))
       ;; Process :LONG-LONG-BYTES input.
       (long-long-bytes-option (assoc-eq :long-long-bytes options))
       (long-long-bytes (if long-long-bytes-option
                            (cdr long-long-bytes-option)
                          8))
       ((unless (and (integerp long-long-bytes)
                     (>= long-long-bytes 8)
                     (>= long-long-bytes long-bytes)))
        (reterr (msg "The :LONG-LONG-BYTES input must be ~
                      an integer greater than or equal to 8, ~
                      and greater than or equal to ~
                      the value ~x0 of :LONG-BYTES, ~
                      but it is ~x1 instead."
                     long-bytes long-long-bytes)))
       ;; Process :PLAIN-CHAR-SIGNED input.
       (plain-char-signed-option (assoc-eq :plain-char-signed options))
       (plain-char-signed (if plain-char-signed-option
                              (cdr plain-char-signed-option)
                            nil))
       ((unless (booleanp plain-char-signed))
        (reterr (msg "The :PLAIN-CHAR-SIGNED input must be a boolean, ~
                      but it is ~x0 instead."
                     plain-char-signed)))
       ;; Build the implementation environment.
       (ienv (make-ienv :short-bytes short-bytes
                        :int-bytes int-bytes
                        :long-bytes long-bytes
                        :llong-bytes long-long-bytes
                        :plain-char-signedp plain-char-signed)))
    (retok ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs ((args true-listp) (progp booleanp))
  :returns (mv erp
               (paths filepath-setp)
               (preprocessor string-optionp)
               (process input-files-process-inputp)
               (const symbolp)
               (const-files symbolp)
               (const-preproc symbolp)
               (const-parsed symbolp)
               (const-disamb symbolp)
               (gcc booleanp)
               (ienv ienvp))
  :short "Process the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('paths') result of this function
     is calculated from the @(':files') input.")
   (xdoc::p
    "The @('preprocessor') result of this function
     is calculated from the @(':preprocess') input.
     The use of `preprocessor' vs. `preprocess' is intentional.")
   (xdoc::p
    "The other results of this function are the homonymous inputs,
     except that the last five inputs are combined into
     an implementation environment result."))
  (b* (((reterr) nil nil :read nil nil nil nil nil nil (ienv-default))
       ;; Check and obtain inputs.
       ((mv erp extra options)
        (partition-rest-and-keyword-args
         args *input-files-allowed-options*))
       ((when erp)
        (reterr (msg "The inputs must be the options ~&0, ~
                      but instead they are ~x1."
                     *input-files-allowed-options*
                     args)))
       ((when extra)
        (reterr (msg "The only allowed inputs are the options ~&0, ~
                      but instead the extra inputs ~x1 were supplied."
                     *input-files-allowed-options*
                     extra)))
       ;; Process the inputs.
       ((erp paths) (input-files-process-files options))
       ((erp preprocessor) (input-files-process-preprocess options))
       ((erp process) (input-files-process-process options))
       ((erp const const-files const-preproc const-parsed const-disamb)
        (input-files-process-const-inputs options preprocessor process progp))
       ((erp gcc) (input-files-process-gcc options))
       ((erp ienv) (input-files-process-ienv options)))
    (retok paths
           preprocessor
           process
           const
           const-files
           const-preproc
           const-parsed
           const-disamb
           gcc
           ienv))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-read-files ((paths filepath-setp) state)
  :returns (mv erp (fileset filesetp) state)
  :short "Read a file set from a given set of paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each path,
     and we attempt to read the file at each path,
     constructing the file set along the way."))
  (b* (((reterr) (fileset nil) state)
       ((when (set::emptyp paths)) (retok (fileset nil) state))
       (path (set::head paths))
       (path-string (filepath->unwrap path))
       ((unless (stringp path-string))
        (raise "Internal error: file path ~x0 is not a string." path-string)
        (reterr t))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list (filepath->unwrap path) state))
       ((when erp)
        (reterr (msg "Reading ~x0 failed." (filepath->unwrap path))))
       (data (filedata bytes))
       ((erp fileset state)
        (input-files-read-files (set::tail paths) state)))
    (retok (fileset (omap::update path data (fileset->unwrap fileset)))
           state))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-gen-events ((paths filepath-setp)
                                (preprocessor string-optionp)
                                (process input-files-process-inputp)
                                (const symbolp)
                                (const-files symbolp)
                                (const-preproc symbolp)
                                (const-parsed symbolp)
                                (const-disamb symbolp)
                                (gcc booleanp)
                                (ienv ienvp)
                                (progp booleanp)
                                state)
  :returns (mv erp
               (events pseudo-event-form-listp)
               (read-files filesetp)
               (preproc-files filesetp)
               (parsed-tuens transunit-ensemblep)
               (disamb-tuens transunit-ensemblep)
               (valid-tuens transunit-ensemblep)
               state)
  :short "Generate the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform all the necessary preprocessing and processing.
     Besides the events, we also return the artifacts at all stages,
     as additional results, for use by the programmatic interface;
     if an artifact at some stage is not actually calculated
     (e.g. the @(':process') input is not @(':validate')),
     we return an irrelevant value for it as result.
     If the programmatic interface is being used,
     no events are actually generated."))
  (b* ((irr-fileset (fileset nil))
       ((reterr)
        nil
        irr-fileset
        irr-fileset
        (irr-transunit-ensemble)
        (irr-transunit-ensemble)
        (irr-transunit-ensemble)
        state)
       ;; Initialize list of generated events.
       (events nil)
       ;; Read files from file system.
       ((erp read-files state) (input-files-read-files paths state))
       ;; Generate :CONST-FILE constant if required.
       (events (if (and const-files
                        (not progp))
                   (rcons `(defconst ,const-files ',read-files) events)
                 events))
       ;; Preprocess if required;
       ;; either way, after this, FILES contains the files to process.
       ((erp files state) (if preprocessor
                              (preprocess-files paths
                                                :preprocessor preprocessor)
                            (retok read-files state)))
       (preproc-files (if preprocessor files irr-fileset))
       ;; Generate :CONST-PREPROC if required.
       (events (if (and const-preproc
                        (not progp))
                   (rcons `(defconst ,const-preproc ',files) events)
                 events))
       ;; If no processing is required, we are done;
       ;; generate :CONST constant with the files.
       ((when (eq process :read))
        (b* ((events (if (not progp)
                         (rcons `(defconst ,const ',files) events)
                       events)))
          (retok events
                 read-files
                 preproc-files
                 (irr-transunit-ensemble)
                 (irr-transunit-ensemble)
                 (irr-transunit-ensemble)
                 state)))
       ;; At least parsing is required.
       ((erp parsed-tuens) (parse-fileset files gcc))
       ;; Generate :CONST-PARSED constant if required.
       (events (if (and const-parsed
                        (not progp))
                   (rcons `(defconst ,const-parsed ',parsed-tuens) events)
                 events))
       ;; If only parsing is required, we are done;
       ;; generate :CONST constant with the parsed translation units.
       ((when (eq process :parse))
        (b* ((events (if (not progp)
                         (rcons `(defconst ,const ',parsed-tuens) events)
                       events)))
          (retok events
                 read-files
                 preproc-files
                 parsed-tuens
                 (irr-transunit-ensemble)
                 (irr-transunit-ensemble)
                 state)))
       ;; Disambiguation is required.
       ((erp disamb-tuens) (dimb-transunit-ensemble parsed-tuens gcc))
       ;; Generate :CONST-DISAMB constant if required.
       (events (if (and const-disamb
                        (not progp))
                   (rcons `(defconst ,const-disamb ',disamb-tuens) events)
                 events))
       ;; If no validation is required, we are done;
       ;; generate :CONST constant with the disambiguated translation unit.
       ((when (eq process :disambiguate))
        (b* ((events (if (not progp)
                         (rcons `(defconst ,const ',disamb-tuens) events)
                       events)))
          (retok events
                 read-files
                 preproc-files
                 parsed-tuens
                 disamb-tuens
                 (irr-transunit-ensemble)
                 state)))
       ;; Validation is required.
       ((erp valid-tuens) (valid-transunit-ensemble disamb-tuens gcc ienv))
       ;; Generate :CONST constant with the validated translation unit.
       (events (if (not progp)
                   (rcons `(defconst ,const ',valid-tuens) events)
                 events)))
    (retok events
           read-files
           preproc-files
           parsed-tuens
           disamb-tuens
           valid-tuens
           state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs-and-gen-events ((args true-listp)
                                                   (progp booleanp)
                                                   state)
  :returns (mv erp
               (event pseudo-event-formp)
               (read-files filesetp)
               (preproc-files filesetp)
               (parsed-tuens transunit-ensemblep)
               (disamb-tuens transunit-ensemblep)
               (valid-tuens transunit-ensemblep)
               state)
  :short "Process the inputs and generate the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The event is an empty @(tsee progn) if
     this is called via the programmatic interface.
     We also return the artifacts at all the applicable stages,
     for use by the programmatic interface."))
  (b* ((irr-fileset (fileset nil))
       ((reterr)
        '(_)
        irr-fileset
        irr-fileset
        (irr-transunit-ensemble)
        (irr-transunit-ensemble)
        (irr-transunit-ensemble)
        state)
       ((erp paths
             preprocessor
             process
             const
             const-files
             const-preproc
             const-parsed
             const-disamb
             gcc
             ienv)
        (input-files-process-inputs args progp))
       ((erp events
             read-files
             preproc-files
             parsed-tuens
             disamb-tuens
             valid-tuens
             state)
        (input-files-gen-events paths
                                preprocessor
                                process
                                const
                                const-files
                                const-preproc
                                const-parsed
                                const-disamb
                                gcc
                                ienv
                                progp
                                state)))
    (retok `(progn ,@events)
           read-files
           preproc-files
           parsed-tuens
           disamb-tuens
           valid-tuens
           state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee input-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp) for the programmatic interface to @('nil').
     We ignore the artifacts returned as additional results."))
  (b* (((mv erp event & & & & & state)
        (input-files-process-inputs-and-gen-events args nil state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-definition
  :short "Definition of the @(tsee input-files) macro."
  (defmacro input-files (&rest args)
    `(make-event-terse
      (input-files-fn ',args 'input-files state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-files-prog
  :parents (input-files)
  :short "Programmatic interface to @(tsee input-files)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This (non-event) macro provides
     a programmatic interface to the functionality of @(tsee input-files).
     It has the form:")
   (xdoc::codeblock
    "(input-files-prog :files             ...  ; no default"
    "                  :preprocess        ...  ; default nil"
    "                  :process           ...  ; default :validate"
    "                  :gcc               ...  ; default nil"
    "                  :short-bytes       ...  ; default 2"
    "                  :int-bytes         ...  ; default 4"
    "                  :long-bytes        ...  ; default 8"
    "                  :long-long-bytes   ...  ; default 8"
    "                  :plain-char-signed ...  ; default nil"
    "  )")
   (xdoc::p
    "This is the same as @(tsee input-files),
     except that there are no inputs for the constant names,
     because this macro does not generate any events.
     Instead, it returns an "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuple")
    " consisting of the values that @(tsee input-files)
     would assign to the generated named constants.
     These are the results of the error-value tuple, in order:")
   (xdoc::ul
    (xdoc::li
     "@('read-files'):
      the @(tsee fileset) consisting of the files read,
      without any preprocessing.")
    (xdoc::li
     "@('preproc-files'):
      the @(tsee fileset) resulting from preprocessing @('read-files'),
      if @(':preprocess') is not @('nil');
      or an irrelevant value of type @(tsee fileset),
      if @(':preprocess') is @('nil').")
    (xdoc::li
     "@('parsed-tuens'):
      the @(tsee transunit-ensemble) resulting from
      parsing either @('read-files') (if @(':preprocess') is @('nil'))
      or @('preproc-files') (if @(':preprocess') is not @('nil')),
      if @(':process') is @(':parse') or @(':disambiguate') or @(':validate');
      or an irrelevant value of type @(tsee transunit-ensemble),
      if @(':process') is @(':read').")
    (xdoc::li
     "@('disamb-tuens'):
      the @(tsee transunit-ensemble) resulting from
      disambiguating @('parsed-tuens'),
      if @(':process') is @(':disambiguate') or @(':validate');
      or an irrelevant value of type @(tsee transunit-ensemble),
      if @(':process') is @(':read') or @(':parse').")
    (xdoc::li
     "@('valid-tuens'):
      the @(tsee transunit-ensemble) resulting from
      validating @('disamb-tuens'),
      if @(':process') is @(':validate');
      or an irrelevant value of type @(tsee transunit-ensemble),
      if @(':process') is @(':read') or @(':parse') or @(':disambiguate').")
    (xdoc::li
     "@('state'):
      the ACL2 @(see state)."))
   (xdoc::p
    "Note that the macro implicitly takes @(tsee state),
     so it must be used in a context where @(tsee state) is available."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-prog-fn ((args true-listp) state)
  :returns (mv erp
               (read-files filesetp)
               (preproc-files filesetp)
               (parsed-tuens transunit-ensemblep)
               (disamb-tuens transunit-ensemblep)
               (valid-tuens transunit-ensemblep)
               state)
  :short "Implementation of @(tsee input-files-prog)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp') for the programmatic interface to @('t').
     We ignore the event returned as result,
     and just return the artifacts."))
  (b* ((irr-fileset (fileset nil))
       ((reterr)
        irr-fileset
        irr-fileset
        (irr-transunit-ensemble)
        (irr-transunit-ensemble)
        (irr-transunit-ensemble)
        state)
       ((erp &
             read-files
             preproc-files
             parsed-tuens
             disamb-tuens
             valid-tuens
             state)
        (input-files-process-inputs-and-gen-events args t state)))
    (retok read-files
           preproc-files
           parsed-tuens
           disamb-tuens
           valid-tuens
           state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-prog-definition
  :short "Definition of the @(tsee input-files-prog) macro."
  (defmacro input-files-prog (&rest args)
    `(input-files-prog-fn ',args state)))
