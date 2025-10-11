; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "external-preprocessing")
(include-book "parser")
(include-book "disambiguator")
(include-book "validator")
(include-book "code-ensembles")

(include-book "clause-processors/magic-ev" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)
(include-book "kestrel/fty/string-stringlist-map" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "std/system/pseudo-event-form-listp" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-alists/symbol-alistp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
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
        :path
        :preprocess
        :preprocess-args
        :process
        :const
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
  (and (member-eq x '(:parse :disambiguate :validate)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-files ((files-presentp booleanp) files)
  :returns (mv erp (new-files string-listp))
  :short "Process the @(':files') input."
  (b* (((reterr) nil)
       ((unless files-presentp)
        (reterr (msg "The :FILES input must be supplied, ~
                      but it was not supplied.")))
       ((unless (string-listp files))
        (reterr (msg "The :FILES input must evaluate to a list of strings, ~
                      but it evaluates to ~x0 instead."
                     files)))
       ((unless (no-duplicatesp-equal files))
        (reterr (msg "The :FILES input must be a list without duplicates, ~
                      but the supplied ~x0 has duplicates."
                     files)))
       ((unless (consp files))
        (reterr (msg "The :FILES input must contain at least one element, ~
                      but it does not contain any."))))
    (retok files)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-path (path)
  :returns (mv erp (new-path stringp))
  :short "Process the @(':path') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the string is not @('/') but ends with @('/'),
     we remove the ending @('/').
     This is for uniformity when concatenating this
     with the files specified in the @(':files') input."))
  (b* (((reterr) "")
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
       (path (str::implode path-chars)))
    (retok path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-preprocess (preprocess)
  :returns (mv erp
               (preprocessor string-optionp
                             :hints
                             (("Goal"
                               :in-theory
                               (enable input-files-preprocess-inputp)))))
  :short "Process the @(':preprocess') input."
  (b* (((reterr) nil)
       ((unless (input-files-preprocess-inputp preprocess))
        (reterr (msg "The :PREPROCESS input must be NIL, :AUTO, or a string, ~
                      but it is ~x0 instead."
                     preprocess)))
       (preprocessor (if (eq preprocess :auto)
                         "gcc"
                       preprocess)))
    (retok preprocessor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-preprocess-args ((preprocessor string-optionp)
                                             preprocess-args-presentp
                                             preprocess-args
                                             state)
  (declare (ignore state))
  :returns (mv erp
               (new-preprocess-args-presentp booleanp)
               (preprocess-extra-args
                 (or (string-listp preprocess-extra-args)
                     (acl2::string-stringlist-mapp preprocess-extra-args))))
  :short "Process the @(':preprocess-args') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('preprocessor') input to this function
     is the result of processing the @(':preprocess') input.")
   (xdoc::p
    "If processing of the @(':preprocess-args') input is successful,
     we return a boolean saying whether the input was present or not,
     and the list of strings that it consists of (@('nil') if absent);
     the latter are passed as the @(':extra-args') input
     of @(tsee preprocess-files), which justifies the name of the result."))
  (b* (((reterr) nil nil)
       ((when (not preprocess-args-presentp))
        (retok nil nil))
       ((when (not preprocessor))
        (reterr (msg "Since the :PREPROCESS input is NIL, ~
                      the :PREPROCESS-ARGS input must be absent, ~
                      but it is ~x0 instead."
                     preprocess-args)))
       ((unless (or (string-listp preprocess-args)
                    (acl2::string-stringlist-mapp preprocess-args)))
        (reterr (msg "The :PREPROCESS-ARGS input must evaluate to ~
                      a list of strings ~
                      or an omap associating strings to lists of strings, ~
                      but it evaluates to ~x0 instead."
                     preprocess-args))))
    (retok t preprocess-args))

  ///

  (defret string-listp-of-input-files-process-preprocess-args.preprocess-extra-args
    (implies (not (acl2::string-stringlist-mapp preprocess-extra-args))
             (string-listp preprocess-extra-args))
    :hints
    (("Goal" :use return-type-of-input-files-process-preprocess-args.preprocess-extra-args
             :in-theory (disable return-type-of-input-files-process-preprocess-args.preprocess-extra-args))))

  (defret string-stringlist-mapp-of-input-files-process-preprocess-args.preprocess-extra-args
    (implies (not (string-listp preprocess-extra-args))
             (acl2::string-stringlist-mapp preprocess-extra-args))
    :hints
    (("Goal" :use return-type-of-input-files-process-preprocess-args.preprocess-extra-args
             :in-theory (disable return-type-of-input-files-process-preprocess-args.preprocess-extra-args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-process (process)
  :returns (mv erp (new-process input-files-process-inputp))
  :short "Process the @(':process') input."
  (b* (((reterr) :parse)
       ((unless (input-files-process-inputp process))
        (reterr (msg "The :PROCESS input must be ~
                      :PARSE, :DISAMBIGUATE, or :VALIDATE ~
                      but it is ~x0 instead."
                     process))))
    (retok process))

  ///

  (defret input-files-process-process.new-process
    (implies (not erp)
             (equal new-process process)))
  (in-theory (disable input-files-process-process.new-process)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-const ((const-presentp booleanp)
                                   const
                                   (progp booleanp))
  :returns (mv erp (new-const symbolp))
  :short "Process the @(':const') inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the programmatic interface has been called, this input must be absent.
     In this case, we return @('nil') as result."))
  (b* (((reterr) nil)
       ((when progp)
        (b* (((when const-presentp)
              (reterr (msg "The :CONST input must not be supplied ~
                            to the programmatic interface."))))
          (retok nil)))
       ((unless const-presentp)
        (reterr (msg "The :CONST input must be supplied, ~
                      but it was not supplied.")))
       ((unless (symbolp const))
        (reterr (msg "The :CONST input must be a symbol, ~
                      but it is ~x0 instead."
                     const))))
    (retok const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-keep-going (keep-going)
  :returns (mv erp (new-keep-going booleanp))
  :short "Process the @(':keep-going') input."
  (b* (((reterr) nil)
       ((unless (booleanp keep-going))
        (reterr (msg "The :KEEP-GOING input must be a boolean ~
                      but it is ~x0 instead."
                     keep-going))))
    (retok keep-going)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-ienv (gcc
                                  short-bytes
                                  int-bytes
                                  long-bytes
                                  long-long-bytes
                                  plain-char-signed)
  :returns (mv erp (ienv ienvp))
  :short "Process the
          @(':gcc'),
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
     which we return if the processing of these inputs is successful.")
   (xdoc::p
    "For now we choose the C17 standard, with or without GCC extensions."))
  (b* (((reterr) (ienv-default))
       ;; Process :GCC input.
       ((unless (booleanp gcc))
        (reterr (msg "The :GCC input must be a boolean, ~
                      but it is ~x0 instead."
                     gcc)))
       ;; Process :SHORT-BYTES input.
       ((unless (and (integerp short-bytes)
                     (>= short-bytes 2)))
        (reterr (msg "The :SHORT-BYTES input must be ~
                      an integer greater than or equal to 2, ~
                      but it is ~x0 instead."
                     short-bytes)))
       ;; Process :INT-BYTES input.
       ((unless (and (integerp int-bytes)
                     (>= int-bytes 2)
                     (>= int-bytes short-bytes)))
        (reterr (msg "The :INT-BYTES input must be ~
                      an integer greater than or equal to 2, ~
                      and greater than or equal to ~
                      the value ~x0 of :SHORT-BYTES, ~
                      but it is ~x1 instead."
                     short-bytes int-bytes)))
       ;; Process :LONG-BYTES input.
       ((unless (and (integerp long-bytes)
                     (>= long-bytes 4)
                     (>= long-bytes int-bytes)))
        (reterr (msg "The :LONG-BYTES input must be ~
                      an integer greater than or equal to 4, ~
                      and greater than or equal to ~
                      the value ~x0 of :INT-BYTES, ~
                      but it is ~x1 instead."
                     int-bytes long-bytes)))
       ;; Process :LONG-LONG-BYTES input.
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
       ((unless (booleanp plain-char-signed))
        (reterr (msg "The :PLAIN-CHAR-SIGNED input must be a boolean, ~
                      but it is ~x0 instead."
                     plain-char-signed)))
       ;; Build the implementation environment.
       (ienv (make-ienv :version (if gcc (c::version-c17+gcc) (c::version-c17))
                        :short-bytes short-bytes
                        :int-bytes int-bytes
                        :long-bytes long-bytes
                        :llong-bytes long-long-bytes
                        :plain-char-signedp plain-char-signed)))
    (retok ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs ((files-presentp booleanp)
                                    files
                                    path
                                    preprocess
                                    (preprocess-args-presentp booleanp)
                                    preprocess-args
                                    process
                                    (const-presentp booleanp)
                                    const
                                    keep-going
                                    gcc
                                    short-bytes
                                    int-bytes
                                    long-bytes
                                    long-long-bytes
                                    plain-char-signed
                                    (progp booleanp)
                                    state)
  :returns (mv erp
               (new-files string-listp)
               (new-path stringp)
               (preprocessor string-optionp)
               (new-preprocess-args-presentp booleanp)
               (preprocess-extra-args
                 (or (string-listp preprocess-extra-args)
                     (acl2::string-stringlist-mapp preprocess-extra-args)))
               (new-process input-files-process-inputp)
               (new-const symbolp)
               (keep-going booleanp)
               (ienv ienvp))
  :short "Process the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('preprocessor') result of this function
     is calculated from the @(':preprocess') input.
     The use of `preprocessor' vs. `preprocess' is intentional.")
   (xdoc::p
    "The other results of this function are the homonymous inputs,
     except that the last five inputs are combined into
     an implementation environment result."))
  (b* (((reterr) nil "" nil nil nil :parse nil nil (ienv-default))
       ;; Process the inputs.
       ((erp files) (input-files-process-files files-presentp files))
       ((erp path) (input-files-process-path path))
       ((erp preprocessor) (input-files-process-preprocess preprocess))
       ((erp preprocess-args-presentp preprocess-extra-args)
        (input-files-process-preprocess-args preprocessor
                                             preprocess-args-presentp
                                             preprocess-args
                                             state))
       ((erp process) (input-files-process-process process))
       ((erp const) (input-files-process-const const-presentp const progp))
       ((erp keep-going) (input-files-process-keep-going keep-going))
       ((erp ienv) (input-files-process-ienv gcc
                                             short-bytes
                                             int-bytes
                                             long-bytes
                                             long-long-bytes
                                             plain-char-signed)))
    (retok files
           path
           preprocessor
           preprocess-args-presentp
           preprocess-extra-args
           process
           const
           keep-going
           ienv))
  :guard-hints (("Goal" :in-theory (enable acl2::alistp-when-symbol-alistp)))

  ///

  (defret string-listp-of-input-files-process-inputs.preprocess-extra-args
    (implies (not (acl2::string-stringlist-mapp preprocess-extra-args))
             (string-listp preprocess-extra-args))
    :hints
    (("Goal" :use return-type-of-input-files-process-inputs.preprocess-extra-args
             :in-theory (disable return-type-of-input-files-process-inputs.preprocess-extra-args))))

  (defret string-stringlist-mapp-of-input-files-process-inputs.preprocess-extra-args
    (implies (not (string-listp preprocess-extra-args))
             (acl2::string-stringlist-mapp preprocess-extra-args))
    :hints
    (("Goal" :use return-type-of-input-files-process-inputs.preprocess-extra-args
             :in-theory (disable return-type-of-input-files-process-inputs.preprocess-extra-args))))

  (defret input-files-process-inputs.new-process
    (implies (not erp)
             (equal new-process process))
    :hints
    (("Goal"
      :in-theory (enable input-files-process-process.new-process))))
  (in-theory (disable input-files-process-inputs.new-process)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-read-files ((files string-listp) (path stringp) state)
  :returns (mv erp (fileset filesetp) state)
  :short "Read a file set from a given set of paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each file, we prepend the path,
     and we attempt to read the file at each resulting path,
     constructing the file set along the way.
     Recall that @('path') nevers ends with @('/') (unless it is just @('/')),
     because input processing removes the ending slash."))
  (b* (((reterr) (irr-fileset) state)
       ((when (endp files)) (retok (fileset nil) state))
       (file (car files))
       (path-to-read (str::cat path "/" file))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list path-to-read state))
       ((when erp)
        (reterr (msg "Reading ~x0 failed." path-to-read)))
       (data (filedata bytes))
       ((erp fileset state)
        (input-files-read-files (cdr files) path state)))
    (retok (fileset (omap::update (filepath file)
                                  data
                                  (fileset->unwrap fileset)))
           state))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-gen-events ((files string-listp)
                                (path stringp)
                                (preprocessor string-optionp)
                                (preprocess-args-presentp booleanp)
                                (preprocess-extra-args
                                 (or (acl2::string-stringlist-mapp
                                      preprocess-extra-args)
                                     (string-listp preprocess-extra-args)))
                                (process input-files-process-inputp)
                                (const symbolp)
                                (keep-going booleanp)
                                (ienv ienvp)
                                (progp booleanp)
                                state)
  :returns (mv erp
               (events pseudo-event-form-listp)
               (code code-ensemblep)
               state)
  :short "Generate the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform all the necessary preprocessing and processing.
     Besides the events, we also return the code ensemble
     resulting from processing the (possibly preprocessed) files,
     together with the implementation environment.
     If the programmatic interface is being used,
     no events are actually generated."))
  (b* (((reterr) nil (irr-code-ensemble) state)
       ;; Initialize list of generated events.
       (events nil)
       ;; Preprocess if required, or read files from file system.
       ((erp files state) (if preprocessor
                              (if preprocess-args-presentp
                                  (preprocess-files
                                   files
                                   :path path
                                   :preprocessor preprocessor
                                   :extra-args preprocess-extra-args)
                                (preprocess-files
                                 files
                                 :path path
                                 :preprocessor preprocessor))
                            (input-files-read-files files path state)))
       ;; Parsing is always required.
       ((erp tunits) (parse-fileset files (ienv->gcc ienv) keep-going))
       ;; If only parsing is required, we are done;
       ;; generate :CONST constant with the parsed translation units.
       ((when (eq process :parse))
        (b* ((code (make-code-ensemble :transunits tunits :ienv ienv))
             (events (if (not progp)
                         (rcons `(defconst ,const ',code) events)
                       events)))
          (retok events code state)))
       ;; Disambiguation is required, if we get here.
       ((erp tunits)
        (dimb-transunit-ensemble tunits (ienv->gcc ienv) keep-going))
       ;; If no validation is required, we are done;
       ;; generate :CONST constant with the disambiguated translation unit.
       ((when (eq process :disambiguate))
        (b* ((code (make-code-ensemble :transunits tunits :ienv ienv))
             (events (if (not progp)
                         (rcons `(defconst ,const ',code) events)
                       events)))
          (retok events code state)))
       ;; Validation is required, if we get here.
       ((erp tunits) (valid-transunit-ensemble tunits ienv keep-going))
       (code (make-code-ensemble :transunits tunits :ienv ienv))
       ;; Generate :CONST constant with the validated translation unit.
       (events (if (not progp)
                   (rcons `(defconst ,const ',code) events)
                 events)))
    (retok events code state))

  ///

  (defret code-ensemble-unambp-of-input-files-gen-events
    (implies (not erp)
             (code-ensemble-unambp code))
    :hyp (or (equal process :disambiguate)
             (equal process :validate))
    :hints (("Goal" :in-theory (enable code-ensemble-unambp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs-and-gen-events ((files-presentp booleanp)
                                                   files
                                                   path
                                                   preprocess
                                                   (preprocess-args-presentp booleanp)
                                                   preprocess-args
                                                   process
                                                   (const-presentp booleanp)
                                                   const
                                                   keep-going
                                                   gcc
                                                   short-bytes
                                                   int-bytes
                                                   long-bytes
                                                   long-long-bytes
                                                   plain-char-signed
                                                   (progp booleanp)
                                                   state)
  :returns (mv erp
               (event pseudo-event-formp)
               (code code-ensemblep)
               state)
  :short "Process the inputs and generate the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The event is an empty @(tsee progn) if
     this is called via the programmatic interface.
     We also return the translation unit ensemble
     resulting from processing the (possibly preprocessed) files."))
  (b* (((reterr) '(_) (irr-code-ensemble) state)
       ((erp files
             path
             preprocessor
             preprocess-args-presentp
             preprocess-extra-args
             process
             const
             keep-going
             ienv)
        (input-files-process-inputs files-presentp
                                    files
                                    path
                                    preprocess
                                    preprocess-args-presentp
                                    preprocess-args
                                    process
                                    const-presentp
                                    const
                                    keep-going
                                    gcc
                                    short-bytes
                                    int-bytes
                                    long-bytes
                                    long-long-bytes
                                    plain-char-signed
                                    progp
                                    state))
       ((erp events code state)
        (input-files-gen-events files
                                path
                                preprocessor
                                preprocess-args-presentp
                                preprocess-extra-args
                                process
                                const
                                keep-going
                                ienv
                                progp
                                state)))
    (retok `(progn ,@events) code state))

  ///

  (defret code-ensemble-unambp-of-input-files-process-inputs-and-gen-events
    (implies (not erp)
             (code-ensemble-unambp code))
    :hyp (or (equal process :disambiguate)
             (equal process :validate))
    :hints
    (("Goal"
      :in-theory
      (enable input-files-process-inputs.new-process)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-fn ((files-presentp booleanp)
                        files
                        path
                        preprocess
                        (preprocess-args-presentp booleanp)
                        preprocess-args
                        process
                        (const-presentp booleanp)
                        const
                        keep-going
                        gcc
                        short-bytes
                        int-bytes
                        long-bytes
                        long-long-bytes
                        plain-char-signed
                        (ctx ctxp)
                        state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee input-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp') for the programmatic interface to @('nil').
     We ignore the artifacts returned as additional results."))
  (b* (((mv erp event & state)
        (input-files-process-inputs-and-gen-events files-presentp
                                                   files
                                                   path
                                                   preprocess
                                                   preprocess-args-presentp
                                                   preprocess-args
                                                   process
                                                   const-presentp
                                                   const
                                                   keep-going
                                                   gcc
                                                   short-bytes
                                                   int-bytes
                                                   long-bytes
                                                   long-long-bytes
                                                   plain-char-signed
                                                   nil
                                                   state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-definition
  :short "Definition of the @(tsee input-files) macro."
  (defmacro input-files (&key (files 'nil files-presentp)
                              (path '".")
                              (preprocess 'nil)
                              (preprocess-args 'nil preprocess-args-presentp)
                              (process ':validate)
                              (const 'nil const-presentp)
                              (keep-going 'nil)
                              (gcc 'nil)
                              (short-bytes '2)
                              (int-bytes '4)
                              (long-bytes '8)
                              (long-long-bytes '8)
                              (plain-char-signed 'nil))
    `(make-event-terse
       (input-files-fn ',files-presentp
                       ,files
                       ',path
                       ',preprocess
                       ',preprocess-args-presentp
                       ,preprocess-args
                       ',process
                       ',const-presentp
                       ',const
                       ',keep-going
                       ',gcc
                       ',short-bytes
                       ',int-bytes
                       ',long-bytes
                       ',long-long-bytes
                       ',plain-char-signed
                       'input-files
                       state))))

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
    "(input-files-prog :files             ...  ; required"
    "                  :path              ...  ; default \".\""
    "                  :preprocess        ...  ; default nil"
    "                  :preprocess-args   ...  ; no default"
    "                  :process           ...  ; default :validate"
    "                  :keep-going        ...  ; default nil"
    "                  :gcc               ...  ; default nil"
    "                  :short-bytes       ...  ; default 2"
    "                  :int-bytes         ...  ; default 4"
    "                  :long-bytes        ...  ; default 8"
    "                  :long-long-bytes   ...  ; default 8"
    "                  :plain-char-signed ...  ; default nil"
    "  )")
   (xdoc::p
    "This is the same as @(tsee input-files),
     except that there is no @(':const') input,
     because this macro does not generate any events.
     Instead, it returns an "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuple")
    " consisting of the value that @(tsee input-files)
     would assign to the generated named constant.
     These are the results of the error-value tuple, in order:")
   (xdoc::ul
    (xdoc::li
     "@('code'):
      the code unit ensemble
      (a value of type @(tsee code-ensemble))
      resulting from processing, according to the @(':process') input,
      the files read from the paths specified by @(':files')
      (if @(':preprocess') is @('nil'))
      or the files resulting from their preprocessing
      (if @(':preprocess') is not @('nil').")
    (xdoc::li
     "@('state'):
      the ACL2 @(see state)."))
   (xdoc::p
    "Note that the macro implicitly takes @(tsee state),
     so it must be used in a context where @(tsee state) is available."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-prog-fn ((files-presentp booleanp)
                             files
                             path
                             preprocess
                             (preprocess-args-presentp booleanp)
                             preprocess-args
                             process
                             (const-presentp booleanp)
                             const
                             keep-going
                             gcc
                             short-bytes
                             int-bytes
                             long-bytes
                             long-long-bytes
                             plain-char-signed
                             state)
  :returns (mv erp (code code-ensemblep) state)
  :short "Implementation of @(tsee input-files-prog)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp') for the programmatic interface to @('t').
     We ignore the event returned as result,
     and just return the artifacts."))
  (b* (((reterr) (irr-code-ensemble) state)
       ((erp & code state)
        (input-files-process-inputs-and-gen-events files-presentp
                                                   files
                                                   path
                                                   preprocess
                                                   preprocess-args-presentp
                                                   preprocess-args
                                                   process
                                                   const-presentp
                                                   const
                                                   keep-going
                                                   gcc
                                                   short-bytes
                                                   int-bytes
                                                   long-bytes
                                                   long-long-bytes
                                                   plain-char-signed
                                                   t
                                                   state)))
    (retok code state))

  ///

  (defret code-ensemble-unambp-of-input-files-prog-fn
    (implies (not erp)
             (code-ensemble-unambp code))
    :hyp (or (equal process :disambiguate)
             (equal process :validate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-prog-definition
  :short "Definition of the @(tsee input-files-prog) macro."
  (defmacro input-files-prog (&key (files 'nil files-presentp)
                                   (path '".")
                                   (preprocess 'nil)
                                   (preprocess-args 'nil preprocess-args-presentp)
                                   (process ':validate)
                                   (const 'nil const-presentp)
                                   (keep-going 'nil)
                                   (gcc 'nil)
                                   (short-bytes '2)
                                   (int-bytes '4)
                                   (long-bytes '8)
                                   (long-long-bytes '8)
                                   (plain-char-signed 'nil))
    `(input-files-prog-fn ',files-presentp
                          ,files
                          ',path
                          ',preprocess
                          ',preprocess-args-presentp
                          ,preprocess-args
                          ',process
                          ',const-presentp
                          ',const
                          ',keep-going
                          ',gcc
                          ',short-bytes
                          ',int-bytes
                          ',long-bytes
                          ',long-long-bytes
                          ',plain-char-signed
                          state)))
