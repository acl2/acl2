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
  (and (member-eq x '(:parse :disambiguate :validate)) t))

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

(define input-files-process-preprocess-args ((options symbol-alistp)
                                             (preprocessor string-optionp))
  :returns (mv erp
               (preprocess-args-presentp booleanp)
               (preprocess-extra-args string-listp))
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
       (preprocess-args-option (assoc-eq :preprocess-args options))
       ((when (not preprocess-args-option))
        (retok nil nil))
       (preprocess-args (cdr preprocess-args-option))
       ((when (not preprocessor))
        (reterr (msg "Since the :PREPROCESS input is NIL, ~
                      the :PREPROCESS-ARGS input must be absent, ~
                      but it is ~x0 instead."
                     preprocess-args)))
       ((unless (string-listp preprocess-args))
        (reterr (msg "The :PREPROCESS-ARGS input must a list of strings, ~
                      but it is ~x0 instead."
                     preprocess-args))))
    (retok t preprocess-args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-process ((options symbol-alistp))
  :returns (mv erp (process input-files-process-inputp))
  :short "Process the @(':process') input."
  (b* (((reterr) :parse)
       (process-option (assoc-eq :process options))
       (process (if process-option
                    (cdr process-option)
                  :validate))
       ((unless (input-files-process-inputp process))
        (reterr (msg "The :PROCESS input must be ~
                      :PARSE, :DISAMBIGUATE, or :VALIDATE ~
                      but it is ~x0 instead."
                     process))))
    (retok process)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-const ((options symbol-alistp)
                                   (progp booleanp))
  :returns (mv erp (const symbolp))
  :short "Process the @(':const') inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the programmatic interface has been called, this input must be absent.
     In this case, we return @('nil') as result."))
  (b* (((reterr) nil)
       (const-option (assoc-eq :const options))
       ((when progp)
        (b* (((when const-option)
              (reterr (msg "The :CONST input must not be supplied ~
                            to the programmatic interface."))))
          (retok nil)))
       ((unless const-option)
        (reterr (msg "The :CONST input must be supplied, ~
                      but it was not supplied.")))
       (const (cdr const-option))
       ((unless (symbolp const))
        (reterr (msg "The :CONST input must be a symbol, ~
                      but it is ~x0 instead."
                     const))))
    (retok const)))

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
               (preprocess-args-presentp booleanp)
               (preprocess-extra-args string-listp)
               (process input-files-process-inputp)
               (const symbolp)
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
  (b* (((reterr) nil nil nil nil :parse nil nil (ienv-default))
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
       ((erp preprocess-args-presentp preprocess-extra-args)
        (input-files-process-preprocess-args options preprocessor))
       ((erp process) (input-files-process-process options))
       ((erp const) (input-files-process-const options progp))
       ((erp gcc) (input-files-process-gcc options))
       ((erp ienv) (input-files-process-ienv options)))
    (retok paths
           preprocessor
           preprocess-args-presentp
           preprocess-extra-args
           process
           const
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
  (b* (((reterr) (irr-fileset) state)
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
                                (preprocess-args-presentp booleanp)
                                (preprocess-extra-args string-listp)
                                (process input-files-process-inputp)
                                (const symbolp)
                                (gcc booleanp)
                                (ienv ienvp)
                                (progp booleanp)
                                state)
  :returns (mv erp
               (events pseudo-event-form-listp)
               (tunits transunit-ensemblep)
               state)
  :short "Generate the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform all the necessary preprocessing and processing.
     Besides the events, we also return the translation unit ensemble
     resulting from processing the (possibly preprocessed) files.
     If the programmatic interface is being used,
     no events are actually generated."))
  (b* (((reterr) nil (irr-transunit-ensemble) state)
       ;; Initialize list of generated events.
       (events nil)
       ;; Preprocess if required, or read files from file system.
       ((erp files state) (if preprocessor
                              (if preprocess-args-presentp
                                  (preprocess-files
                                   paths
                                   :preprocessor preprocessor
                                   :extra-args preprocess-extra-args)
                                (preprocess-files
                                 paths
                                 :preprocessor preprocessor))
                            (input-files-read-files paths state)))
       ;; Parsing is always required.
       ((erp tunits) (parse-fileset files gcc))
       ;; If only parsing is required, we are done;
       ;; generate :CONST constant with the parsed translation units.
       ((when (eq process :parse))
        (b* ((events (if (not progp)
                         (rcons `(defconst ,const ',tunits) events)
                       events)))
          (retok events tunits state)))
       ;; Disambiguation is required, if we get here.
       ((erp tunits) (dimb-transunit-ensemble tunits gcc))
       ;; If no validation is required, we are done;
       ;; generate :CONST constant with the disambiguated translation unit.
       ((when (eq process :disambiguate))
        (b* ((events (if (not progp)
                         (rcons `(defconst ,const ',tunits) events)
                       events)))
          (retok events tunits state)))
       ;; Validation is required, if we get here.
       ((erp tunits) (valid-transunit-ensemble tunits gcc ienv))
       ;; Generate :CONST constant with the validated translation unit.
       (events (if (not progp)
                   (rcons `(defconst ,const ',tunits) events)
                 events)))
    (retok events tunits state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs-and-gen-events ((args true-listp)
                                                   (progp booleanp)
                                                   state)
  :returns (mv erp
               (event pseudo-event-formp)
               (tunits transunit-ensemblep)
               state)
  :short "Process the inputs and generate the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The event is an empty @(tsee progn) if
     this is called via the programmatic interface.
     We also return the translation unit ensemble
     resulting from processing the (possibly preprocessed) files."))
  (b* (((reterr) '(_) (irr-transunit-ensemble) state)
       ((erp paths
             preprocessor
             preprocess-args-presentp
             preprocess-extra-args
             process
             const
             gcc
             ienv)
        (input-files-process-inputs args progp))
       ((erp events tunits state)
        (input-files-gen-events paths
                                preprocessor
                                preprocess-args-presentp
                                preprocess-extra-args
                                process
                                const
                                gcc
                                ienv
                                progp
                                state)))
    (retok `(progn ,@events) tunits state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Event expansion of @(tsee input-files) from the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp) for the programmatic interface to @('nil').
     We ignore the artifacts returned as additional results."))
  (b* (((mv erp event & state)
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
    "                  :preprocess-args   ...  ; no default"
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
     except that there is no @(':const') input,
     because this macro does not generate any events.
     Instead, it returns an "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuple")
    " consisting of the value that @(tsee input-files)
     would assign to the generated named constant.
     These are the results of the error-value tuple, in order:")
   (xdoc::ul
    (xdoc::li
     "@('tunits'):
      the translation unit ensemble
      (a value of type @(tsee transunit-ensemble))
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

(define input-files-prog-fn ((args true-listp) state)
  :returns (mv erp (tunits transunit-ensemblep) state)
  :short "Implementation of @(tsee input-files-prog)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the flag @('progp') for the programmatic interface to @('t').
     We ignore the event returned as result,
     and just return the artifacts."))
  (b* (((reterr) (irr-transunit-ensemble) state)
       ((erp & tunits state)
        (input-files-process-inputs-and-gen-events args t state)))
    (retok tunits state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-prog-definition
  :short "Definition of the @(tsee input-files-prog) macro."
  (defmacro input-files-prog (&rest args)
    `(input-files-prog-fn ',args state)))
