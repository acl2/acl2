; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocess-file")
(include-book "parser")
(include-book "disambiguator")

(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)
(include-book "system/pseudo-event-form-listp" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))
(local (include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system))
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
        :gcc)
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
  (and (member-eq x '(nil :parse :disamb)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs ((args true-listp))
  :returns (mv erp
               (paths filepath-setp)
               (preprocessor string-optionp
                             :hints
                             (("Goal"
                               :in-theory
                               (enable input-files-preprocess-inputp))))
               (process input-files-process-inputp)
               (const symbolp)
               (const-files symbolp)
               (const-preproc symbolp)
               (const-parsed symbolp)
               (gcc booleanp))
  :short "Process the inputs."
  (b* (((reterr) nil nil nil nil nil nil nil nil)
       ;; Check and obtain options.
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
       ;; Process :FILES input.
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
       (paths (input-files-strings-to-paths files))
       ;; Process :PREPROCESS input.
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
                       preprocess))
       ;; Process :PROCESS input.
       (process-option (assoc-eq :process options))
       (process (if process-option
                    (cdr process-option)
                  nil))
       ((unless (input-files-process-inputp process))
        (reterr (msg "The :PROCESS input must be NIL, :PARSE, or :DISAMB, ~
                      but it is ~x0 instead."
                     process)))
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
       ;; Process :CONST-FILES input.
       (const-files-option (assoc-eq :const-files options))
       (const-files (if const-files-option
                        (cdr const-files-option)
                      nil))
       ((unless (symbolp const-files))
        (reterr (msg "The :CONST-FILES input must be a symbol, ~
                      but it is ~x0 instead."
                     const-files)))
       ((when (and const-files
                   (not preprocess)
                   (not process)))
        (reterr (msg "The :CONST-FILES input must be NIL ~
                      if both the :PREPROCESS and the :PROCESS inputs are NIL, ~
                      which is the case in this call of INPUT-FILES.")))
       ;; Process :CONST-PREPROC input.
       (const-preproc-option (assoc-eq :const-preproc options))
       (const-preproc (if const-preproc-option
                          (cdr const-preproc-option)
                        nil))
       ((unless (symbolp const-preproc))
        (reterr (msg "The :CONST-PREPROC input must be a symbol, ~
                      but it is ~x0 instead."
                     const-preproc)))
       ((when (and const-preproc
                   (not preprocess)))
        (reterr (msg "The :CONST-FILES input must be NIL ~
                      if the :PREPROCESS input is NIL, ~
                      which is the case in this call of INPUT-FILES.")))
       ;; Process :CONST-PARSED input.
       (const-parsed-option (assoc-eq :const-parsed options))
       (const-parsed (if const-parsed-option
                         (cdr const-parsed-option)
                       nil))
       ((unless (symbolp const-parsed))
        (reterr (msg "The :CONST-PARSED input must be a symbol, ~
                      but it is ~x0 instead."
                     const-parsed)))
       ((when (and const-parsed
                   (not process)))
        (reterr (msg "The :CONST-FILES input must be NIL ~
                      if the :PROCESS input is NIL, ~
                      which is the case in this call of INPUT-FILES.")))
       ((when (and const-parsed
                   (eq process :parse)))
        (reterr (msg "The :CONST-FILES input must be NIL ~
                      if the :PROCESS input is :PARSE, ~
                      which is the case in this call of INPUT-FILES.")))
       ;; Process :GCC input.
       (gcc-option (assoc-eq :gcc options))
       (gcc (if gcc-option
                (cdr gcc-option)
              nil))
       ((unless (booleanp gcc))
        (reterr (msg "The :GCC input must be a boolean, ~
                      but it is ~x0 instead."
                     gcc))))
    (retok paths
           preprocessor
           process
           const
           const-files
           const-preproc
           const-parsed
           gcc))
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
                                (gcc booleanp)
                                state)
  :returns (mv erp (events pseudo-event-form-listp) state)
  :short "Generate the events."
  (b* (((reterr) nil state)
       ;; Initialize list of generated events.
       (events nil)
       ;; Read files from file system.
       ((erp files state) (input-files-read-files paths state))
       ;; Generate :CONST-FILE constant if required.
       (events (if const-files
                   (cons `(defconst ,const-files ',files) events)
                 events))
       ;; Preprocess if required;
       ;; either way, after this, FILES contains the files to process.
       ((erp files state) (if preprocessor
                              (preprocess-files paths
                                                :preprocessor preprocessor)
                            (retok files state)))
       ;; Generate :CONST-PREPROC if required.
       (events (if const-preproc
                   (cons `(defconst ,const-preproc ',files) events)
                 events))
       ;; If no processing is required, we are done;
       ;; generate :CONST constant with the files.
       ((when (eq process nil))
        (b* ((events (cons `(defconst ,const ',files) events)))
          (retok events state)))
       ;; At least parsing is required.
       ((erp parsed) (parse-fileset files gcc))
       ;; Generate :CONST-PARSED constant if required.
       (events (if const-parsed
                   (cons `(defconst ,const-parsed ',parsed) events)
                 events))
       ;; If only parsing is required, we are done;
       ;; generate :CONST constant with the parsed translation units.
       ((when (eq process :parse))
        (b* ((events (cons `(defconst ,const ',parsed) events)))
          (retok events state)))
       ;; Disambiguation is required.
       ((erp disamb) (dimb-transunit-ensemble parsed gcc))
       (events (cons `(defconst ,const ',disamb) events)))
    (retok events state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs-and-gen-events ((args true-listp) state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_) state)
       ((erp paths
             preprocessor
             process
             const
             const-files
             const-preproc
             const-parsed
             gcc)
        (input-files-process-inputs args))
       ((erp events state) (input-files-gen-events paths
                                                   preprocessor
                                                   process
                                                   const
                                                   const-files
                                                   const-preproc
                                                   const-parsed
                                                   gcc
                                                   state)))
    (retok `(progn ,@events) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp events state)
  :short "Event expansion of @(tsee input-files) from the inputs."
  (b* (((mv erp events state)
        (input-files-process-inputs-and-gen-events args state))
       ((when erp) (er-soft+ ctx t nil "~@0" erp)))
    (value events)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-definition
  :short "Definition of the @(tsee input-files) macro."
  (defmacro input-files (&rest args)
    `(make-event-terse
      (input-files-fn ',args 'input-files state))))
