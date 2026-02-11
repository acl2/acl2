; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Supporting author: Grant Jurgensen (grant@kestrel.edu)

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

(acl2::controlled-configuration :hooks nil)

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
                                             preprocess-args
                                             state)
  (declare (ignore state))
  :returns (mv erp
               (preprocess-extra-args
                 (or (string-listp preprocess-extra-args)
                     (acl2::string-stringlist-mapp preprocess-extra-args))))
  :short "Process the @(':preprocess-args') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('preprocessor') input to this function
     is the result of processing the @(':preprocess') input.
     If it is @('nil'), the @(':preprocess-args') input
     is expected to also be @('nil').")
   (xdoc::p
    "If processing of the @(':preprocess-args') input is successful,
     we return its value,
     which is either a string list or an omap from strings to string lists.
     This value is passed as part of the @(':extra-args') input
     of @(tsee preprocess-files), which justifies the name of the result."))
  (b* (((reterr) nil)
       ((when (and (not preprocessor)
                   preprocess-args))
        (reterr (msg "Since the :PREPROCESS input is NIL, ~
                      the :PREPROCESS-ARGS input must also be NIL, ~
                      but it is ~x0 instead."
                     preprocess-args)))
       ((unless (or (string-listp preprocess-args)
                    (acl2::string-stringlist-mapp preprocess-args)))
        (reterr (msg "The :PREPROCESS-ARGS input must evaluate to ~
                      a list of strings ~
                      or an omap associating strings to lists of strings, ~
                      but it evaluates to ~x0 instead."
                     preprocess-args))))
    (retok preprocess-args))

  ///

  (defret string-listp-of-input-files-process-preprocess-args.preprocess-extra-args
    (implies (not (acl2::string-stringlist-mapp preprocess-extra-args))
             (string-listp preprocess-extra-args))
    :hints
    (("Goal"
      :use return-type-of-input-files-process-preprocess-args.preprocess-extra-args
      :in-theory
      (disable
       return-type-of-input-files-process-preprocess-args.preprocess-extra-args))))

  (defret string-stringlist-mapp-of-input-files-process-preprocess-args.preprocess-extra-args
    (implies (not (string-listp preprocess-extra-args))
             (acl2::string-stringlist-mapp preprocess-extra-args))
    :hints
    (("Goal"
      :use return-type-of-input-files-process-preprocess-args.preprocess-extra-args
      :in-theory
      (disable
       return-type-of-input-files-process-preprocess-args.preprocess-extra-args)))))

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
  :short "Process the @(':const') input."
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

(define input-files-process-ienv (ienv)
  :returns (mv erp (ienv ienvp))
  :short "Process the @('ienv') input."
  (b* (((reterr) (irr-ienv))
       ((unless ienv)
        (retok (ienv-default)))
       ((unless (ienvp ienv))
        (reterr (msg "The :IENV input must be an implementation environment, ~
                      but it is ~x0 instead."
                     ienv))))
    (retok ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-inputs ((files-presentp booleanp)
                                    files
                                    path
                                    preprocess
                                    preprocess-args
                                    process
                                    (const-presentp booleanp)
                                    const
                                    keep-going
                                    ienv
                                    (progp booleanp)
                                    state)
  :returns (mv erp
               (new-files string-listp)
               (new-path stringp)
               (preprocessor string-optionp)
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
  (b* (((reterr) nil "" nil nil :parse nil nil (irr-ienv))
       ;; Process the inputs.
       ((erp files) (input-files-process-files files-presentp files))
       ((erp path) (input-files-process-path path))
       ((erp preprocessor) (input-files-process-preprocess preprocess))
       ((erp preprocess-extra-args)
        (input-files-process-preprocess-args preprocessor
                                             preprocess-args
                                             state))
       ((erp process) (input-files-process-process process))
       ((erp const) (input-files-process-const const-presentp const progp))
       ((erp keep-going) (input-files-process-keep-going keep-going))
       ((erp ienv) (input-files-process-ienv ienv)))
    (retok files
           path
           preprocessor
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
    (("Goal"
      :use return-type-of-input-files-process-inputs.preprocess-extra-args
      :in-theory
      (disable
       return-type-of-input-files-process-inputs.preprocess-extra-args))))

  (defret string-stringlist-mapp-of-input-files-process-inputs.preprocess-extra-args
    (implies (not (string-listp preprocess-extra-args))
             (acl2::string-stringlist-mapp preprocess-extra-args))
    :hints
    (("Goal"
      :use return-type-of-input-files-process-inputs.preprocess-extra-args
      :in-theory
      (disable
       return-type-of-input-files-process-inputs.preprocess-extra-args))))

  (defret input-files-process-inputs.new-process
    (implies (not erp)
             (equal new-process process))
    :hints
    (("Goal"
      :in-theory (enable input-files-process-process.new-process))))
  (in-theory (disable input-files-process-inputs.new-process)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-preprocess-arg-std ((ienv ienvp))
  :returns (preprocess-arg stringp)
  :short "Return the @('-std=') flag reflecting the implementation
          environment."
  (b* (((ienv ienv) ienv))
    (c::version-case
      ienv.version
      :c17 "-std=c17"
      :c23 "-std=c23"
      :c17+gcc "-std=gnu17"
      :c23+gcc "-std=gnu23"
      :c17+clang "-std=gnu17"
      :c23+clang "-std=gnu23")))

(define string-stringlist-map-map-cons-values
  ((x stringp)
   (map acl2::string-stringlist-mapp))
  :returns (new-map acl2::string-stringlist-mapp)
  :short "Cons a string to the value of each entry in an omap from strings to
          string lists."
  (b* ((map (acl2::string-stringlist-map-fix map))
       (x (mbe :logic (acl2::str-fix x) :exec x)))
    (if (omap::emptyp map)
        nil
      (omap::update
        (omap::head-key map)
        (cons x (omap::head-val map))
        (string-stringlist-map-map-cons-values x (omap::tail map)))))
  :verify-guards :after-returns)

(define input-files-complete-preprocess-extra-args
  ((preprocess-extra-args
     (or (acl2::string-stringlist-mapp preprocess-extra-args)
         (string-listp preprocess-extra-args)))
   (ienv ienvp))
  :short "Extend the preprocessing arguments with a @('-std=') flag."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('preprocess-extra-args') is a string list,
     we cons the @('-std=') flag to the front of the list.
     If it is an omap, we cons the flag to the front of each list
     in the omap value set."))
  :returns (new-preprocess-extra-args
            (or (acl2::string-stringlist-mapp new-preprocess-extra-args)
                (string-listp new-preprocess-extra-args)))
  (b* ((arg-std (input-files-preprocess-arg-std ienv))
       (string-listp
         (mbe :logic (string-listp preprocess-extra-args)
              :exec (or (endp preprocess-extra-args)
                        (stringp (first preprocess-extra-args))))))
    (if string-listp
        (cons arg-std preprocess-extra-args)
      (string-stringlist-map-map-cons-values arg-std preprocess-extra-args)))
  :guard-hints (("Goal" :in-theory (enable acl2::string-stringlist-mapp)))
  ///

  (defret string-stringlist-mapp-of-input-files-complete-preprocess-extra-args.new-preprocess-extra-args
    (equal (acl2::string-stringlist-mapp new-preprocess-extra-args)
           (not (string-listp preprocess-extra-args)))
    :hints (("Goal" :in-theory (enable acl2::string-stringlist-mapp))))

  (defret string-listp-of-input-files-complete-preprocess-extra-args.new-preprocess-extra-args
    (implies (not (acl2::string-stringlist-mapp new-preprocess-extra-args))
             (string-listp new-preprocess-extra-args))
    :hints
    (("Goal"
      :use return-type-of-input-files-complete-preprocess-extra-args
      :in-theory
      (disable return-type-of-input-files-complete-preprocess-extra-args)))))

(define input-files-read-files ((files string-listp) (path stringp) state)
  :returns (mv erp (fileset filesetp) state)
  :short "Read a file set from a given set of paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each file, we prepend the path,
     and we attempt to read the file at each resulting path,
     constructing the file set along the way.
     Recall that @('path') never ends with @('/') (unless it is just @('/')),
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

(define input-files-gen-events ((files string-listp)
                                (path stringp)
                                (preprocessor string-optionp)
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
       ((erp files state)
        (if preprocessor
            (preprocess-files
              files
              :path path
              :preprocessor preprocessor
              :extra-args (input-files-complete-preprocess-extra-args
                            preprocess-extra-args
                            ienv))
          (input-files-read-files files path state)))
       ;; Parsing is always required.
       ((erp tunits) (parse-fileset files
                                    (ienv->version ienv)
                                    t ; skip-control-lines
                                    keep-going))
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
        (dimb-transunit-ensemble tunits (ienv->gcc/clang ienv) keep-going))
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

  (defret input-files-gen-events.events-type-prescription
    (true-listp events)
    :rule-classes :type-prescription)

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
                                                   preprocess-args
                                                   process
                                                   (const-presentp booleanp)
                                                   const
                                                   keep-going
                                                   ienv
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
             preprocess-extra-args
             process
             const
             keep-going
             ienv)
        (input-files-process-inputs files-presentp
                                    files
                                    path
                                    preprocess
                                    preprocess-args
                                    process
                                    const-presentp
                                    const
                                    keep-going
                                    ienv
                                    progp
                                    state))
       ((erp events code state)
        (input-files-gen-events files
                                path
                                preprocessor
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
    (("Goal" :in-theory (enable input-files-process-inputs.new-process)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-fn ((files-presentp booleanp)
                        files
                        path
                        preprocess
                        preprocess-args
                        process
                        (const-presentp booleanp)
                        const
                        keep-going
                        ienv
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
                                                   preprocess-args
                                                   process
                                                   const-presentp
                                                   const
                                                   keep-going
                                                   ienv
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
                              (preprocess-args 'nil)
                              (process ':validate)
                              (const 'nil const-presentp)
                              (keep-going 'nil)
                              (ienv 'nil))
    `(make-event-terse
       (input-files-fn ',files-presentp
                       ,files
                       ',path
                       ',preprocess
                       ,preprocess-args
                       ',process
                       ',const-presentp
                       ',const
                       ',keep-going
                       ,ienv
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
    "(input-files-prog :files           ...  ; required"
    "                  :path            ...  ; default \".\""
    "                  :preprocess      ...  ; default nil"
    "                  :preprocess-args ...  ; default nil"
    "                  :process         ...  ; default :validate"
    "                  :keep-going      ...  ; default nil"
    "                  :ienv            ...  ; default (ienv-default)"
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
                             preprocess-args
                             process
                             (const-presentp booleanp)
                             const
                             keep-going
                             ienv
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
                                                   preprocess-args
                                                   process
                                                   const-presentp
                                                   const
                                                   keep-going
                                                   ienv
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
                                   (preprocess-args 'nil)
                                   (process ':validate)
                                   (const 'nil const-presentp)
                                   (keep-going 'nil)
                                   (ienv 'nil))
    `(input-files-prog-fn ',files-presentp
                          ,files
                          ',path
                          ',preprocess
                          ,preprocess-args
                          ',process
                          ',const-presentp
                          ',const
                          ',keep-going
                          ',ienv
                          state)))
