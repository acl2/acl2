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
(include-book "preprocessor")
(include-book "parser")
(include-book "disambiguator")
(include-book "validator")
(include-book "code-ensembles")

(include-book "clause-processors/magic-ev" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/fty/string-option" :dir :system)
(include-book "kestrel/fty/string-stringlist-map" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
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
      (eq x :internal)
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

(define input-files-process-base-dir (base-dir)
  :returns (mv erp (new-base-dir stringp))
  :short "Process the @(':base-dir') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the string is not @('/') but ends with @('/'),
     we remove the ending @('/').
     This is for uniformity when concatenating this
     with the files specified in the @(':files') input."))
  (b* (((reterr) "")
       ((unless (stringp base-dir))
        (reterr (msg "The :BASE-DIR input must be a string, ~
                      but it is ~x0 instead."
                     base-dir)))
       (base-dir-chars (str::explode base-dir))
       ((unless (consp base-dir-chars))
        (reterr (msg "The :BASE-DIR input must be not empty, ~
                      but it is the empty string instead.")))
       (base-dir-chars (if (and (consp (cdr base-dir-chars))
                                (eql (car (last base-dir-chars)) #\/))
                           (butlast base-dir-chars 1)
                         base-dir-chars))
       (base-dir (str::implode base-dir-chars)))
    (retok base-dir)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-preprocess (preprocess)
  :returns (mv erp
               (preprocessor string-optionp
                             :hints
                             (("Goal"
                               :in-theory
                               (enable input-files-preprocess-inputp)))))
  :short "Process the @(':preprocess') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('preprocessor') result of this function
     encodes the preprocessor provided by this library as the empty string,
     so that we can use a simpler return type here,
     namely @(tsee string-optionp).
     Note that the empty string cannot be confused with
     any command to invoke an external preprocessor."))
  (b* (((reterr) nil)
       ((unless (input-files-preprocess-inputp preprocess))
        (reterr (msg "The :PREPROCESS input must be ~
                      NIL, :INTERNAL, :AUTO, or a string, ~
                      but it is ~x0 instead."
                     preprocess)))
       (preprocessor (cond ((eq preprocess :internal) "")
                           ((eq preprocess :auto) "gcc")
                           (t preprocess))))
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
     If it is @('nil') or the empty string
     (the latter encodes the internal preprocessor of this library),
     the @(':preprocess-args') input is expected to also be @('nil').")
   (xdoc::p
    "If processing of the @(':preprocess-args') input is successful,
     we return its value,
     which is either a string list or an omap from strings to string lists.
     This value is passed as part of the @(':extra-args') input
     of @(tsee preprocess-files), which justifies the name of the result."))
  (b* (((reterr) nil)
       ((when (and (member-equal preprocessor '(nil ""))
                   preprocess-args))
        (reterr (msg "Since the :PREPROCESS input is NIL or :INTERNAL, ~
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

(defval *input-files-allowed-preprocess-options*
  :short "Keyword options accepted by @(tsee input-files)
          for the @(':preprocess-options') input."
  (list :full-expansion
        :keep-comments
        :trace-expansion))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-preprocess-options (preprocess-options
                                                (preprocessor string-optionp))
  :returns (mv erp (options ppoptionsp))
  :short "Process the @(':preprocess-options') input."
  (b* (((reterr) (irr-ppoptions))
       ((unless (keyword-value-listp preprocess-options))
        (reterr (msg "The :PREPROCESS-OPTIONS must be a keyword-value list, ~
                      but it is ~x0 instead."
                     preprocess-options)))
       ((when (and preprocess-options
                   (not (equal preprocessor ""))))
        (reterr (msg "Since the :PREPROCESS option is not :INTERNAL, ~
                      the :PREPROCESS-OPTIONS must be NIL, ~
                      but it is ~x0 instead."
                     preprocess-options)))
       (alist (keyword-value-list-to-alist preprocess-options))
       (keywords (strip-cars alist))
       ((unless (subsetp-eq keywords *input-files-allowed-preprocess-options*))
        (reterr (msg "The keywords in the :PREPROCESS-OPTIONS input ~
                      must be among ~&0, but they include ~&1 instead."
                     *input-files-allowed-preprocess-options*
                     (set-difference-eq
                      keywords
                      *input-files-allowed-preprocess-options*))))
       ((unless (no-duplicatesp-eq keywords))
        (reterr (msg "The keywords in the :PREPROCESS-OPTIONS input ~
                      must have no duplicates, ~
                      but the list ~x0 contains duplicates."
                     keywords)))
       (full-expansion (cdr (assoc-eq :full-expansion alist)))
       ((unless (booleanp full-expansion))
        (reterr (msg "The preprocessor option :FULL-EXPANSION ~
                      must be T or NIL, but it is ~x0 instead."
                     full-expansion)))
       (keep-comments (b* ((kwd+val (assoc-eq :keep-comments alist)))
                        (if kwd+val
                            (cdr kwd+val)
                          t)))
       ((unless (booleanp keep-comments))
        (reterr (msg "The preprocessor option :KEEP-COMMENTS ~
                      must be T or NIL, but it is ~x0 instead."
                     keep-comments)))

       (trace-expansion (b* ((kwd+val (assoc-eq :trace-expansion alist)))
                          (if kwd+val
                              (cdr kwd+val)
                            t)))
       ((unless (booleanp trace-expansion))
        (reterr (msg "The preprocessor option :TRACE-EXPANSION ~
                      must be T or NIL, but it ~x0 instead."
                     trace-expansion))))
    (retok (make-ppoptions :full-expansion full-expansion
                           :keep-comments keep-comments
                           :trace-expansion trace-expansion
                           :no-warnings nil)))
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::symbol-listp-of-strip-cars-when-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-process-include-dirs ((preprocessor string-optionp)
                                          include-dirs)
  :returns (mv erp (new-include-dirs string-listp))
  :short "Process the @(':include-dirs') input."
  (b* (((reterr) nil)
       ((unless (string-listp include-dirs))
        (reterr (msg "The :INCLUDE-DIRS input must be a list of strings, ~
                      but it is ~x0 instead."
                     include-dirs)))
       ((when (and (consp include-dirs)
                   (not (equal preprocessor "")))) ; not :internal
        (reterr (msg "Unless the :PREPROCESSOR input is :INTERNAL, ~
                      the :INCLUDE-DIRS input must be NIL, ~
                      but it is ~x0 instead."
                     include-dirs))))
    (retok include-dirs)))

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

(define input-files-process-strict-merge (strict-merge)
  :returns (mv erp (new-strict-merge booleanp))
  :short "Process the @(':strict-merge') input."
  (b* (((reterr) nil)
       ((unless (booleanp strict-merge))
        (reterr (msg "The :STRICT-MERGE input must be a boolean ~
                      but it is ~x0 instead."
                     strict-merge))))
    (retok strict-merge)))

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
                                    base-dir
                                    preprocess
                                    preprocess-args
                                    preprocess-options
                                    include-dirs
                                    process
                                    (const-presentp booleanp)
                                    const
                                    strict-merge
                                    keep-going
                                    ienv
                                    (progp booleanp)
                                    state)
  :returns (mv erp
               (new-files string-listp)
               (new-base-dir stringp)
               (preprocessor string-optionp)
               (preprocess-extra-args
                 (or (string-listp preprocess-extra-args)
                     (acl2::string-stringlist-mapp preprocess-extra-args)))
               (options ppoptionsp)
               (new-include-dirs string-listp)
               (new-process input-files-process-inputp)
               (new-const symbolp)
               (strict-merge booleanp)
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
  (b* (((reterr)
        nil "" nil nil (irr-ppoptions) nil :parse nil nil nil (irr-ienv))
       ;; Process the inputs.
       ((erp files) (input-files-process-files files-presentp files))
       ((erp base-dir) (input-files-process-base-dir base-dir))
       ((erp preprocessor) (input-files-process-preprocess preprocess))
       ((erp preprocess-extra-args)
        (input-files-process-preprocess-args preprocessor
                                             preprocess-args
                                             state))
       ((erp options)
        (input-files-process-preprocess-options preprocess-options
                                                preprocessor))
       ((erp include-dirs)
        (input-files-process-include-dirs preprocessor include-dirs))
       ((erp process) (input-files-process-process process))
       ((erp const) (input-files-process-const const-presentp const progp))
       ((erp strict-merge) (input-files-process-strict-merge strict-merge))
       ((erp keep-going) (input-files-process-keep-going keep-going))
       ((erp ienv) (input-files-process-ienv ienv)))
    (retok files
           base-dir
           preprocessor
           preprocess-extra-args
           options
           include-dirs
           process
           const
           strict-merge
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
  (b* (((c::dialect dialect) (ienv->dialect ienv)))
    (c::standard-case
      dialect.std
      :c17 (if (c::dialect-gcc/clangp dialect) "-std=gnu17" "-std=c17")
      :c23 (if (c::dialect-gcc/clangp dialect) "-std=gnu23" "-std=c23"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-read-files ((files string-listp) (base-dir stringp) state)
  :returns (mv erp (fileset filesetp) state)
  :short "Read a file set from a given set of paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each file, we prepend the base directory,
     and we attempt to read the file at each resulting path,
     constructing the file set along the way.
     Recall that @('base-dir') never ends with @('/')
     (unless it is just @('/')),
     because input processing removes the ending slash."))
  (b* (((reterr) (irr-fileset) state)
       ((when (endp files)) (retok (fileset nil) state))
       (file (car files))
       (path-to-read (str::cat base-dir "/" file))
       ((mv erp bytes state)
        (acl2::read-file-into-byte-list path-to-read state))
       ((when erp)
        (reterr (msg "Reading ~x0 failed." path-to-read)))
       (data (filedata bytes))
       ((erp fileset state)
        (input-files-read-files (cdr files) base-dir state)))
    (retok (fileset (omap::update (filepath file)
                                  data
                                  (fileset->files fileset)))
           state))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-one-file ((path filepathp)
                              (base-dir stringp)
                              (preprocessor string-optionp)
                              (preprocess-extra-args
                               (or (acl2::string-stringlist-mapp
                                    preprocess-extra-args)
                                   (string-listp preprocess-extra-args)))
                              (process input-files-process-inputp)
                              (ienv ienvp)
                              state)
  :guard (not (equal preprocessor ""))
  :returns (mv erp
               (tunit trans-unitp)
               (externals valid-externalsp)
               (completions type-completions-p)
               state)
  :short "Process one file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We preprocess the file as @(tsee preprocess-files) does,
     or just read it if there is no preprocessor.
     Then we parse, disambiguate, and validate it,
     as required by @(':process'),
     as @(tsee parse-fileset), @(tsee dimb-trans-ensemble),
     and @(tsee valid-trans-ensemble) do for each file.")
   (xdoc::p
    "When validating, we also return the file's information
     about identifiers with external linkage and type completions,
     for the caller to merge (see @(tsee input-files-per-file-loop));
     otherwise, we return empty ones.")
   (xdoc::p
    "The internal preprocessor is excluded by the guard:
     it may preserve @('#include') directives,
     and disambiguating those involves other files."))
  (b* (((reterr) (irr-trans-unit) (treemap::empty) (treemap::empty) state)
       (file (filepath->string path))
       ;; BASE-DIR never ends with / (unless it is just /),
       ;; because input processing removes the ending slash.
       (path-to-read (str::cat base-dir "/" file))
       ((erp data state)
        (b* (((reterr) (irr-filedata) state))
          (if preprocessor
              (b* (((erp - data state)
                    (preprocess-file path-to-read
                                     :preprocessor preprocessor
                                     :extra-args (preprocess-file-extra-args
                                                  file preprocess-extra-args)
                                     :state state)))
                (retok data state))
            (b* (((mv erp bytes state)
                  (acl2::read-file-into-byte-list path-to-read state))
                 ((when erp)
                  (reterr (msg "Reading ~x0 failed." path-to-read))))
              (retok (filedata bytes) state)))))
       ((erp tunit)
        (parse-file path (filedata->bytes data) (ienv->dialect ienv) t))
       ((when (eq process :parse))
        (retok tunit (treemap::empty) (treemap::empty) state))
       ((mv erp tunit & &)
        (dimb-trans-unit tunit (init-dstate path ienv) nil nil nil 1000000000))
       ((when erp)
        (reterr (msg "Error in translation unit ~x0: ~@1" file erp)))
       ((when (eq process :disambiguate))
        (retok tunit (treemap::empty) (treemap::empty) state))
       ((mv erp tunit externals completions)
        (valid-trans-unit path tunit ienv))
       ((when erp)
        (reterr (msg "Error in translation unit ~x0: ~@1" file erp))))
    (retok tunit externals completions state))

  ///

  (defret trans-unit-unambp-of-input-files-one-file
    (implies (not erp)
             (trans-unit-unambp tunit))
    :hyp (not (equal process :parse))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-per-file-loop ((paths filepath-setp)
                                   (base-dir stringp)
                                   (preprocessor string-optionp)
                                   (preprocess-extra-args
                                    (or (acl2::string-stringlist-mapp
                                         preprocess-extra-args)
                                        (string-listp preprocess-extra-args)))
                                   (process input-files-process-inputp)
                                   (strict-merge booleanp)
                                   (keep-going booleanp)
                                   (ienv ienvp)
                                   (tumap filepath-trans-unit-mapp)
                                   (mstate valid-merge-statep)
                                   state)
  :guard (not (equal preprocessor ""))
  :returns (mv erp
               (new-tumap filepath-trans-unit-mapp)
               (new-mstate valid-merge-statep)
               state)
  :short "Loop for @(tsee input-files-per-file)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We process each file and, when validating,
     merge its information into @('mstate'),
     in the same order and with the same error handling as
     @(tsee valid-filepath-trans-unit-map).
     We accumulate the translation units in @('tumap')."))
  (b* (((reterr) nil (irr-valid-merge-state) state)
       ((when (set::emptyp (filepath-set-fix paths)))
        (retok (filepath-trans-unit-map-fix tumap)
               (valid-merge-state-fix mstate)
               state))
       (path (set::head paths))
       ((mv erp tunit externals completions state)
        (input-files-one-file path
                              base-dir
                              preprocessor
                              preprocess-extra-args
                              process
                              ienv
                              state))
       ((mv erp new-mstate)
        (b* (((when erp) (mv erp (irr-valid-merge-state)))
             ((unless (eq process :validate))
              (mv nil (valid-merge-state-fix mstate)))
             ((mv erp new-mstate)
              (valid-merge-trans-unit
                externals completions mstate ienv strict-merge))
             ((when erp)
              (mv (msg "Error in translation unit ~x0: ~@1"
                       (filepath->string path)
                       erp)
                  (irr-valid-merge-state))))
          (mv nil new-mstate)))
       ((when erp)
        (if keep-going
            (prog2$ (cw "~@0~%" erp)
                    (input-files-per-file-loop (set::tail paths)
                                               base-dir
                                               preprocessor
                                               preprocess-extra-args
                                               process
                                               strict-merge
                                               keep-going
                                               ienv
                                               tumap
                                               mstate
                                               state))
          (mv erp nil (irr-valid-merge-state) state)))
       (tumap (omap::update path tunit (filepath-trans-unit-map-fix tumap))))
    (input-files-per-file-loop (set::tail paths)
                               base-dir
                               preprocessor
                               preprocess-extra-args
                               process
                               strict-merge
                               keep-going
                               ienv
                               tumap
                               new-mstate
                               state))
  :prepwork ((local (in-theory (enable emptyp-of-filepath-set-fix))))

  ///

  (defret filepath-trans-unit-map-unambp-of-input-files-per-file-loop
    (implies (not erp)
             (filepath-trans-unit-map-unambp new-tumap))
    :hyp (and (filepath-trans-unit-map-unambp (double-rewrite tumap))
              (not (equal process :parse)))
    :hints (("Goal"
             :induct t
             :in-theory (enable filepath-trans-unit-map-unambp-of-update)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-filepaths ((files string-listp))
  :returns (paths filepath-setp)
  :short "Set of file paths of the files."
  (if (endp files)
      nil
    (set::insert (filepath (car files))
                 (input-files-filepaths (cdr files))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-per-file ((files string-listp)
                              (base-dir stringp)
                              (preprocessor string-optionp)
                              (preprocess-extra-args
                               (or (acl2::string-stringlist-mapp
                                    preprocess-extra-args)
                                   (string-listp preprocess-extra-args)))
                              (process input-files-process-inputp)
                              (strict-merge booleanp)
                              (keep-going booleanp)
                              (ienv ienvp)
                              state)
  :guard (not (equal preprocessor ""))
  :returns (mv erp (tunits trans-ensemblep) state)
  :short "Process the files one at a time."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each file goes through all the required stages
     before the next file is processed,
     so the intermediate results of a file
     are not kept while the other files are processed.
     This requires the files to be independent,
     which is why the guard excludes the internal preprocessor
     (see @(tsee input-files-one-file)).")
   (xdoc::p
    "If @(':keep-going') is @('t') and some file has failed,
     we print how many files succeeded.
     When validating, we annotate the translation ensemble
     with the merged information, as @(tsee valid-trans-ensemble) does."))
  (b* (((reterr) (irr-trans-ensemble) state)
       (paths (input-files-filepaths files))
       (preprocess-extra-args (input-files-complete-preprocess-extra-args
                               preprocess-extra-args
                               ienv))
       ((erp tumap mstate state)
        (input-files-per-file-loop paths
                                   base-dir
                                   preprocessor
                                   preprocess-extra-args
                                   process
                                   strict-merge
                                   keep-going
                                   ienv
                                   nil
                                   (init-valid-merge-state)
                                   state))
       (- (if keep-going
              (b* ((len-paths (set::cardinality paths))
                   (len-tumap (omap::size tumap)))
                (if (= len-paths len-tumap)
                    nil
                  (cw "~s0 ~x1/~x2 files.~%"
                      (case process
                        (:parse "Parsed")
                        (:disambiguate "Disambiguated")
                        (t "Validated"))
                      len-tumap
                      len-paths)))
            nil))
       ((valid-merge-state mstate) mstate)
       (info (and (eq process :validate)
                  (make-trans-ensemble-vinfo
                   :externals mstate.externals
                   :completions mstate.completions))))
    (retok (make-trans-ensemble :units tumap
                                :resolved-includes nil
                                :info info)
           state))

  ///

  (defret trans-ensemble-unambp-of-input-files-per-file
    (implies (not erp)
             (trans-ensemble-unambp tunits))
    :hyp (not (equal process :parse))
    :hints
    (("Goal" :in-theory (enable trans-ensemble-unambp-of-trans-ensemble)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-per-stage ((files string-listp)
                               (base-dir stringp)
                               (preprocessor string-optionp)
                               (preprocess-extra-args
                                (or (acl2::string-stringlist-mapp
                                     preprocess-extra-args)
                                    (string-listp preprocess-extra-args)))
                               (options ppoptionsp)
                               (include-dirs string-listp)
                               (process input-files-process-inputp)
                               (strict-merge booleanp)
                               (keep-going booleanp)
                               (ienv ienvp)
                               state)
  :returns (mv erp (tunits trans-ensemblep) state)
  :short "Process the files one stage at a time."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each stage is applied to all the files before the next stage.
     This works with any preprocessing,
     but it keeps the results of each stage for all the files.
     The internal preprocessor may preserve @('#include') directives,
     and disambiguating those involves other files
     (see @(tsee dimb-filepath-trans-unit-map)),
     so with that preprocessor the files cannot be processed one at a time
     as in @(tsee input-files-per-file)."))
  (b* (((reterr) (irr-trans-ensemble) state)
       ;; Preprocess if required, or just read files from file system.
       ;; Unless we use the internal preprocessor,
       ;; the RESOLVED-INCLUDES mapping is empty (NIL).
       ((erp files resolved-includes state)
        (b* (((reterr) (irr-fileset) nil state))
          (cond ((equal preprocessor "") ; internal preprocessor
                 (preprocess files base-dir include-dirs options ienv state))
                ((not preprocessor)
                 (b* (((erp files state)
                       (input-files-read-files files base-dir state)))
                   (retok files nil state)))
                (t ; external preprocessor
                 (b* (((erp files state)
                       (preprocess-files
                        files
                        :path base-dir
                        :preprocessor preprocessor
                        :extra-args (input-files-complete-preprocess-extra-args
                                     preprocess-extra-args
                                     ienv))))
                   (retok files nil state))))))
       ;; Parsing is always required.
       (skip-control-lines (not (equal preprocessor "")))
       ((erp tunits) (parse-fileset files
                                    (ienv->dialect ienv)
                                    skip-control-lines
                                    keep-going))
       ;; We add the RESOLVED-INCLUDES mapping to the translation ensemble.
       ;; This will no longer be necessary once we store that information
       ;; directly in the #include ASTs, coming from our preprocessor.
       (tunits (change-trans-ensemble tunits
                                      :resolved-includes resolved-includes))
       ;; If only parsing is required, we are done.
       ((when (eq process :parse)) (retok tunits state))
       ;; Disambiguation is required, if we get here.
       ((erp tunits) (dimb-trans-ensemble tunits ienv keep-going))
       ;; If no validation is required, we are done.
       ((when (eq process :disambiguate)) (retok tunits state))
       ;; Validation is required, if we get here.
       ((erp tunits)
        (valid-trans-ensemble tunits ienv strict-merge keep-going)))
    (retok tunits state))

  ///

  (defret trans-ensemble-unambp-of-input-files-per-stage
    (implies (not erp)
             (trans-ensemble-unambp tunits))
    :hyp (not (equal process :parse))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-files-gen-events ((files string-listp)
                                (base-dir stringp)
                                (preprocessor string-optionp)
                                (preprocess-extra-args
                                 (or (acl2::string-stringlist-mapp
                                      preprocess-extra-args)
                                     (string-listp preprocess-extra-args)))
                                (options ppoptionsp)
                                (include-dirs string-listp)
                                (process input-files-process-inputp)
                                (const symbolp)
                                (strict-merge booleanp)
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
     With the internal preprocessor, we do that one stage at a time;
     otherwise, we do that one file at a time, which uses less memory.
     Besides the events, we also return the code ensemble
     resulting from processing the (possibly preprocessed) files,
     together with the implementation environment
     and the @(':strict-merge') flag.
     If the programmatic interface is being used,
     no events are actually generated."))
  (b* (((reterr) nil (irr-code-ensemble) state)
       ((erp tunits state)
        (if (equal preprocessor "")
            (input-files-per-stage files
                                   base-dir
                                   preprocessor
                                   preprocess-extra-args
                                   options
                                   include-dirs
                                   process
                                   strict-merge
                                   keep-going
                                   ienv
                                   state)
          (input-files-per-file files
                                base-dir
                                preprocessor
                                preprocess-extra-args
                                process
                                strict-merge
                                keep-going
                                ienv
                                state)))
       (code (make-code-ensemble :trans-units tunits
                                 :ienv ienv
                                 :strict-merge strict-merge))
       ;; Generate :CONST constant with the code ensemble.
       (events (if progp nil (list `(defconst ,const ',code)))))
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
                                                   base-dir
                                                   preprocess
                                                   preprocess-args
                                                   preprocess-options
                                                   include-dirs
                                                   process
                                                   (const-presentp booleanp)
                                                   const
                                                   strict-merge
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
     We also return the translation ensemble
     resulting from processing the (possibly preprocessed) files."))
  (b* (((reterr) '(_) (irr-code-ensemble) state)
       ((erp files
             base-dir
             preprocessor
             preprocess-extra-args
             options
             include-dirs
             process
             const
             strict-merge
             keep-going
             ienv)
        (input-files-process-inputs files-presentp
                                    files
                                    base-dir
                                    preprocess
                                    preprocess-args
                                    preprocess-options
                                    include-dirs
                                    process
                                    const-presentp
                                    const
                                    strict-merge
                                    keep-going
                                    ienv
                                    progp
                                    state))
       ((erp events code state)
        (input-files-gen-events files
                                base-dir
                                preprocessor
                                preprocess-extra-args
                                options
                                include-dirs
                                process
                                const
                                strict-merge
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
                        base-dir
                        preprocess
                        preprocess-args
                        preprocess-options
                        include-dirs
                        process
                        (const-presentp booleanp)
                        const
                        strict-merge
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
                                                   base-dir
                                                   preprocess
                                                   preprocess-args
                                                   preprocess-options
                                                   include-dirs
                                                   process
                                                   const-presentp
                                                   const
                                                   strict-merge
                                                   keep-going
                                                   ienv
                                                   nil
                                                   state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (acl2::value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection input-files-definition
  :short "Definition of the @(tsee input-files) macro."
  (defmacro input-files (&key (files 'nil files-presentp)
                              (base-dir '".")
                              (preprocess 'nil)
                              (preprocess-args 'nil)
                              (preprocess-options 'nil)
                              (include-dirs 'nil)
                              (process ':validate)
                              (const 'nil const-presentp)
                              (strict-merge 't)
                              (keep-going 'nil)
                              (ienv 'nil))
    `(make-event-terse
       (input-files-fn ',files-presentp
                       ,files
                       ',base-dir
                       ',preprocess
                       ,preprocess-args
                       ',preprocess-options
                       ,include-dirs
                       ',process
                       ',const-presentp
                       ',const
                       ',strict-merge
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
    "(input-files-prog :files              ...  ; required"
    "                  :base-dir           ...  ; default \".\""
    "                  :preprocess         ...  ; default nil"
    "                  :preprocess-args    ...  ; default nil"
    "                  :preprocess-options ...  ; default nil"
    "                  :include-dirs       ...  ; default nil"
    "                  :process            ...  ; default :validate"
    "                  :strict-merge       ...  ; default t"
    "                  :keep-going         ...  ; default nil"
    "                  :ienv               ...  ; default (ienv-default)"
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
                             base-dir
                             preprocess
                             preprocess-args
                             preprocess-options
                             include-dirs
                             process
                             (const-presentp booleanp)
                             const
                             strict-merge
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
                                                   base-dir
                                                   preprocess
                                                   preprocess-args
                                                   preprocess-options
                                                   include-dirs
                                                   process
                                                   const-presentp
                                                   const
                                                   strict-merge
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
                                   (base-dir '".")
                                   (preprocess 'nil)
                                   (preprocess-args 'nil)
                                   (preprocess-options 'nil)
                                   (include-dirs 'nil)
                                   (process ':validate)
                                   (const 'nil const-presentp)
                                   (strict-merge 't)
                                   (keep-going 'nil)
                                   (ienv 'nil))
    `(input-files-prog-fn ',files-presentp
                          ,files
                          ',base-dir
                          ',preprocess
                          ,preprocess-args
                          ',preprocess-options
                          ,include-dirs
                          ',process
                          ',const-presentp
                          ',const
                          ',strict-merge
                          ',keep-going
                          ',ienv
                          state)))
