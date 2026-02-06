; Wrappers of the C transformations, suitable for use with run-json-command
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add wrappers of additional transformations.

;; We might be able to avoid creating a different wrapper for each
;; transformation, but consider the case when the arguments cannot be clearly
;; split into arguments passed to input-files/output-files and arguments passed
;; to the transformation (e.g., if the extensions argument is passed to both).

(include-book "kestrel/c/transformation/add-section-attr" :dir :system)
(include-book "kestrel/c/transformation/split-gso" :dir :system)
(include-book "kestrel/c/transformation/simpadd0" :dir :system)
(include-book "kestrel/c/transformation/split-fn" :dir :system)
(include-book "kestrel/c/transformation/wrap-fn" :dir :system)
(include-book "kestrel/c/syntax/input-files" :dir :system)
(include-book "kestrel/c/syntax/output-files" :dir :system)
(include-book "kestrel/utilities/lookup-keyword" :dir :system)
(include-book "kestrel/typed-lists-light/string-list-listp" :dir :system)
(include-book "kestrel/alists-light/lookup-equal-def" :dir :system)
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/utilities/keyword-value-lists2" :dir :system))

;; :OLD-DIR and :NEW-DIR are among the non-transformation-specific arguments.
;; We assume transformation-specific arguments are checked by the individual
;; transformations.
(defun check-dir-args (old-dir new-dir ctx)
  (declare (xargs :guard (and (stringp old-dir)
                              (stringp new-dir))))
  (b* (;; ((when (eq :none old-dir))
       ;;  (er hard? ctx "The :old-dir argument must be supplied."))
       ;; ((when (eq :none new-dir))
       ;;  (er hard? ctx "The :new-dir argument must be supplied."))
       ;; TODO: Consider allowing this, perhaps if the user sets an overwrite-ok argument:
       ((when (equal old-dir new-dir))
        (er hard? ctx "The :old-dir and :new-dir arguments must be different.")))
    nil))

;; Returns (mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions remaining-kv-list).
;; Changes the default for :preprocess to :auto
;; Changes the default for :extensions to :gcc.
(defun handle-common-args (kv-list ctx)
  (declare (xargs :guard t))
  (b* (((when (not (keyword-value-listp kv-list)))
        (er hard? ctx "Ill-formed args: ~x0." kv-list)
        (mv nil nil nil nil nil nil nil nil))
       ;; Handle :old-dir and :new-dir (both required):
       ((when (not (assoc-keyword :old-dir kv-list)))
        (er hard? ctx "Missing argument: old-dir.")
        (mv nil nil nil nil nil nil nil nil))
       (old-dir (lookup-keyword :old-dir kv-list))
       ((when (not (stringp old-dir)))
        (er hard? ctx "Bad argument: old-dir is not a string: ~x0." old-dir)
        (mv nil nil nil nil nil nil nil nil))
       ((when (not (assoc-keyword :new-dir kv-list)))
        (er hard? ctx "Missing argument: new-dir.")
        (mv nil nil nil nil nil nil nil nil))
       (new-dir (lookup-keyword :new-dir kv-list))
       ((when (not (stringp new-dir)))
        (er hard? ctx "Bad argument: new-dir is not a string: ~x0." new-dir)
        (mv nil nil nil nil nil nil nil nil))
       (- (check-dir-args old-dir new-dir ctx))
       (kv-list (remove-keyword :old-dir kv-list))
       (kv-list (remove-keyword :new-dir kv-list))
       ;; Handle :files (required):
       ((when (not (assoc-keyword :files kv-list)))
        (er hard? ctx "Missing argument: files.")
        (mv nil nil nil nil nil nil nil nil))
       (files (lookup-keyword :files kv-list))
       (kv-list (remove-keyword :files kv-list))
       ;; Change the default for :preprocess:
       (preprocess-suppliedp (assoc-keyword :preprocess kv-list))
       (preprocess (if preprocess-suppliedp
                       (lookup-keyword :preprocess kv-list)
                     :auto))
       (kv-list (remove-keyword :preprocess kv-list))
       ;; Handle the :preprocess-args:
       (preprocess-args-suppliedp (if (assoc-keyword :preprocess-args kv-list) t nil))
       (preprocess-args (lookup-keyword :preprocess-args kv-list))
       (preprocess-args-listp (string-listp preprocess-args))
       (preprocess-args-alistp (and (alistp preprocess-args)
                                    (string-listp (strip-cars preprocess-args))
                                    (string-list-listp (strip-cdrs preprocess-args))))
       ((when (not (or preprocess-args-listp
                       preprocess-args-alistp)))
        (er hard? ctx "Bad preprocess-args.  Should be either an array of strings (the preprocess args for the given file) or a JSON object mapping filepaths (strings) to the corresponding preprocess args (each a list of strings).")
        (mv nil nil nil nil nil nil nil nil))
       (preprocess-args (if preprocess-args-listp ; includes the NIL case
                            preprocess-args
                          (omap::from-alist preprocess-args)))
       (kv-list (remove-keyword :preprocess-args kv-list))
       ;; Change the default for :extensions:
       (extensions-suppliedp (assoc-keyword :extensions kv-list))
       (extensions
         (b* (((unless extensions-suppliedp)
               :gcc)
              (extensions-str? (lookup-keyword :extensions kv-list))
              ((when (not extensions-str?))
               nil)
              ((unless (stringp extensions-str?))
               (er hard? ctx "Bad extensions.  Should be either the string \"gcc\", the string \"clang\", or false."))
              (extensions-str (string-downcase extensions-str?)))
           (cond ((equal extensions-str "gcc") :gcc)
                 ((equal extensions-str "clang") :clang)
                 (t (er hard? ctx "Bad extensions.  Should be either the string \"gcc\", the string \"clang\", or false.")))))
       (kv-list (remove-keyword :extensions kv-list)))
    (mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions kv-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an event (a progn).
;; todo: error checking
;; todo: add preprocessor args, etc. (eventually make per-file)
;; could all files to be "all" instead of a list
(defun split-gso-wrapper (kv-list whole-form)
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ',files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ,@(and preprocess-args-suppliedp `(:preprocess-args ',preprocess-args))
                        :ienv (c$::ienv-default :extensions ,extensions))
       (c2c::split-gso *old-const*
                       *new-const*
                       ;; Pass through all other args:
                       ,@remaining-kv-list)
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for split-gso that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command.
(defmacro split-gso (&whole whole-form &rest kv-list)
  `(make-event (split-gso-wrapper ',kv-list ',whole-form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an event.
;; todo: error checking
;; todo: add preprocessor args, etc. (eventually make per-file)
;; could all files to be "all" instead of a list
(defun simpadd0-wrapper (kv-list whole-form)
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ',files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ,@(and preprocess-args-suppliedp `(:preprocess-args ',preprocess-args))
                        :ienv (c$::ienv-default :extensions ,extensions))
       (c2c::simpadd0 :const-old *old-const*
                      :const-new *new-const*
                      ;; Pass through all other args (currently, none):
                      ,@remaining-kv-list)
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for simpadd0 that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command
(defmacro simpadd0 (&whole whole-form &rest kv-list)
  `(make-event (simpadd0-wrapper ',kv-list ',whole-form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an event.
;; todo: error checking
;; todo: add preprocessor args, etc. (eventually make per-file)
;; could all files to be "all" instead of a list
(defun split-fn-wrapper (kv-list whole-form)
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ',files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ,@(and preprocess-args-suppliedp `(:preprocess-args ',preprocess-args))
                        :ienv (c$::ienv-default :extensions ,extensions))
       (c2c::split-fn *old-const*
                      *new-const*
                      ;; Pass through all other args:
                      ,@remaining-kv-list)
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for split-fn that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command
(defmacro split-fn (&whole whole-form &rest kv-list)
  `(make-event (split-fn-wrapper ',kv-list ',whole-form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an event.
;; todo: error checking
;; todo: add preprocessor args, etc. (eventually make per-file)
;; could all files to be "all" instead of a list
(defun wrap-fn-wrapper (kv-list whole-form)
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ',files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ,@(and preprocess-args-suppliedp `(:preprocess-args ',preprocess-args))
                        :ienv (c$::ienv-default :extensions ,extensions))
       (c2c::wrap-fn *old-const*
                     *new-const*
                     ;; Pass through all other args (currently, :targets):
                     ,@remaining-kv-list)
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for wrap-fn that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command
(defmacro wrap-fn (&whole whole-form &rest kv-list)
  `(make-event (wrap-fn-wrapper ',kv-list ',whole-form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-add-section-attr-input-aux (array-elems)
  (declare (xargs :guard (true-listp array-elems)))
  (if (endp array-elems)
      nil ; empty alist
    (let ((elem (first array-elems)))
      ;; Elem might be {"target": {"filepath": "file9.c", "ident": "foo"}, "section": "mysection"}
      (if (not (alistp elem))
          (er hard? 'make-add-section-attr-input-aux "Bad item in :attr option: ~x0." elem)
        (if (not (equal '("target" "section")
                        (strip-cars elem)))
            (er hard? 'make-add-section-attr-input-aux "Bad keys in item in :attr option (expected \"target\" and\"section\"): ~x0." elem)
          (let ((target (lookup-equal "target" elem))
                (section (lookup-equal "section" elem)))
            (if (not (alistp target))
                (er hard? 'make-add-section-attr-input-aux "Bad target in :attr option: ~x0." target)
              (if (not (equal '("filepath" "ident")
                              (strip-cars target)))
                  (er hard? 'make-add-section-attr-input-aux "Bad keys in target in :attr option: ~x0." target)
                (if (not (stringp section))
                    (er hard? 'make-add-section-attr-input-aux "Bad section in :attr option: ~x0." section)
                  (let ((filepath (lookup-equal "filepath" target))
                        (ident (lookup-equal "ident" target)))
                    (if (not (or (stringp filepath)
                                 (eq :null filepath)))
                        (er hard? 'make-add-section-attr-input-aux "Bad filepath in :attr option: ~x0." filepath)
                      (if (not (stringp ident))
                          (er hard? 'make-add-section-attr-input-aux "Bad ident in :attr option: ~x0." ident)
                        (acons (c2c::make-qualified-ident :filepath? (if (eq :null filepath)
                                                                         (c$::filepath-option-none)
                                                                       (c$::filepath-option-some (c$::filepath filepath)))
                                                          :ident (c$::ident ident))
                               section
                               (make-add-section-attr-input-aux (rest array-elems)))))))))))))))

;; The attrs have been converted from a JSON value to a Lisp value (see parsed-json-value-to-lisp-value)
(defund make-add-section-attr-input (attrs)
  (declare (xargs :guard t))
  (if (not (true-listp attrs))
      (er hard? 'make-add-section-attr-input ":attr option should be a list, but it is ~x0." attrs)
    (make-add-section-attr-input-aux attrs)))

;; Returns an event.
;; todo: error checking
(defun add-section-attr-wrapper (kv-list whole-form)
  (declare (xargs :guard (keyword-value-listp kv-list)))
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess preprocess-args-suppliedp preprocess-args extensions remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ',files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ,@(and preprocess-args-suppliedp `(:preprocess-args ',preprocess-args))
                        :ienv (c$::ienv-default :extensions ,extensions))
       (c2c::add-section-attr *old-const*
                              *new-const*
                              ;; The only transformation-specific option is :attrs (todo: check for any other args):
                              :attrs ',(make-add-section-attr-input (lookup-keyword :attrs remaining-kv-list)))
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for add-section-attr that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command
(defmacro add-section-attr (&whole whole-form &rest kv-list)
  `(make-event (add-section-attr-wrapper ',kv-list ',whole-form)))
