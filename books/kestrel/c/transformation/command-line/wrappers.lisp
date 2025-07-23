; Wrappers of the C transformations, suitable for use with run-json-command
;
; Copyright (C) 2025 Kestrel Institute
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
;; to the transformation (e.g., if the gcc argument is passed to both).

(include-book "kestrel/c/transformation/splitgso" :dir :system)
(include-book "kestrel/c/transformation/simpadd0" :dir :system)
(include-book "kestrel/c/syntax/input-files" :dir :system)
(include-book "kestrel/c/syntax/output-files" :dir :system)
(include-book "kestrel/utilities/lookup-keyword" :dir :system)
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
       ((when (equal old-dir new-dir))
        (er hard? ctx "The :old-dir and :new-dir arguments must be different.")))
    nil))

;; Returns (mv old-dir new-dir files preprocess gcc remaining-kv-list).
;; Changes the default for :preprocess to :auto
;; Changes the default for :gcc to t.
(defun handle-common-args (kv-list ctx)
  (declare (xargs :guard t))
  (b* (((when (not (keyword-value-listp kv-list)))
        (er hard? ctx "Ill-formed args: ~x0." kv-list)
        (mv nil nil nil nil nil nil))
       ;; Handle :old-dir and :new-dir (both required):
       ((when (not (assoc-keyword :old-dir kv-list)))
        (er hard? ctx "Missing argument: old-dir.")
        (mv nil nil nil nil nil nil))
       (old-dir (lookup-keyword :old-dir kv-list))
       ((when (not (stringp old-dir)))
        (er hard? ctx "Bad argument: old-dir is not a string: ~x0." old-dir)
        (mv nil nil nil nil nil nil))
       ((when (not (assoc-keyword :new-dir kv-list)))
        (er hard? ctx "Missing argument: new-dir.")
        (mv nil nil nil nil nil nil))
       (new-dir (lookup-keyword :new-dir kv-list))
       ((when (not (stringp new-dir)))
        (er hard? ctx "Bad argument: new-dir is not a string: ~x0." new-dir)
        (mv nil nil nil nil nil nil))
       (- (check-dir-args old-dir new-dir ctx))
       (kv-list (remove-keyword :old-dir kv-list))
       (kv-list (remove-keyword :new-dir kv-list))
       ;; Handle :files (required):
       ((when (not (assoc-keyword :files kv-list)))
        (er hard? ctx "Missing argument: files.")
        (mv nil nil nil nil nil nil))
       (files (lookup-keyword :files kv-list))
       (kv-list (remove-keyword :files kv-list))
       ;; Change the default for :preprocess:
       (preprocess-suppliedp (assoc-keyword :preprocess kv-list))
       (preprocess (if preprocess-suppliedp
                       (lookup-keyword :preprocess kv-list)
                     :auto))
       (kv-list (remove-keyword :preprocess kv-list))
       ;; Change the default for :gcc:
       (gcc-suppliedp (assoc-keyword :gcc kv-list))
       (gcc (if gcc-suppliedp
                (lookup-keyword :gcc kv-list)
              t))
       (kv-list (remove-keyword :gcc kv-list)))
    (mv old-dir new-dir files preprocess gcc kv-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an event (a progn).
;; todo: error checking
;; todo: add preprocessor args, etc. (eventually make per-file)
;; could all files to be "all" instead of a list
(defun splitgso-wrapper (kv-list whole-form)
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess gcc remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ,files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ;; :preprocess-args ; todo?
                        :gcc ,gcc)
       (c2c::splitgso *old-const*
                      *new-const*
                      ;; Pass through all other args:
                      ,@remaining-kv-list)
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for splitgso that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command.
(defmacro splitgso (&whole whole-form &rest kv-list)
  `(make-event (splitgso-wrapper ',kv-list ',whole-form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an event.
;; todo: error checking
;; todo: add preprocessor args, etc. (eventually make per-file)
;; could all files to be "all" instead of a list
(defun simpadd0-wrapper (kv-list whole-form)
  (b* ((ctx whole-form)
       ;; Pick out the args that are for input-files and output-files:
       ((mv old-dir new-dir files preprocess gcc remaining-kv-list)
        (handle-common-args kv-list ctx)))
    `(progn
       (c$::input-files :files ,files
                        :path ,old-dir
                        :const *old-const* ; todo: avoid name clash
                        :preprocess ,preprocess
                        ;; :preprocess-args ; todo
                        :gcc ,gcc)
       (c2c::simpadd0 *old-const*
                      *new-const*
                      ;; Pass through all other args (currently, none):
                      ,@remaining-kv-list)
       (c$::output-files :const *new-const*
                         :path ,new-dir))))

;; A wrapper for simpadd0 that takes all its arguments as alternating keywords/values.
;; This wrapper is in the ACL2 package, for ease of use by run-json-command
(defmacro simpadd0 (&whole whole-form &rest kv-list)
  `(make-event (simpadd0-wrapper ',kv-list ',whole-form)))
