; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../preprocessor")

(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Build a fileset from alternating paths and contents,
; e.g. (fileset-of "file1.c" "void f() {}" "file2.c" "int g(int x);").

(defmacro fileset-of (&rest paths+contents)
  `(fileset (fileset-map (list ,@paths+contents))))

(defun fileset-map (paths+contents)
  (b* (((when (endp paths+contents)) nil)
       (path (car paths+contents))
       (content (cadr paths+contents))
       (content (if (stringp content)
                    (acl2::string=>nats content)
                  content)))
    (omap::update (filepath path)
                  (filedata content)
                  (fileset-map (cddr paths+contents)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turn fileset into map from strings to strings.

(defun fileset-map-to-string-map (fileset-map)
  (b* (((when (omap::emptyp fileset-map)) nil)
       ((mv filepath filedata) (omap::head fileset-map)))
    (omap::update (filepath->string filepath)
                  (acl2::nats=>string (filedata->bytes filedata))
                  (fileset-map-to-string-map (omap::tail fileset-map)))))

(defun fileset-to-string-map (fileset)
  (fileset-map-to-string-map (fileset->files fileset)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check result of preprocessing against expectation.

(defmacro test-preproc (files
                        &key
                        (base-dir '".")
                        include-dirs
                        full-expansion
                        (keep-comments 't)
                        (trace-expansion 't)
                        dialect
                        expected)
  `(assert!-stobj
    (b* ((dialect (or ,dialect (c::make-dialect :std (c::standard-c17))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (options (make-ppoptions :full-expansion ,full-expansion
                                  :keep-comments ,keep-comments
                                  :trace-expansion ,trace-expansion
                                  :no-warnings nil))
         (ienv (change-ienv (ienv-default) :dialect dialect))
         ((mv erp fileset & state) (preprocess files
                                               base-dir
                                               include-dirs
                                               options
                                               ienv
                                               state)))
      (mv (if erp
              (cw "~@0" erp) ; CW returns NIL, so ASSERT!-STOBJ fails
            (or (equal fileset ,expected)
                (cw "Actual:~%~x0" ; CW returns nil (see above)
                    (fileset-to-string-map fileset))))
          state))
    state))

;;;;;;;;;;;;;;;;;;;;

; Specialization to one file.

(defmacro test-preproc-1 (file
                          expected
                          &key
                          (base-dir '".")
                          include-dirs
                          full-expansion
                          (keep-comments 't)
                          (trace-expansion 't)
                          dialect)
  `(test-preproc '(,file)
                 :base-dir ,base-dir
                 :include-dirs ,include-dirs
                 :full-expansion ,full-expansion
                 :keep-comments ,keep-comments
                 :trace-expansion ,trace-expansion
                 :dialect ,dialect
                 :expected (fileset-of ,file ,expected)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Show result of preprocessing.

(defmacro show-preproc (files &key
                              (base-dir '".")
                              include-dirs
                              full-expansion
                              (keep-comments 't)
                              (trace-expansion 't)
                              dialect)
  `(assert!-stobj
    (b* ((dialect (or ,dialect (c::make-dialect :std (c::standard-c17))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (options (make-ppoptions :full-expansion ,full-expansion
                                  :keep-comments ,keep-comments
                                  :trace-expansion ,trace-expansion
                                  :no-warnings nil))
         (ienv (change-ienv (ienv-default) :dialect dialect))
         ((mv erp fileset & state) (preprocess files
                                               base-dir
                                               include-dirs
                                               options
                                               ienv
                                               state))
         (- (if erp
                (cw "~@0" erp)
              (cw "Result:~%~x0" (fileset-to-string-map fileset)))))
      (mv t state))
    state))

;;;;;;;;;;;;;;;;;;;;

; Specialization to one file.

(defmacro show-preproc-1 (file
                          &key
                          (base-dir '".")
                          include-dirs
                          full-expansion
                          (keep-comments 't)
                          (trace-expansion 't)
                          dialect)
  `(show-preproc '(,file)
                 :base-dir ,base-dir
                 :include-dirs ,include-dirs
                 :full-expansion ,full-expansion
                 :keep-comments ,keep-comments
                 :trace-expansion ,trace-expansion
                 :dialect ,dialect))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check directive-preserving expansion against full expansion.

(defun strip-provenance (lexemes)
  (b* (((when (endp lexemes)) nil)
       (lexeme (car lexemes))
       (lexeme (if (plexeme-case lexeme :ident)
                   (change-plexeme-ident lexeme :provenance nil)
                 lexeme))
       (lexemes (strip-provenance (cdr lexemes))))
    (cons lexeme lexemes)))

(defun ppart-to-tokens (part)
  (ppart-case
   part
   :line (strip-provenance (plexemes-without-nontokens part.lexemes))
   :cond (er hard? 'ppart-to-tokens "Found conditional section ~x0." part)))

(defun ppart-list-to-tokens (parts)
  (cond ((endp parts) nil)
        (t (append (ppart-to-tokens (car parts))
                   (ppart-list-to-tokens (cdr parts))))))

(defun pfile-to-tokens (file)
  (ppart-list-to-tokens (pfile->parts file)))

(defun compare-expanded-pfiles (original transformed)
  (b* (((when (endp original))
        (if (endp transformed)
            t
          (cw "Transformed files have extra elements ~x0."
              (strip-cars transformed))))
       ((when (endp transformed))
        (cw "Transformed files miss elements ~x0."
            (strip-cars original)))
       ((cons name pfile-original) (car original))
       (name+pfile (assoc-equal name transformed))
       ((unless name+pfile)
        (cw "Transformed files miss element ~x0." name))
       (pfile-transformed (cdr name+pfile))
       (tokens-original (pfile-to-tokens pfile-original))
       (tokens-transformed (pfile-to-tokens pfile-transformed)))
    (if (equal tokens-original tokens-transformed)
        t
      (cw "File ~x0 fails." name))))

(defun filemap-relativize-absolute-paths (filemap)
  (b* (((when (omap::emptyp filemap)) nil)
       ((mv path data) (omap::head filemap))
       (new-path (if (path-absolutep (filepath->string path))
                     (filepath (subseq (filepath->string path) 1 nil))
                   path))
       (new-filemap-tail
        (filemap-relativize-absolute-paths (omap::tail filemap))))
    (omap::update new-path data new-filemap-tail)))

(defun fileset-relativize-absolute-paths (fileset)
  (fileset (filemap-relativize-absolute-paths (fileset->files fileset))))

(defun relativize-include-dirs (dirs dir)
  (cond ((endp dirs) nil)
        (t (cons (str::cat dir (car dirs))
                 (relativize-include-dirs (cdr dirs) dir)))))

(defmacro test-preproc-fullexp (files
                                &key
                                (base-dir '".")
                                include-dirs
                                (out-dir-prefix '"tmp") ; relative to base-dir
                                (keep-comments 't)
                                (trace-expansion 't)
                                dialect)
  `(assert!-stobj
    (b* (;; Setup.
         (dialect (or ,dialect (c::make-dialect :std (c::standard-c17))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (out-dir-prefix ,out-dir-prefix)
         (out-dir-initial (str::cat base-dir "/" out-dir-prefix "-initial"))
         (out-dir-original (str::cat base-dir "/" out-dir-prefix "-original"))
         (out-dir-transformed (str::cat base-dir "/" out-dir-prefix "-transformed"))
         (ienv (change-ienv (ienv-default) :dialect dialect))
         (options-preserve (make-ppoptions :full-expansion nil
                                           :keep-comments ,keep-comments
                                           :trace-expansion ,trace-expansion
                                           :no-warnings nil))
         (options-expand (make-ppoptions :full-expansion t
                                         :keep-comments ,keep-comments
                                         :trace-expansion nil
                                         :no-warnings nil))
         ;; Initial preprocessing.
         ((mv erp fileset-initial & state)
          (preprocess files base-dir include-dirs options-preserve ienv state))
         ((when erp)
          (mv (cw "Initial preprocessing fails: ~@0" erp) state))
         (fileset-initial
          (fileset-relativize-absolute-paths fileset-initial))
         ((mv erp state)
          (write-fileset fileset-initial out-dir-initial state))
         ((when erp)
          (mv (cw "Initial file set writing fails: ~x0" erp) state))
         ;; Full-expansion preprocessing of original files.
         ((mv erp pfiles-original & state)
          (pproc-files files base-dir include-dirs
                       options-expand ienv state 1000000000))
         ((when erp)
          (mv (cw "Full-expansion preprocessing of original files fails: ~@0"
                  erp)
              state))
         (fileset-original
          (fileset
           (string-pfile-alist-to-filepath-filedata-map pfiles-original)))
         (fileset-original
          (fileset-relativize-absolute-paths fileset-original))
         ((mv erp state)
          (write-fileset fileset-original out-dir-original state))
         ((when erp)
          (mv (cw "Original file set writing fails: ~x0" erp) state))
         ;; Full-expansion preprocessing of transformed files.
         (include-dirs-initial
          (relativize-include-dirs include-dirs out-dir-initial))
         ((mv erp pfiles-transformed & state)
          (pproc-files files out-dir-initial include-dirs-initial
                       options-expand ienv state 1000000000))
         ((when erp)
          (mv (cw "Full-expansion preprocessing of transformed files fails: ~@0"
                  erp)
              state))
         (fileset-transformed
          (fileset
           (string-pfile-alist-to-filepath-filedata-map pfiles-transformed)))
         (fileset-transformed
          (fileset-relativize-absolute-paths fileset-transformed))
         ((mv erp state)
          (write-fileset fileset-transformed out-dir-transformed state))
         ((when erp)
          (mv (cw "Transformed file set writing fails: ~x0" erp) state)))
      ;; Comparison.
      (mv (compare-expanded-pfiles pfiles-original pfiles-transformed)
          state))
    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro write-preproc (files
                         &key
                         (base-dir '".")
                         include-dirs
                         (out-dir '"./preproc-out")
                         (keep-comments 't)
                         (trace-expansion 't)
                         (full-expansion 'nil)
                         dialect)
  `(assert!-stobj
    (b* ((dialect (or ,dialect (c::make-dialect :std (c::standard-c17))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (out-dir ,out-dir)
         (options (make-ppoptions :full-expansion ,full-expansion
                                  :keep-comments ,keep-comments
                                  :trace-expansion ,trace-expansion
                                  :no-warnings nil))
         (ienv (change-ienv (ienv-default) :dialect dialect))
         ((mv erp fileset & state) (preprocess files
                                               base-dir
                                               include-dirs
                                               options
                                               ienv
                                               state))
         ((when erp) (mv (cw "Preprocessing fails: ~@0" erp) state))
         (fileset (fileset-relativize-absolute-paths fileset))
         ((mv erp state) (write-fileset fileset out-dir state))
         ((when erp) (mv (cw "File set writing fails: ~x0" erp) state)))
      (mv t state))
    state))
