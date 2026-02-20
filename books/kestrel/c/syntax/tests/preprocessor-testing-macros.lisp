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
    (omap::update (filepath->unwrap filepath)
                  (acl2::nats=>string (filedata->unwrap filedata))
                  (fileset-map-to-string-map (omap::tail fileset-map)))))

(defun fileset-to-string-map (fileset)
  (fileset-map-to-string-map (fileset->unwrap fileset)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check result of preprocessing against expectation.

(defmacro test-preproc (files
                        &key
                        (base-dir '".")
                        include-dirs
                        full-expansion
                        (keep-comments 't)
                        (trace-expansion 't)
                        std
                        gcc
                        clang
                        expected)
  `(assert!-stobj
    (b* ((version (if (or (not ,std)
                          (= ,std 17))
                      (cond (,gcc (c::version-c17+gcc))
                            (,clang (c::version-c17+clang))
                            (t (c::version-c17)))
                    (cond (,gcc (c::version-c23+gcc))
                          (,clang (c::version-c23+clang))
                          (t (c::version-c23)))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (options (make-ppoptions :full-expansion ,full-expansion
                                  :keep-comments ,keep-comments
                                  :trace-expansion ,trace-expansion
                                  :no-errors/warnings nil))
         (ienv (change-ienv (ienv-default) :version version))
         ((mv erp fileset state) (preprocess files
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
                          std
                          gcc
                          clang)
  `(test-preproc '(,file)
                 :base-dir ,base-dir
                 :include-dirs ,include-dirs
                 :full-expansion ,full-expansion
                 :keep-comments ,keep-comments
                 :trace-expansion ,trace-expansion
                 :std ,std
                 :gcc ,gcc
                 :clang ,clang
                 :expected (fileset-of ,file ,expected)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Show result of preprocessing.

(defmacro show-preproc (files &key
                              (base-dir '".")
                              include-dirs
                              full-expansion
                              (keep-comments 't)
                              (trace-expansion 't)
                              std
                              gcc
                              clang)
  `(assert!-stobj
    (b* ((version (if (or (not ,std)
                          (= ,std 17))
                      (cond (,gcc (c::version-c17+gcc))
                            (,clang (c::version-c17+clang))
                            (t (c::version-c17)))
                    (cond (,gcc (c::version-c23+gcc))
                          (,clang (c::version-c23+clang))
                          (t (c::version-c23)))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (options (make-ppoptions :full-expansion ,full-expansion
                                  :keep-comments ,keep-comments
                                  :trace-expansion ,trace-expansion
                                  :no-errors/warnings nil))
         (ienv (change-ienv (ienv-default) :version version))
         ((mv erp fileset state) (preprocess files
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
                          std
                          gcc
                          clang)
  `(show-preproc '(,file)
                 :base-dir ,base-dir
                 :include-dirs ,include-dirs
                 :full-expansion ,full-expansion
                 :keep-comments ,keep-comments
                 :trace-expansion ,trace-expansion
                 :std ,std
                 :gcc ,gcc
                 :clang ,clang))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check directive-preserving expansion against full expansion.

(defun filemap-drop-absolute-paths (filemap)
  (b* (((when (omap::emptyp filemap)) nil)
       ((mv path data) (omap::head filemap))
       (new-filemap-tail (filemap-drop-absolute-paths (omap::tail filemap))))
    (if (path-absolutep (filepath->unwrap path))
        new-filemap-tail
      (omap::update path data new-filemap-tail))))

(defun fileset-drop-absolute-paths (fileset)
  (fileset (filemap-drop-absolute-paths (fileset->unwrap fileset))))

(defun ppart-to-tokens (part)
  (ppart-case
   part
   :line (plexemes-without-nontokens part.lexemes)
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
      (cw "Original tokens ~x0 differ from transformed tokens ~x1."
          tokens-original tokens-transformed))))

(defmacro test-preproc-fullexp (files
                                &key
                                (base-dir '".")
                                include-dirs
                                (keep-comments 't)
                                (trace-expansion 't)
                                std
                                gcc
                                clang)
  `(assert!-stobj
    (b* ((version (if (or (not ,std)
                          (= ,std 17))
                      (cond (,gcc (c::version-c17+gcc))
                            (,clang (c::version-c17+clang))
                            (t (c::version-c17)))
                    (cond (,gcc (c::version-c23+gcc))
                          (,clang (c::version-c23+clang))
                          (t (c::version-c23)))))
         (files ,files)
         (base-dir ,base-dir)
         (include-dirs ,include-dirs)
         (ienv (change-ienv (ienv-default) :version version))
         (options-preserve (make-ppoptions :full-expansion nil
                                           :keep-comments ,keep-comments
                                           :trace-expansion ,trace-expansion
                                           :no-errors/warnings nil))
         (options-expand (make-ppoptions :full-expansion t
                                         :keep-comments ,keep-comments
                                         :trace-expansion nil
                                         :no-errors/warnings nil))
         ((mv erp fileset state)
          (preprocess files base-dir include-dirs options-preserve ienv state))
         ((when erp)
          (mv (cw "Initial preprocessing fails: ~@0" erp) state))
         (tmp-dir (str::cat base-dir "/tmp"))
         (fileset (fileset-drop-absolute-paths fileset))
         ((mv erp state) (write-fileset fileset tmp-dir state))
         ((when erp)
          (mv (cw "File set writing fails: ~x0" erp) state))
         ((mv erp pfiles-original state)
          (pproc-files files base-dir include-dirs
                       options-expand ienv state 1000000000))
         ((when erp)
          (mv (cw "Full-expansion preprocessing of original files fails: ~@0"
                  erp)
              state))
         ((mv erp pfiles-transformed state)
          (pproc-files files tmp-dir include-dirs
                       options-expand ienv state 1000000000))
         ((when erp)
          (mv (cw "Full-expansion preprocessing of transformed files fails: ~@0"
                  erp)
              state)))
      (mv (compare-expanded-pfiles pfiles-original pfiles-transformed) state))
    state))
