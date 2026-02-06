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

(defmacro test-preproc (files &key std gcc clang include-dirs expected)
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
         (base-dir ".")
         (include-dirs ,include-dirs)
         (ienv (change-ienv (ienv-default) :version version))
         ((mv erp fileset state)
          (pproc-files files base-dir include-dirs ienv state 1000000000)))
      (mv (if erp
              (cw "~@0" erp) ; CW returns NIL, so ASSERT!-STOBJ fails
            (or (equal fileset ,expected)
                (cw "Actual:~%~x0" ; CW returns nil (see above)
                    (fileset-to-string-map fileset))))
          state))
    state))

;;;;;;;;;;;;;;;;;;;;

; Specialization to one file.

(defmacro test-preproc-1 (file expected &key std gcc clang include-dirs)
  `(test-preproc '(,file)
                 :std ,std
                 :gcc ,gcc
                 :clang ,clang
                 :include-dirs ,include-dirs
                 :expected (fileset-of ,file ,expected)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Show result of preprocessing.

(defmacro show-preproc (files &key std gcc clang include-dirs)
  `(assert!-stobj
    (b* ((version (if (or (not ,std)
                          (= ,std 17))
                      (cond (,gcc (c::version-c17+gcc))
                            (,clang (c::version-c17+clang))
                            (t (c::version-c17)))
                    (cond (,gcc (c::version-c23+gcc))
                          (,clang (c::version-c23+clang))
                          (t (c::version-c23)))))(files ,files)
         (base-dir ".")
         (include-dirs ,include-dirs)
         (ienv (change-ienv (ienv-default) :version version))
         ((mv erp fileset state)
          (pproc-files files base-dir include-dirs ienv state 1000000000))
         (- (if erp
                (cw "~@0" erp)
              (cw "Result:~%~x0" (fileset-to-string-map fileset)))))
      (mv t state))
    state))

;;;;;;;;;;;;;;;;;;;;

; Specialization to one file.

(defmacro show-preproc-1 (file &key std gcc clang include-dirs)
  `(show-preproc '(,file)
                 :std ,std
                 :gcc ,gcc
                 :clang ,clang
                 :include-dirs ,include-dirs))
