; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "REWRITE-CODE"
        (append
         ; "imports":
         '(value er-let* er-decode-logical-name getprop current-acl2-world
           stobjs-in cltl-command global-value soft)
         ; "exports":
         '(er-rewrite-form
           get-defun
           compute-copy-defun+rewrite
           assert-include-defun-matches-certify-defun
           copy-defun+rewrite
           copy-defun)
         (union-eq *acl2-exports*
                   *common-lisp-symbols-from-main-lisp-package*)))
