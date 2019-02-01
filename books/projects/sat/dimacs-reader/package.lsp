;; DEFPKG for DIMACS-READER
;; Includes the usual stuff plus b*

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "DIMACS-READER"
  (union-eq
   '(
     define
     defsection
     defxdoc
     b*
     implode
     explode
     rev
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))
