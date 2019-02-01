;; DEFPKG for farrays
;; Includes the usual stuff plus b*

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "FARRAY"
  (union-eq
   '(
     define
     defsection
     defxdoc
     b*
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))
