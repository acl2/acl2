; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg  "M1"
  (set-difference-equal
   (union-eq '(defp measure l< delta preprocess fast-loop fast correct-loop correct
                pairlis-x2)
         (union-eq *common-lisp-symbols-from-main-lisp-package*
                   *acl2-exports*))
   '(PC PROGRAM ID PUSH POP STEP COMPILE COROLLARY)))
