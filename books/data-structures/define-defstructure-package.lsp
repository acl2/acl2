;; Define the STRUCTURES package.

(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "DEFSTRUCTURE"
  (union-eq
   '(DEFSTRUCTURE) ;The main macro exported by this book.
   (union-eq
    *acl2-exports*
    (union-eq
     *common-lisp-symbols-from-main-lisp-package*
     '(ACCESS ARGLISTP *BUILT-IN-EXECUTABLE-COUNTERPARTS*
              CHANGE CONSTANT DEFREC ER *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*
              HARD LEGAL-VARIABLE-OR-CONSTANT-NAMEP MAKE MSG
              REASON-FOR-NON-KEYWORD-VALUE-LISTP STATE-GLOBAL-LET*
              defxdoc defsection

              u::defloop u::force-term-list
              u::get-option-argument u::get-option-as-flag
              u::get-option-check-syntax u::get-option-entry
              u::get-option-entries u::get-option-member
              u::get-option-subset u::pack-intern
              u::unique-symbols)))))
