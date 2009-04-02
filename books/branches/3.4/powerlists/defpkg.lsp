;; This just sets up the environment...

;(value :q)
;(setq si::*multiply-stacks* 2)

(defpkg "U"
  (union-eq *acl2-exports*
	    *common-lisp-symbols-from-main-lisp-package*))
(defpkg "STRUCTURES"
  (union-eq
   '(DEFSTRUCTURE)			;The main macro exported by this book.
   (union-eq
    *acl2-exports*
    (union-eq
     *common-lisp-symbols-from-main-lisp-package*
     '(ACCESS ARGLISTP *BUILT-IN-EXECUTABLE-COUNTERPARTS*
        CHANGE CONSTANT DEFREC ER *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*
        HARD LEGAL-VARIABLE-OR-CONSTANT-NAMEP MAKE MSG
        REASON-FOR-NON-KEYWORD-VALUE-LISTP STATE-GLOBAL-LET*

       u::defloop u::force-term-list
       u::get-option-argument u::get-option-as-flag
       u::get-option-check-syntax u::get-option-entry
       u::get-option-entries u::get-option-member
       u::get-option-subset u::pack-intern
       u::unique-symbols)))))

; Before ACL2 Version 2.5 we unioned the following additional
; symbols into the imports of the package below.

; (defconst *missing-acl2-exports*
;   '(set-verify-guards-eagerness
;     booleanp
;     acl2-numberp
;     e0-ord-<
;     defequiv
;     defcong
;     binary-+
;     fix
;     realfix
;     ifix
;     true-listp
;     zp))

(defpkg "POWERLISTS"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))
