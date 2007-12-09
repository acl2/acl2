; Contributed by Scott L. Burson; based on Makefile in this directory.

(in-package "ACL2")

(ubt! 1)

(certify-book "array1" 0)
:u

(certify-book "list-defuns" 0)
:u

(certify-book "list-defthms" 0)
:u

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))
(certify-book "utilities" 1)
:u :u

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))
(certify-book "deflist" 1)
:u :u

(certify-book "list-theory" 0)
:u

(certify-book "set-defuns" 0)
:u

(certify-book "set-defthms" 0)
:u

(certify-book "set-theory" 0)
:u

(certify-book "alist-defuns" 0)
:u

(certify-book "alist-defthms" 0)
:u

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))
(certify-book "defalist" 1)
:u :u

(certify-book "alist-theory" 0)
:u

(defpkg "U" (union-eq *acl2-exports*
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
(certify-book "structures" 2)
:u :u :u

(certify-book "number-list-defuns" 0)
:u

(certify-book "number-list-defthms" 0)
:u

(certify-book "number-list-theory" 0)
:u
