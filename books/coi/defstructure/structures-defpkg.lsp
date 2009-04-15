#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

;(include-book "symbol-fns-exports" :dir :symbol-fns)
(ld "symbol-fns-exports.lsp" :dir :symbol-fns)

;bzo drop?
;(include-book "record-exports" :dir :records)
(ld "record-exports.lsp" :dir :records) 

;bzo
;(include-book "path-exports" :dir :paths) -ews
(ld "path-defpkg.lsp" :dir :paths)

;; Define the STRUCTURES package (and the U package).  The STRUCTURES and U packages are stolen from the books/
;; directory and put here so that we can modify them and refer to them more easily.  (We like to ld the books which
;; contain defpkgs, but we have no way to easily ld a book from the books/ directory without using an absolute
;; pathname.)   
;;-- Now we do, with :dir support on LDs in ACL2 version 2.9.3.  So I'm trying to make use of that   -ews

(ld "data-structures/define-u-package.lsp" :dir :system)

;; (defpkg "U" (union-eq *acl2-exports*
;;                       *common-lisp-symbols-from-main-lisp-package*))

;This differs somewhat from the version in books/data-structures/define-structures-package.lisp.  -ews

(defpkg "STRUCTURES"
  (union-eq
   symbol-fns::*symbol-fns-exports*
   (union-eq
    '(DEFSTRUCTURE DEFSTRUCTURE+) ;The main macros exported by defstructure.lisp
    (union-eq
     *acl2-exports*
     (union-eq
      *common-lisp-symbols-from-main-lisp-package*
      '(

	acl2::wfr

	path::sp
	path::gp
	path::gp-list
	path::psort

	ACCESS ARGLISTP *BUILT-IN-EXECUTABLE-COUNTERPARTS*
        CHANGE CONSTANT DEFREC ER *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*
        HARD LEGAL-VARIABLE-OR-CONSTANT-NAMEP MAKE MSG
        REASON-FOR-NON-KEYWORD-VALUE-LISTP STATE-GLOBAL-LET*
	
	u::defloop u::force-term-list
	u::get-option-argument u::get-option-as-flag
	u::get-option-check-syntax u::get-option-entry
	u::get-option-entries u::get-option-member
	u::get-option-subset u::pack-intern
	u::unique-symbols))))))





