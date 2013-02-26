#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

; (ld "Makefile.acl2")

;(ld "../lists/list-defpkg.lsp")

(defpkg "INSTANCE"
  (union-eq '()
    (union-eq *acl2-exports*
  	      *common-lisp-symbols-from-main-lisp-package*)))
