#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

;(ld "list-defpkg.lsp" :dir :lists)

(defpkg "INSTANCE"
  (union-eq '()
    (union-eq *acl2-exports*
  	      *common-lisp-symbols-from-main-lisp-package*)))
