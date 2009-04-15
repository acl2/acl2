#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "instance-defpkg.lsp")

(defpkg "COMPUTED-HINTS"
  (union-eq '(mfc-ancestors 
	      mfc-clause
	      string-for-tilde-@-clause-id-phrase
	      INSTANCE::instance-rewrite)
    (union-eq *acl2-exports*
  	      *common-lisp-symbols-from-main-lisp-package*)))
