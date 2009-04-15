#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

;(include-book "list-exports" :dir :lists)
(ld "list-exports.lsp" :dir :lists)

(defpkg "ALIST"
;	(remove-duplicates-eql ;no longer necessary due to change in ACL2
         `(,@*acl2-exports*
           ,@*common-lisp-symbols-from-main-lisp-package*
	   ,@LIST::*exports*
	   LIST::len-len-induction)
;         )
         )

           
           
