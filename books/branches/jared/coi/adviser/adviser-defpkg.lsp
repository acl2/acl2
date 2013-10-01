#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(defpkg "ADVISER" 
;  (remove-duplicates-eql  ;no longer necessary due to change in ACL2
   `(,@*acl2-exports*
     ,@*common-lisp-symbols-from-main-lisp-package*
     mfc-ancestors
     mfc-clause)
   ;)
   )
