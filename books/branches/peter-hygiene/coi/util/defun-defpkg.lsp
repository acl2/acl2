#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(defpkg "DEFUN" (cons 'acl2::val
		      (cons 'acl2::met 
			    (append *acl2-exports*
				    *common-lisp-symbols-from-main-lisp-package*))))


