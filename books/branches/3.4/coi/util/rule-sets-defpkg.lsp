#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(defpkg "RULE-SETS"
  (remove 'assert
  (remove 'version
	  (append *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))))
