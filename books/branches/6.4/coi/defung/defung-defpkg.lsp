#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(defpkg "DEFUNG"
  (append '(acl2::llist
	    acl2::l<
	    acl2::D<  ;; What is this??
	    acl2::val
	    acl2::met
	    acl2::*nil*
	    acl2::*t*
	    acl2::must-be-equal
	    acl2::*EC-CALL-BAD-OPS*
	    )
	  (union-eq *acl2-exports*
		    *common-lisp-symbols-from-main-lisp-package*)))

