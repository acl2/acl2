#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(defpkg "QUANT" 
  (revappend '(acl2::BASH-TERM-TO-DNF 
	       acl2::ADD-GENERALIZATION-PATTERN
	       acl2::genvar2 acl2::val acl2::met acl2::s acl2::g)
  (revappend *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)))
