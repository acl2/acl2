#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

; (ld "Makefile.acl2")

(defpkg "SYN"
  (set-difference-equal
   *acl2-exports*
   '(acl2::defevaluator
     defevaluator-form
     nth
     null
     nil
     apply
     ifp
     consp cons car cdr
     quotep enquote dequote
     appendp append
     arg
     and
     if
     len
     )))
