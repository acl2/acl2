(in-package "DJVM")
(include-book "../../BCV/typechecker")


(acl2::set-verify-guards-eagerness 0)
(defun fake-env (scl)
  (bcv::makeenvironment 'class 'method 'returntype 'mergedcode 'maxstack
                       'handlers scl))




(acl2::set-verify-guards-eagerness 2)


(include-book "base-locals")
