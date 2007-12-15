; Contributed by Scott L. Burson; based on Makefile in this directory.

(in-package "ACL2")

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))
(certify-book "ihs-init" 1)
:u :u

(certify-book "ihs-theories" 0)
:u

(certify-book "math-lemmas" 0)
:u

(certify-book "quotient-remainder-lemmas" 0)
:u

(certify-book "logops-definitions" 0)
:u

(certify-book "ihs-definitions" 0)
:u

(certify-book "logops-lemmas" 0)
:u

(certify-book "ihs-lemmas" 0)
:u

(certify-book "@logops" 0)
:u
