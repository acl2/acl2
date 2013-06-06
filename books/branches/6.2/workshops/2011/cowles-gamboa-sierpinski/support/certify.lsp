(certify-book "r-no-cover")
:u

(certify-book "s-no-cover1")
:u

(certify-book "s-no-cover")
:u

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))

(certify-book "verifying-macros" 1)
