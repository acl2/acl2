;; Define the U package.

(in-package "ACL2")

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))
