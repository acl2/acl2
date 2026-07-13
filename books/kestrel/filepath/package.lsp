(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defpkg "FILEPATH"
  (union-eq
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   std::*std-exports*))
