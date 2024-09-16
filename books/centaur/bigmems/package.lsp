(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defpkg "BIGMEMS" (union-eq *acl2-exports* std::*std-exports*))
(defconst bigmems::*bigmems-exports*
          '(bigmems::bigmems bigmems::mem$ap bigmems::read-mem$a bigmems::write-mem$a
            bigmems::create-mem$a bigmems::bigmems))
