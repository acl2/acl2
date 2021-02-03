(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "sub1") ; no_port
(must-fail
 (include-book "sub2")) ; no_port
(include-book "pkg1") ; no_port
(must-fail
 (defthm contradiction
   nil
   :hints (("Goal" :use ((:instance a-not-in-acl2-pkg
                                    (x (intern$ "B" "MY-PKG")))
                         (:instance a-in-acl2-pkg
                                    (x (intern$ "B" "MY-PKG"))))))
   :rule-classes nil))
