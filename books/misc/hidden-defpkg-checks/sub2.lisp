(in-package "ACL2")

(encapsulate
  ()
  (local (include-book "pkg2")) ; no_port
  (defthm a-in-acl2-pkg
    (implies (and (symbolp x)
                  (equal (symbol-package-name x) "MY-PKG"))
             (equal (symbol-package-name
                     (intern-in-package-of-symbol "A" x))
                    "ACL2"))
    :rule-classes nil))
