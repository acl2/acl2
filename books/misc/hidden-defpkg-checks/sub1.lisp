(in-package "ACL2")

(encapsulate
  ()
  (local (include-book "pkg1")) ; no_port
  (defthm a-not-in-acl2-pkg
    (implies (and (symbolp x)
                  (equal (symbol-package-name x) "MY-PKG"))
             (equal (symbol-package-name
                     (intern-in-package-of-symbol "A" x))
                    "MY-PKG"))
    :rule-classes nil))
