(in-package "ACL2")

(include-book "acl2x-help")

(make-event
 (er-progn
  (thm (equal (append (append x y) z)
              (append x y z)))
  (value '(skip-proofs?
           (defthm app-assoc
             (equal (append (append x y) z)
                    (append x y z)))))))
