(in-package "ACL2")

(include-book "acl2x-help")

(make-event
 (er-progn
  (thm (equal (append (append x y) z)
              (append x y z)))
  (value '(maybe-skip-proofs
           (defthm app-assoc
             (equal (append (append x y) z)
                    (append x y z)))))))
