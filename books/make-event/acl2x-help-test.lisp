(in-package "ACL2")

(include-book "acl2x-help")

(make-event-skip-proofs
 (er-progn
  (thm (equal (append (append x y) z)
              (append x y z)))
  (value '(defthm app-assoc
            (equal (append (append x y) z)
                   (append x y z))))))
