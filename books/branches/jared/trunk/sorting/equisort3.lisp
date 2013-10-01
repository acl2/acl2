; (certify-book "equisort3")

(in-package "ACL2")

(include-book "perm")
(include-book "ordered-perms")
(include-book "convert-perm-to-how-many")

(defthm equisort
  (implies (and (force (orderedp a))
                (force (orderedp b))
                (force (true-listp a))
                (force (true-listp b))
                (force (perm a b)))
           (equal (equal a b) t))
  :hints (("Goal" :use ordered-perms)))

(in-theory (disable equisort))

