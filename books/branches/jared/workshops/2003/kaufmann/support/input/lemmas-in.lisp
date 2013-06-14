(in-package "ACL2")

(include-book "defs-in")

(defthm %lemma-1
  (implies (true-listp x)
           (equal (%g2 x y) nil))
  :hints (("Goal" :in-theory (enable %g1 %g2))))
