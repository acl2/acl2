(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm strip-cars-of-reverse-list
  (equal (strip-cars (reverse-list x))
         (reverse-list (strip-cars x)))
  :hints (("Goal" :in-theory (enable reverse-list))))
