(in-package "ACL2")

(include-book "help2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

(in-theory (disable append))

;;fails
(must-fail
 (defthm consp-of-append
   (implies (consp x)
            (consp (append x y)))))

(help2)

(must-be-redundant
 ;; The tool finds this proof:
 (defthm consp-of-append
   (implies (consp x)
            (consp (binary-append x y)))
   :hints (("Goal" :induct (binary-append x y)
            :in-theory (enable binary-append)))))
