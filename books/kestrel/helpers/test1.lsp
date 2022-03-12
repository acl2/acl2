(in-package "ACL2")

(include-book "help2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

(in-theory (disable pos-listp nat-listp))

(must-fail
 ;;fails:
 (defthm nat-listp-when-pos-listp
   (implies (pos-listp x)
            (nat-listp x))))

(help2)

;; TODO: Have the tool try to combine the 2 steps that it finds
(must-be-redundant ; todo: make a quiet version of this
 ;; The tool finds this proof:
 (defthm nat-listp-when-pos-listp-induct0
   (implies (and (consp x)
                 (integerp (car x))
                 (< 0 (car x))
                 (nat-listp (cdr x))
                 (pos-listp (cdr x)))
            (nat-listp x))
   :hints (("Goal" :in-theory (enable (:definition nat-listp)))))
 (defthm nat-listp-when-pos-listp
   (implies (pos-listp x)
            (nat-listp x))
   :hints (("Goal" :induct (pos-listp x)
            :in-theory (enable pos-listp)))))
