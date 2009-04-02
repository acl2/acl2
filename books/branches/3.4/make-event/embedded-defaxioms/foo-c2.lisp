(in-package "ACL2")

(defmacro my-local (x) `(local ,x))

;(c2)
(encapsulate () (my-local (include-book "bar" :ttags (:writes-okp)))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))

)
