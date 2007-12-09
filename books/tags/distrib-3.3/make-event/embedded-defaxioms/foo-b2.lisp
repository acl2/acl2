(in-package "ACL2")

(defmacro my-local (x) `(local ,x))

;(b2) - as with (b1) but with macro for local
(my-local (include-book "bar" :ttags (:writes-okp)))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))
