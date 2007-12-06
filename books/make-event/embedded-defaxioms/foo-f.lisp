(in-package "ACL2")

(defmacro my-local (x) `(local ,x))

;(f) - this fails because of non-local include-book in an encapsulate
(encapsulate () (include-book "bar" :ttags (:writes-okp))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))

)
