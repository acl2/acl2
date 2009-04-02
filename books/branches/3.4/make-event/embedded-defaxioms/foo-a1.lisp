(in-package "ACL2")

(defmacro my-local (x) `(local ,x))

;(a1) - this should fail directly because of local defaxiom
(local (defaxiom bad-ax nil :rule-classes nil))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))
