(in-package "ACL2")

(defmacro my-local (x) `(local ,x))

;(a21) - this should fail because of macro expanding to local defaxiom
(my-local (defaxiom bad-ax nil :rule-classes nil))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))
