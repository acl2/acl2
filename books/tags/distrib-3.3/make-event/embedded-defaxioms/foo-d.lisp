(in-package "ACL2")

;(d) - this fails because we don't permit local defaxioms inside encapsulate
(encapsulate () (local (defaxiom bad-ax nil :rule-classes nil))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))

)
