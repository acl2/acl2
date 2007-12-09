(in-package "ACL2")

;(e) - this fails because don't permit defaxioms in encapsulates
(encapsulate () (defaxiom bad-ax nil :rule-classes nil)

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))

)
