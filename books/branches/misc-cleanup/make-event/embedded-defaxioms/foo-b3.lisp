(in-package "ACL2")

;(b3) - as with (b1) but with two levels of include-book
(local (include-book "baruser" :ttags (:writes-okp)))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))
