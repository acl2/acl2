(in-package "ACL2")

;(c1) - this fails because we don't permit local include-books with
;      defaxiom, just as with (b1)
(encapsulate () (local (include-book "bar" :ttags (:writes-okp)))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))

)
