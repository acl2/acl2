(in-package "ACL2")

;(b1) - this fails because "bar" contains a defaxiom and when we do
;      the chk-embedded-event-form on the forms in "bar" we know
;      in-local-flg.
(local (include-book "bar" :ttags (:writes-okp)))

(defthm bad
  nil
  :rule-classes nil
  :hints (("Goal" :use bad-ax)))
