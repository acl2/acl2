(in-package "ACL2")

(make-event '(local (defaxiom foo nil :rule-classes nil)))

(defthm inconsistency
  nil
  :rule-classes nil
  :hints (("Goal" :use foo)))
