(in-package "ACL2")

(local (make-event '(defaxiom foo nil :rule-classes nil)))

(defthm inconsistency
  nil
  :rule-classes nil
  :hints (("Goal" :use foo)))
