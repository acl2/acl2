(in-package "ACL2")

(include-book "nsa-lemmas")
(include-book "defaxioms")

(defun between (x a b)
  (if (< a b)
      (and (<= a x) (<= x b))
    (and (<= b x) (<= x a))))

(defthm standard-part-<=-linear
  (implies (and (realp x) (realp y) (<= x y))
           (<= (standard-part x)
               (standard-part y)))
  :rule-classes :linear)

(defthm standard-part-preserves-between
  (implies (and (realp x)
                (realp y)
                (realp z)
                (between z x y))
           (between (standard-part z)
                    (standard-part x)
                    (standard-part y)))
  :rule-classes nil
  :hints (("Goal"
           :cases
           ((<= (standard-part x)
                (standard-part z))))))
