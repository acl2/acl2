(in-package "ACL2")

(include-book "../lib1/arith")
(local (include-book "../../arithmetic/top"))

(defthm expt-positive-integer-type
    (implies (and (integerp a)
		  (integerp i)
		  (>= i 0))
	     (integerp (expt a i)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable expt))))


