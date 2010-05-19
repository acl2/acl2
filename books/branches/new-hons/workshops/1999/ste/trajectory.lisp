(in-package "ACL2")

(include-book "circuit")

(defuntyped t-p ((r-p r) (c-p c)) t
  booleanp nil
  (case-match r
	      ((s1 s2 . ss)
	       (and (s-lte (c-eval c s1) s2)
		    (t-p (cons s2 ss) c)))
	      (& t)
	      ))

(defthm single-state-run-is-trajectory
  (implies (and (c-p c)
		(r-p r)
		(equal (len r) 1)
		)
	   (t-p r c)))

