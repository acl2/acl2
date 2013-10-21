(in-package "ACL2")

(include-book "run")

(defuntyped e-p (e) t
  booleanp nil
  (if (naturalp e)
      t
    (if (b-p e)
	t
      (case-match e
		  (('not x)   (e-p x))
		  (('and x y) (and (e-p x) (e-p y)))
		  (&          nil)))))


(defuntyped e-eval ((e-p e) (s-p s)) t
  b-p 'x
  (if (n-p e s)
      (nth e s)
    (if (b-p e)
	e
      (case-match e
		  (('not x)   (b-not (e-eval x s)))
		  (('and x y) (b-and (e-eval x s) (e-eval y s)))
		  (&          'x)))))




(defthm e-eval-of-s-lte-is-b-lte
  (implies (and (s-p s1)
		(s-p s2)
		(equal (len s1) (len s2))
		(s-lte s1 s2)
		(e-p e)
		)
	   (b-lte (e-eval e s1)
		  (e-eval e s2)))
  )


