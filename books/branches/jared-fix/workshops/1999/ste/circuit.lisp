(in-package "ACL2")

(include-book "expression")

(deflisttyped c-p e-p)

(defuntyped c-eval ((c-p c) (s-p s)) t
  s-p nil
  (if (consp c)
      (cons (e-eval (car c) s)
	    (c-eval (cdr c) s))
    nil))


(defthm s-lte-c-eval-is-s-lte
  (implies (and (c-p c)
		(s-p s1)
		(s-p s2)
		(equal (len s1) (len s2))
		(s-lte s1 s2)
		)
	   (s-lte (c-eval c s1)
		  (c-eval c s2)))  )

(defuntyped c-run ((naturalp n) (c-p c) (s-p s)) t
  r-p nil
  (if (equal n 0)
      (list s)
    (cons s (c-run (1- n) c (c-eval c s)))))


(defthm c-run-len
  (implies (and (naturalp n)
		(c-p c)
		(s-p s)		)
	   (equal (len (c-run n c s))
		  (+ n 1)))
  )
