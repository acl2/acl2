(in-package "ACL2")

(local (include-book "float"))


(defun sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0 (if (< x 0) -1 1)))

(defthm sgn-of-not-rationalp
  (implies (not (rationalp x))
           (equal (sgn x) 0)))
