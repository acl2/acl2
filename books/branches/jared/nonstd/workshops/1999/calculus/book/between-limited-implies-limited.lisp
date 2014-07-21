(in-package "ACL2")

;;; This book can be included in its entirety.

(include-book "nsa-lemmas")

(defun between (x a b)
  (if (< a b)
      (and (<= a x) (<= x b))
    (and (<= b x) (<= x a))))

(defthm between-limited-implies-limited
  (implies (and (between z x y)
                (realp x) (i-limited x)
                (realp y) (i-limited y)
                (realp z))
           (i-limited z))
  :hints (("Goal"
           :use
           ((:instance
             large-if->-large
             (y (max (abs x) (abs y)))
             (x z))))))
