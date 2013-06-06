(in-package "ACL2")

(include-book "nsa-lemmas")

(defthm i-close-implies-abs-difference-small
  (implies (and (realp r)
                (standard-numberp r)
                (< 0 r)
                (realp x)
                (realp y)
                (i-close x y))
           (< (abs (- x y)) r))
  :hints (("Goal" :use
           (:instance small-<-non-small
                       (x (- x y)) (y r))
           :expand (i-small r)
           :in-theory (union-theories '(i-close)
                                      (disable small-<-non-small)))))
