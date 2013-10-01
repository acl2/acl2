(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-sum-approximates-integral-1")

(defthm riemann-sum-approximates-integral-2-commuted
  (implies (and (partitionp p)
                (equal a (car p))
                (equal b (car (last p)))
                (< a b)
                (standard-numberp a)
                (standard-numberp b)
                (i-small (mesh p)))
           (i-close (riemann-rcfn
                     (common-refinement
                      p
                      (make-partition (car p) (car (last p)) (i-large-integer))))
                    (riemann-rcfn p)))
  :hints (("Goal"
           :in-theory
           (disable mesh riemann-rcfn make-partition))))

(defthm riemann-sum-approximates-integral-2
  (implies (and (partitionp p)
                (equal a (car p))
                (equal b (car (last p)))
                (< a b)
                (standard-numberp a)
                (standard-numberp b)
                (i-small (mesh p)))
           (i-close (riemann-rcfn p)
                    (riemann-rcfn
                     (common-refinement
                      p
                      (make-partition (car p) (car (last p)) (i-large-integer))))))
  :hints (("Goal"
           :in-theory
           (union-theories '(i-close-symmetric)
                           (disable mesh riemann-rcfn make-partition)))))
