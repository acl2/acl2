(in-package "ACL2")

;;; Define basic notions.
(include-book "riemann-defuns")

;;; Get definition of make-partition.
(include-book "integral-rcfn")

;;; Make this book available for the proof of the second lemma too.
(local (include-book "riemann-sum-approximates-integral-1"))

;;; The following should now be redundant.
(defthm riemann-sum-approximates-integral-1
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
                    (integral-rcfn a b))))

(encapsulate
 ()
 (local (include-book "riemann-sum-approximates-integral-2"))
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
                       (make-partition (car p) (car (last p)) (i-large-integer))))))))

(defthm riemann-sum-approximates-integral
  (implies (and (partitionp p)
                (equal a (car p))
                (equal b (car (last p)))
                (< a b)
                (standard-numberp a)
                (standard-numberp b)
                (i-small (mesh p)))
           (i-close (riemann-rcfn p)
                    (integral-rcfn a b)))
  :hints (("Goal"
           :in-theory
           (disable mesh riemann-rcfn make-partition)
           :use
           ((:instance
             i-close-transitive
             (x (riemann-rcfn p))
             (y (riemann-rcfn
                 (common-refinement
                  p
                  (make-partition (car p) (car (last p)) (i-large-integer)))))
             (z (integral-rcfn a b)))))))
