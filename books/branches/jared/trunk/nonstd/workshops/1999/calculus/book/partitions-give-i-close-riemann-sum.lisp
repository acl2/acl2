(in-package "ACL2")

(include-book "riemann-defuns")

(encapsulate
 ()
 (local (include-book "refinement-makes-i-small-change"))
 (defthm refinement-makes-i-small-change
   (implies (and (strong-refinement-p p1 p2)
                 (standard-numberp (car p1))
                 (standard-numberp (car (last p1)))
                 (i-small (mesh p2)))
            (i-small (- (riemann-rcfn p1)
                        (riemann-rcfn p2))))))

(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(defthm partitions-give-i-close-riemann-sum
  (implies (and (partitionp2 p1 p2)
                (refinement-p p1 p2)
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-close (riemann-rcfn p1)
                    (riemann-rcfn p2)))
  :hints
  (("Goal"
    :in-theory (union-theories '(i-close)
                               (disable riemann-rcfn mesh)))))
