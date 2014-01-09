(in-package "ACL2")

#|
Goals:
1. A structured, organized presentation.
2. Some history of how I did things.
3. Replayability as I go along (endangered by modifying base of
lemmas).

The tension is between leaving basic lemmas in place and moving them
to a lemma repository.

Why not encapsulate?  Because it's not all that pretty and it doesn't
solve the tension.  But maybe it's worth a try to use encapsulate.
Except:  Defaxiom isn't allowed inside it.

|#

;;; Define basic notions.
(include-book "riemann-defuns")

;;; General-purpose lemmas, proved at first in order to prove
;;; riemann-bound.
(include-book "riemann-lemmas")

(include-book "integral-rcfn")

(encapsulate
 ()
 (local (include-book "riemann-sum-approximates-integral"))

 (defthm riemann-sum-approximates-integral
   (implies (and (partitionp p)
                 (equal a (car p))
                 (equal b (car (last p)))
                 (< a b)
                 (standard-numberp a)
                 (standard-numberp b)
                 (i-small (mesh p)))
            (i-close (riemann-rcfn p)
                     (integral-rcfn a b)))))
