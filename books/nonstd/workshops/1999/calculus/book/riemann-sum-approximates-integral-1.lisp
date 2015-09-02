(in-package "ACL2")

(include-book "defaxioms")

;;; Define basic notions.
(include-book "riemann-defuns")

;;; General-purpose lemmas, proved at first in order to prove
;;; riemann-bound.
(include-book "riemann-lemmas")

(include-book "integral-rcfn")
(include-book "integral-rcfn-lemmas")

(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(encapsulate
 ()
 (local (include-book "partitions-give-i-close-riemann-sum"))
 (defthm partitions-give-i-close-riemann-sum
   (implies (and (partitionp2 p1 p2)
                 (refinement-p p1 p2)
                 (standard-numberp (car p1))
                 (standard-numberp (car (last p1)))
                 (i-small (mesh p2)))
            (i-close (riemann-rcfn p1)
                     (riemann-rcfn p2)))))

;;; standard-part-is-idempotent and standard-part-+ were initially
;;; included here, and standard-part-is-i-close and
;;; i-close-standard-part-2 were moved to nsa-lemmas.lisp.

;;; The missing step now is to consider the common refinement of p and
;;; (MAKE-PARTITION (CAR P) (CAR (LAST P)) (I-LARGE-INTEGER)).
;;; We make these local, and do not put these in a library, because we
;;; prefer not to hang rewrite rules on car.

;;; Note:  The following two lemmas are needed for
;;; riemann-sum-approximates-integral-2-commuted in
;;; riemann-sum-approximates-integral-2.lisp.  Thus, they need to be
;;; top-level exports of this file, in departure from our convention
;;; that only the last lemma in the file is generally of external
;;; interest.

(defthm car-common-refinement
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car p1) (car p2)))
           (equal (car (common-refinement p1 p2))
                  (car p1))))

(defthm car-last-common-refinement
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car (last p2))))
           (equal (car (last (common-refinement p1 p2)))
                  (car (last p1)))))

;;; After rearranging lemmas, got rid of limited-is-<-positive-i-large
;;; but proved this one instead (taken from sum-of-integrals.lisp):
(defthm i-large-integer-is-greater-than-1
  (< 1 (i-large-integer))
  :hints (("Goal" :use
           (i-large-integer-is-large
            (:instance large-if->-large
                       (y 1)
                       (x (i-large-integer))))
           :in-theory
           (disable i-large-integer-is-large
                    large-if->-large))))

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
                    (integral-rcfn a b)))
  :hints (("Goal"
           :in-theory
           (disable mesh riemann-rcfn make-partition))))

