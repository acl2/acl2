(in-package "ACL2")

(include-book "partition-defuns")

; The prover's first attempt to prove partitionp-make-partition-rec
; results in generalization being performed on the following subgoal.
; Generalization is usually a bad sign, and in this case the proof
; eventually fails.  However, it is clear that the right-hand side of
; the conclusion is equal to (+ a delta), which leads to the rewrite
; rule car-make-partition-rec below.
#|
(IMPLIES (AND (INTEGERP N)
              (< 0 N)
              (PARTITIONP (MAKE-PARTITION-REC (+ A DELTA)
                                              DELTA (+ -1 N)))
              (RATIONALP DELTA)
              (< 0 DELTA)
              (RATIONALP A))
         (< A
            (CAR (MAKE-PARTITION-REC (+ A DELTA)
                                     DELTA (+ -1 N)))))
|#

(defthm car-make-partition-rec
  (equal (car (make-partition-rec a delta n))
         a))

; Unfortunately, the proof of partitionp-make-partition-rec still
; fails at this point.  This time we again see an appropriate proof by
; induction, but now with the following subgoal that suggests the
; lemma below.
#|
(IMPLIES (AND (RATIONALP DELTA)
              (< 0 DELTA)
              (RATIONALP A))
         (PARTITIONP (MAKE-PARTITION-REC A DELTA 1)))
|#
; The use of syntaxp below is necessary in order to prevent
; the proof of partitionp-make-partition-rec to from failing because
; the prover does not try to induct.  A different solution to that
; problem is to give the :hints (("Goal" :induct t)) for
; partitionp-make-partition-rec.  Yet a third solution is to avoid
; these subsidiary lemmas completely in favor of expand hints on
; partitionp-make-partition-rec,
#|
    :hints (("Goal"
             :expand
             ((make-partition-rec (+ a delta)
                                  delta (+ -1 n))
              (make-partition-rec a delta 1))))
|#

(defthm make-partition-rec-open
  (implies (and (integerp n)
                (< 0 n)
                (syntaxp (quotep n))) ; only open on constants n
           (equal (make-partition-rec a delta n)
                  (cons a  (make-partition-rec (+ a delta) delta (- n 1))))))

(defthm partitionp-make-partition-rec
  (implies (and (not (zp n))
                (rationalp delta)
                (< 0 delta)
                (rationalp a))
           (partitionp (make-partition-rec a delta n))))
