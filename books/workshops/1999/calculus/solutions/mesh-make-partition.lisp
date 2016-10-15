(in-package "ACL2")

; Solution to Exercise 6.6.

; This solution is just barely simple enough that we do not create lemma books
; underneath it.

(include-book "partition-defuns")

; If one submits mesh-make-partition or thinks first about how the proof might
; go, one is led quickly to the decision to prove an appropriate fact about the
; mesh of (make-partition-rec a delta n), namely, mesh-make-partition-rec
; below.  When that theorem is submitted to ACL2, the following term is printed
; in a goal that does not simplify further:

#|
                    (CAR (MAKE-PARTITION-REC (+ A DELTA)
                                             DELTA (+ -1 N)))
|#

; But the first element of the result returned by make-partition-rec is clearly
; its first argument, a fact brought to the prover's attention with the first
; lemma below.

(encapsulate
 ()

 (local
  (defthm car-make-partition-rec
    (equal (car (make-partition-rec a delta n))
           a)))

 (defthm mesh-make-partition-rec
   (implies (and (rationalp delta)
                 (<= 0 delta)
                 (integerp n)
                 (< 0 n))
            (equal (mesh (make-partition-rec a delta n))
                   delta))
   :hints (("Goal" :expand ((make-partition-rec a delta 1))))))

; We need to disable the nonrecursive function symbol mesh in order for the
; rewrite rule mesh-make-partition-rec to apply when we are trying to prove
; mesh-make-partition.
(in-theory (disable mesh))

; The theorem mesh-make-partition now goes through automatically if we include
; an appropriate arithmetic book, e.g.,
; (include-book "/projects/acl2/v2-5/books/arithmetic/top").  However, below we
; show how one can get the theorem proved without such help.

; An attempt to prove mesh-make-partition causes an induction to be tried,
; which is perhaps surprising given the rewrite rule mesh-make-partition-rec,
; and is followed by failure to prove the thoerem.  Why is that?  The problem
; is that the prover cannot show that the particular delta fed to
; make-partition-rec by make-partition satisfies the nonnegativity hypothesis
; of rule mesh-make-partition-rec.  If it is not clear that this is indeed the
; issue, then see file mesh-make-partition_info.txt for an annotated transcript
; of a proof-builder session that leads us to this fact.

; Lemma hack2 below states that the delta in question is indeed nonnegative.
; We have to work a bit in order to prove hack2.  It seems clear if the
; distributivity law is applied in reverse, so our approach is to obtain hack2
; from a lemma hack1 that is the result of applying factoring to hack2 (and
; then simplifying and generalizing a bit).  An attempt to prove hack1, in
; turn, leads the prover to get stuck attempting to prove
; (<= 0 (* X (+ (- A) B)))
; under relevant hypotheses, which leads us to prove the lemma
; product-nonnegative below.

(local
 (encapsulate
  ()

  (local
   (defthm product-nonnegative
     (implies (and (rationalp x) (rationalp y))
              ;; If we use equal instead of iff, ACL2's linear arithmetic
              ;; doesn't happen to work.
              (iff (< (* x y) 0);; (not (<= 0 (* x y)))
                   (or (and (< 0 x) (< y 0))
                       (and (< x 0) (< 0 y)))))))

  (local
   (defthm hack1
     (implies (and (rationalp x) (rationalp a) (rationalp b)
                   (<= 0 x)
                   (<= a b))
              (<= 0 (* x (- b a))))
     :hints (("Goal" :in-theory (disable distributivity)))
     :rule-classes nil))

  (defthm hack2
    (implies (and (rationalp n)
                  (< 0 n)
                  (rationalp a)
                  (rationalp b)
                  (<= a b))
             (<= 0 (+ (* b (/ n)) (* (/ n) (- a)))))
    :hints (("Goal" :use ((:instance hack1 (x (/ n)))))))))

(defthm mesh-make-partition
  (implies (and (rationalp a)
                (rationalp b)
                (< a b)
                (integerp n)
                (< 0 n))
           (equal (mesh (make-partition a b n))
                  (/ (- b a) n))))
