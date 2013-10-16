(in-package "ACL2")

; Solution to Exercise 6.5.

(include-book "partition-defuns")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (local (include-book "partitionp-make-partition-rec"))
 (defthm partitionp-make-partition-rec
   (implies (and (not (zp n))
                 (rationalp delta)
                 (< 0 delta)
                 (rationalp a))
            (partitionp (make-partition-rec a delta n)))))

; A proof attempt now fails, though the lemma above was intended to
; allow its proof to succeed by applying the preceding lemma.  What
; went wrong?  Here is the last goal printed out before a fruitless
; induction attempt.
#|
(IMPLIES (AND (RATIONALP A)
              (RATIONALP B)
              (< A B)
              (INTEGERP N)
              (< 0 N))
         (PARTITIONP (MAKE-PARTITION-REC A (+ (* B (/ N)) (* (/ N) (- A)))
                                         N)))
|#
; The only explanation for the failure is that the prover is not
; recognizing that the second argument to make-partition-rec is a
; positive rational number.  The easy solution is to use include-book
; on either "arithmetic/top-with-meta" or "arithmetic/top", from the
; books/ subdirectory of the ACL2 distribution.  Alternatively, one
; can notice that the rewrite rule DISTRIBUTIVITY was used in the
; failed proof attempt, and see what happens if that rule is
; disabled.  This time the last goal before induction is as follows.
#|
(IMPLIES (AND (RATIONALP A)
              (RATIONALP B)
              (< A B)
              (INTEGERP N)
              (< 0 N))
         (PARTITIONP (MAKE-PARTITION-REC A (* (/ N) (+ (- A) B))
                                         N)))
|#
; This formula suggests the following two rewrite rules, so that ACL2
; can reason that the product above is positive.

(defthm <-times
  (implies (and (rationalp x) (rationalp y))
           (iff (< 0 (* x y))
                (or (and (< 0 x) (< 0 y))
                    (and (< x 0) (< y 0))))))

(defthm <-0-difference
  (iff (< 0 (+ (- a) b))
       (< a b)))

(defthm partitionp-make-partition
  (implies (and (rationalp a)
                (rationalp b)
                (< a b)
                (not (zp n)))
           (partitionp (make-partition a b n)))
  ;; Unfortunately, with just the lemmas above the proof fails unless
  ;; we disable distributivity.
  :hints (("Goal" :in-theory (disable distributivity))))
