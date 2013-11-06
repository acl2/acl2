(in-package "ACL2")

; Solution to Exercise 6.7.

(include-book "partition-defuns")

; The first attempt at mesh-append produces this failed subgoal.
#|
(IMPLIES (AND (PARTITIONP P1)
              (CONSP P2)
              (RATIONALP (CAR P2))
              (NOT (CDR P2))
              (EQUAL (CAR (LAST P1)) (CAR P2))
              (< 0 (MAXLIST (DELTAS P1))))
         (EQUAL (MAXLIST (DELTAS (APPEND P1 NIL)))
                (MAXLIST (DELTAS P1))))
|#
; The conclusion of this subgoal suggests the following lemma.

(defthm partitionp-append-nil
  (implies (partitionp p)
           (equal (append p nil) p)))

; Mesh-append still fails, this time at the following goal.
#|
(IMPLIES (AND (PARTITIONP P1)
              (CONSP P2)
              (RATIONALP (CAR P2))
              (NOT (CDR P2))
              (EQUAL (CAR (LAST P1)) (CAR P2))
              (<= (MAXLIST (DELTAS P1)) 0))
         (EQUAL (MAXLIST (DELTAS P1)) 0))
|#
; The conclusion suggests the following rewrite rule.

(defthm equal-maxilst-deltas
  (implies (partitionp p)
           (equal (equal (maxlist (deltas p)) 0)
                  (equal (cdr p) nil))))

; The proof of mesh-append gets farther this time, where the final
; goal has the following conclusion:
#|
(EQUAL (MAXLIST (DELTAS (APPEND P1 (CDR P2))))
       (MAXLIST (DELTAS P1)))
|#
; This suggests a lemma about how deltas distributes over append.

(defthm deltas-append
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car p2)))
           (equal (deltas (append p1 (cdr p2)))
                  (append (deltas p1) (deltas p2)))))

; This time the conclusion is as follows.
#|
(EQUAL (MAXLIST (APPEND (DELTAS P1)
                        (CONS (+ (- (CAR P2)) (CADR P2))
                              (DELTAS (CDR P2)))))
       (MAXLIST (DELTAS P1)))
|#
; The left-hand side suggests the following rule for how maxlist
; distributes over append.

(defthm maxlist-append
  (equal (maxlist (append x y))
         (max (maxlist x) (maxlist y))))

; The main theorem of this book now follows.  We did not create any
; lemma sub-books because all the major lemmas were proved
; automatically.

(defthm mesh-append
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car p2)))
           (equal (mesh (append p1 (cdr p2)))
                  (max (mesh p1) (mesh p2))))
  :hints (("Goal" :do-not-induct t
           :do-not '(eliminate-destructors))))
