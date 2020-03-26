(in-package "ACL2")

(include-book "misc/defpun" :dir :system)
(include-book "arithmetic/top" :dir :system)

(include-book "nested-intervals")

(encapsulate
 ( ((seq *) => * :formals (n) :guard (posp n))
   ((a) => *)
   ((b) => *)
   )
 (local (defun seq (n)
          (declare (xargs :guard (posp n))
                   (ignore n))
          0))
 (local (defun a () 0))
 (local (defun b () 1))

 (defthm seq-is-real
   (realp (seq n))
   :rule-classes (:rewrite :type-prescription))

 (defthm a-b-is-open-interval
   (and (realp (a))
        (realp (b))
        (< (a) (b))))
 )


(defun in-range (x A B)
  (and (< A x)
       (< x B)))

(defpun next-index-in-range (n A B)
  (if (in-range (seq n) A B)
      n
    (next-index-in-range (1+ n) A B)))

(defun-sk exists-next-index-in-range (n A B)
  (exists m
          (and (posp m)
               (<= n m)
               (in-range (seq m) A B))))

(local
 (defun next-index-in-range-valid-lemma-induction-hint (n m)
   (declare (xargs :measure (nfix (1+  (- m n)))))
   (if (and (posp n) (posp m))
       (if (<= n m)
           (next-index-in-range-valid-lemma-induction-hint (1+ n) m)
         (- n m))
     nil)))

(local
 (defthm next-index-in-range-valid-lemma
   (implies (and (posp n)
                 (posp m)
                 (<= n m)
                 (in-range (seq m) A B))
            (and (posp (next-index-in-range n A B))
                 (<= n (next-index-in-range n A B))
                 (<= (next-index-in-range n A B) m)
                 (in-range (seq (next-index-in-range n A B)) A B)))
   :hints (("Goal"
            :induct (next-index-in-range-valid-lemma-induction-hint n m)))
   ))

(defthm next-index-in-range-valid
  (implies (and (posp n)
                (exists-next-index-in-range n A B))
           (and (posp (next-index-in-range n A B))
                (<= n (next-index-in-range n A B))
                (in-range (seq (next-index-in-range n A B)) A B))))

(defun next-two-indexes-in-range (n A B)
  (cons (next-index-in-range n A B)
        (next-index-in-range (1+ (next-index-in-range n A B))
                             (seq (next-index-in-range n A B))
                             B)))

(defun exist-next-two-indexes-in-range (n A B)
  (and (exists-next-index-in-range n A B)
       (exists-next-index-in-range (1+ (next-index-in-range n A B))
                                   (seq (next-index-in-range n A B))
                                   B)))

(defthm next-two-indexes-in-range-valid
  (implies (and (posp n)
                (exist-next-two-indexes-in-range n A B))
           (let* ((m1-m2 (next-two-indexes-in-range n A B))
                  (m1 (car m1-m2))
                  (m2 (cdr m1-m2)))
             (and (posp m1)
                  (<= n m1)
                  (in-range (seq m1) A B)
                  (posp m2)
                  (< m1 m2)
                  (in-range (seq m2) A B)
                  (< (seq m1) (seq m2)))))
  :hints (("Goal"
           :use ((:instance next-index-in-range-valid
                            (n n)
                            (A A)
                            (B B))
                 (:instance next-index-in-range-valid
                            (n (1+ (next-index-in-range n A B)) )
                            (A (seq (next-index-in-range n A B)))
                            (B B)))
           :in-theory (disable next-index-in-range-valid))))

(defun counter-example (n A B)
  (if (zp n)
      (/ (+ A B) 2)
    (if (in-range (seq n) A B)
        (counter-example (1- n) A (seq n))
      (counter-example (1- n) A B))))

(defthm counter-example-in-range
  (implies (and (realp A)
                (realp B)
                (< A B))
           (and (realp (counter-example n A B))
                (< A (counter-example n A B))
                (< (counter-example n A B) B))))

(local
 (defthm must-be-1
   (implies (and (posp n)
                 (not (posp (+ -1 n))))
            (equal n 1))
   :rule-classes nil))

(local
 (defthm counter-example-not-in-previous-sequence-lemma-1
   (implies (and (not (zp n))
                 (not (in-range (seq n) a b))
                 (not (posp (+ -1 n)))
                 (realp a)
                 (realp b)
                 (< a b)
                 (posp n)
                 (posp m)
                 (<= m n))
            (not (equal (seq m)
                        (counter-example n a b))))
   :hints (("Goal"
            :use ((:instance must-be-1))))
   :rule-classes (:built-in-clause)
   ))

(local
 (defthm counter-example-not-in-previous-sequence-lemma-2
   (implies (and (realp A)
                 (realp B)
                 (< A B))
            (not (equal B
                        (counter-example n A B))))
   :hints (("Goal"
            :use ((:instance counter-example-in-range))))
   ))


(local
 (defthm counter-example-not-in-previous-sequence-lemma-3
   (implies (and (not (zp n))
                 (in-range (seq n) a b)
                 (not (posp (+ -1 n)))
                 (realp a)
                 (realp b)
                 (< a b)
                 (posp n)
                 (posp m)
                 (<= m n))
            (not (equal (seq m)
                        (counter-example n a b))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance must-be-1)))
           ("Goal'"
            :expand ((COUNTER-EXAMPLE 1 A B)))
           )
   :rule-classes (:built-in-clause)
   ))

(defthm counter-example-not-in-previous-sequence
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (posp m)
                (<= m n))
           (not (equal (seq m)
                       (counter-example n A B)))))

(defthm no-next-index-in-range-sequence-not-in-range
  (implies (and (posp n)
                (posp m)
                (<= n m)
                (not (exists-next-index-in-range n A B)))
           (not (in-range (seq m) A B))))

(defthm no-next-index-in-range-counter-example-not-in-following-sequence
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (posp m)
                (<= n m)
                (not (exists-next-index-in-range n A B)))
           (not (equal (seq m)
                       (counter-example n A B))))
  :hints (("Goal"
           :use ((:instance no-next-index-in-range-sequence-not-in-range)
                 (:instance counter-example-in-range)))))

(defthm no-next-index-in-range-counter-example-not-in-sequence
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (posp m)
                (not (exists-next-index-in-range n A B)))
           (not (equal (seq m)
                       (counter-example n A B))))
  :hints (("Goal"
           :use ((:instance counter-example-not-in-previous-sequence)
                 (:instance no-next-index-in-range-counter-example-not-in-following-sequence)))))


(defun-sk exists-in-sequence (x)
  (exists i
          (and (posp i)
               (equal (seq i) x))))

(defthm no-next-index-in-range-counter-example-not-in-sequence-sk
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (not (exists-next-index-in-range n A B)))
           (not (exists-in-sequence (counter-example n A B)))))

(defun-sk exists-in-interval-but-not-in-sequence (A B)
  (exists x
          (and (realp x)
               (< A x)
               (< x B)
               (not (exists-in-sequence x)))))

;; MILESTONE: If ever we find an index so that the remainder of the sequence is out
;; of the interval, then the theorem is trivially(!) true.

(defthm no-next-index-in-range-exists-in-interval-but-not-in-sequence
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (not (exists-next-index-in-range n A B)))
           (exists-in-interval-but-not-in-sequence A B))
  :hints (("Goal"
           :use ((:instance exists-in-interval-but-not-in-sequence-suff
                            (x (counter-example n A B)))))))

;; MILESTONE: We generalize the previous, so that if we can't find two indexes in the
;; remainder of the sequence that are inside the interval, then the theorem is true.

(local
 (defthm exists-in-interval-but-not-in-sequence-monotonic-1
   (implies (and (realp A)
                 (realp A1)
                 (realp B)
                 (< A A1)
                 (< A1 B)
                 (exists-in-interval-but-not-in-sequence A1 B))
            (exists-in-interval-but-not-in-sequence A B))
   :hints (("Goal"
            :use ((:instance exists-in-interval-but-not-in-sequence-suff
                             (x (exists-in-interval-but-not-in-sequence-witness A1 B))))))
   ))

(local
 (defthm exists-in-interval-but-not-in-sequence-monotonic-2
   (implies (and (realp A)
                 (realp B1)
                 (realp B)
                 (< A B1)
                 (< B1 B)
                 (exists-in-interval-but-not-in-sequence A B1))
            (exists-in-interval-but-not-in-sequence A B))
   :hints (("Goal"
            :use ((:instance exists-in-interval-but-not-in-sequence-suff
                             (x (exists-in-interval-but-not-in-sequence-witness A B1))))))
   ))

(defthm exists-in-interval-but-not-in-sequence-monotonic
  (implies (and (realp A)
                (realp A1)
                (realp B1)
                (realp B)
                (<= A A1)
                (< A1 B1)
                (<= B1 B)
                (exists-in-interval-but-not-in-sequence A1 B1))
           (exists-in-interval-but-not-in-sequence A B))
  :hints (("Goal"
           :use ((:instance exists-in-interval-but-not-in-sequence-monotonic-1
                            (A A)
                            (A1 A1)
                            (B B1))
                 (:instance exists-in-interval-but-not-in-sequence-monotonic-2
                            (A A)
                            (B1 B1)
                            (B B)))
           :in-theory (disable exists-in-interval-but-not-in-sequence
                               exists-in-interval-but-not-in-sequence-monotonic-1
                               exists-in-interval-but-not-in-sequence-monotonic-2))))

(local
 (defthm no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence-lemma-1
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (exists-next-index-in-range n A B)
                (not (exists-next-index-in-range (1+ (next-index-in-range n A B))
                                                 (seq (next-index-in-range n A B))
                                                 B)))
           (exists-in-interval-but-not-in-sequence (seq (next-index-in-range n A B)) B))
  :hints (("Goal"
           :use ((:instance no-next-index-in-range-exists-in-interval-but-not-in-sequence
                            (n (1+ (next-index-in-range n A B)))
                            (A (seq (next-index-in-range n A B)))
                            (B B))
                 (:instance next-index-in-range-valid))
           :in-theory (disable exists-in-interval-but-not-in-sequence
                               exists-next-index-in-range
                               next-index-in-range-valid)
           ))))

(local
 (defthm no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence-lemma
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (exists-next-index-in-range n A B)
                (not (exists-next-index-in-range (1+ (next-index-in-range n A B))
                                                 (seq (next-index-in-range n A B))
                                                 B)))
           (exists-in-interval-but-not-in-sequence A B))
  :hints (("Goal"
           :use ((:instance no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence-lemma-1)
                 (:instance exists-in-interval-but-not-in-sequence-monotonic-1
                            (A1 (seq (next-index-in-range n A B))))
                 (:instance next-index-in-range-valid))
           :in-theory (disable exists-in-interval-but-not-in-sequence
                               exists-next-index-in-range
                               no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence-lemma-1
                               exists-in-interval-but-not-in-sequence-monotonic-1
                               next-index-in-range-valid)))))

(defthm no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence
  (implies (and (realp A)
                (realp B)
                (< A B)
                (posp n)
                (not (exist-next-two-indexes-in-range n A B)))
           (exists-in-interval-but-not-in-sequence A B))
  :hints (("Goal"
           :use ((:instance no-next-index-in-range-exists-in-interval-but-not-in-sequence (n n))
                 (:instance no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence-lemma))
           :in-theory '(exist-next-two-indexes-in-range)
           )))


;;-----------------------
;;
;; Next up: We can assume that we can always get a next interval in the sequence,
;; so we should be able to get an infinite chain of closed intervals so that the
;; intersection of the intervals is in the original open interval (A,B) but not
;; in the sequence.

(defun extend-seq (n def)
  (if (posp n)
      (seq n)
    def))

(defun indexes-to-interval (indexes)
  (cons (extend-seq (car indexes) (a))
        (extend-seq (cdr indexes) (b))))

(defun cantor-sequence-indexes (n)
  (if (zp n)
      (cons 0 0)
    (let* ((a-b (cantor-sequence-indexes (1- n)))
           (next-n (1+ (max (car a-b) (cdr a-b)))))
      (if (consp a-b)
          (let* ((interval-a-b (indexes-to-interval a-b))
                 (next-a (car interval-a-b))
                 (next-b (cdr interval-a-b)))
            (if (exist-next-two-indexes-in-range next-n next-a next-b)
                (next-two-indexes-in-range next-n next-a next-b)
              nil))
        nil))))

(local
 (defthm cantor-sequence-indexes-is-pair-of-natps-lemma
   (implies (and (not (zp n))
                 (consp (cantor-sequence-indexes (+ -1 n)))
                 (natp (car (cantor-sequence-indexes (+ -1 n))))
                 (natp (cdr (cantor-sequence-indexes (+ -1 n))))
                 (consp (cantor-sequence-indexes n)))
            (and (natp (car (cantor-sequence-indexes n)))
                 (natp (cdr (cantor-sequence-indexes n)))))
   :hints (("Goal"
            :use ((:instance next-two-indexes-in-range-valid
                             (n (1+ (max (car (cantor-sequence-indexes (1- n))) (cdr (cantor-sequence-indexes (1- n))))))
                             (A (car (indexes-to-interval (cantor-sequence-indexes (1- n)))))
                             (B (cdr (indexes-to-interval (cantor-sequence-indexes (1- n)))))))
            :in-theory (disable next-two-indexes-in-range-valid
                                exist-next-two-indexes-in-range
                                indexes-to-interval
                                next-two-indexes-in-range)))))


(local
 (defthm cantor-sequence-indexes-is-pair-of-natps-lemma-useful
   (implies
    (and (not (zp n))
         (consp (cantor-sequence-indexes (+ -1 n)))
         (exist-next-two-indexes-in-range
              (+ 1
                 (max (car (cantor-sequence-indexes (+ -1 n)))
                      (cdr (cantor-sequence-indexes (+ -1 n)))))
              (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n))))
              (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
         (implies (not (null (cantor-sequence-indexes (+ -1 n))))
                  (and (natp (car (cantor-sequence-indexes (+ -1 n))))
                       (natp (cdr (cantor-sequence-indexes (+ -1 n)))))))
    (implies (not (null (cantor-sequence-indexes n)))
             (and (natp (car (cantor-sequence-indexes n)))
                  (natp (cdr (cantor-sequence-indexes n))))))
   :hints (("Goal"
            :use ((:instance cantor-sequence-indexes-is-pair-of-natps-lemma))
            :in-theory (disable cantor-sequence-indexes
                                indexes-to-interval
                                exist-next-two-indexes-in-range
                                )))
   :rule-classes (:built-in-clause)))

(defthm cantor-sequence-indexes-is-pair-of-natps
  (implies (not (null (cantor-sequence-indexes n)))
           (and (natp (car (cantor-sequence-indexes n)))
                (natp (cdr (cantor-sequence-indexes n)))))
  :hints (("Goal"
           :in-theory (disable exist-next-two-indexes-in-range
                               next-two-indexes-in-range))
          ("Subgoal *1/2"
           :by (:instance cantor-sequence-indexes-is-pair-of-natps-lemma-useful))
          )
)

(defthm cantor-sequence-indexes-is-pair-of-natps-type-1
  (implies (cantor-sequence-indexes n)
           (natp (car (cantor-sequence-indexes n))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps))))
  :rule-classes (:type-prescription))

(defthm cantor-sequence-indexes-is-pair-of-natps-type-2
  (implies (cantor-sequence-indexes n)
           (natp (cdr (cantor-sequence-indexes n))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps))))
  :rule-classes (:type-prescription))

(defthm 1+-max-of-nats-is-posp
  (implies (and (natp x)
                (natp y))
           (posp (+ 1 (max x y))))
  :rule-classes (:type-prescription :rewrite)
  )

(defthm cantor-sequence-indexes-is-interval
  (implies (cantor-sequence-indexes n)
           (< (car (indexes-to-interval (cantor-sequence-indexes n)))
              (cdr (indexes-to-interval (cantor-sequence-indexes n)))))
  :hints (("Goal"
           :in-theory (disable exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ("Subgoal *1/2"
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          )
  )

(defthm cantor-sequence-indexes-car-in-range
  (implies (cantor-sequence-indexes n)
           (<= (a)
               (car (indexes-to-interval (cantor-sequence-indexes n)))))
  :hints (("Goal"
           :in-theory (disable exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ("Subgoal *1/4"
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ("Subgoal *1/3"
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ))

(defthm cantor-sequence-indexes-cdr-in-range
  (implies (cantor-sequence-indexes n)
           (<= (cdr (indexes-to-interval (cantor-sequence-indexes n)))
               (b)))
  :hints (("Goal"
           :in-theory (disable exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ("Subgoal *1/4"
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ("Subgoal *1/3"
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          ))

(defthm cantor-sequence-indexes-is-nested-interval-left
  (implies (and (posp n)
                (cantor-sequence-indexes n))
           (< (car (indexes-to-interval (cantor-sequence-indexes (1- n))))
              (car (indexes-to-interval (cantor-sequence-indexes n)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          )
  )

(defthm cantor-sequence-indexes-is-nested-interval-right
  (implies (and (posp n)
                (cantor-sequence-indexes n))
           (< (cdr (indexes-to-interval (cantor-sequence-indexes n)))
              (cdr (indexes-to-interval (cantor-sequence-indexes (1- n))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1
                                  (max (car (cantor-sequence-indexes (+ -1 n)))
                                       (cdr (cantor-sequence-indexes (+ -1 n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           :in-theory (disable max
                               next-two-indexes-in-range-valid
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               next-two-indexes-in-range))
          )
  )

(local
 (defun cantor-sequence-indexes-is-nested-interval-strong-induction-hint (m n)
   (if (zp n)
       nil
     (if (equal m (1- n))
         t
       (cantor-sequence-indexes-is-nested-interval-strong-induction-hint m (1- n))))))

(local
 (defthm null-cantor-sequence-indexes-monotonic
   (implies (and (posp n)
                 (cantor-sequence-indexes n))
            (cantor-sequence-indexes (+ -1 n)))))


(defthm cantor-sequence-indexes-is-nested-interval-left-strong
  (implies (and (posp n)
                (natp m)
                (< m n)
                (cantor-sequence-indexes n))
           (< (car (indexes-to-interval (cantor-sequence-indexes m)))
              (car (indexes-to-interval (cantor-sequence-indexes n)))))
  :hints (("Goal"
           :induct (cantor-sequence-indexes-is-nested-interval-strong-induction-hint m n)
           :in-theory (disable cantor-sequence-indexes indexes-to-interval))
          ("Subgoal *1/3"
           :use ((:instance cantor-sequence-indexes-is-nested-interval-left))
           :in-theory (disable cantor-sequence-indexes indexes-to-interval cantor-sequence-indexes-is-nested-interval-left))
          ))

(defthm cantor-sequence-indexes-is-nested-interval-right-strong
  (implies (and (posp n)
                (natp m)
                (< m n)
                (cantor-sequence-indexes n))
           (< (cdr (indexes-to-interval (cantor-sequence-indexes n)))
              (cdr (indexes-to-interval (cantor-sequence-indexes m)))))
  :hints (("Goal"
           :induct (cantor-sequence-indexes-is-nested-interval-strong-induction-hint m n)
           :in-theory (disable cantor-sequence-indexes indexes-to-interval))
          ("Subgoal *1/3"
           :use ((:instance cantor-sequence-indexes-is-nested-interval-right))
           :in-theory (disable cantor-sequence-indexes indexes-to-interval cantor-sequence-indexes-is-nested-interval-right))
          ))

(local
 (defthm indexes-to-interval-zero
   (equal (indexes-to-interval (cons 0 0))
          (cons (a) (b)))
   :hints (("Goal"
            :in-theory (disable (indexes-to-interval))))
   ))

(defthm cantor-sequence-indexes-car-in-range-strong
  (implies (and (posp n)
                (cantor-sequence-indexes n))
           (< (a)
              (car (indexes-to-interval (cantor-sequence-indexes n)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cantor-sequence-indexes-is-nested-interval-left-strong
                            (m 0)
                            (n n))
                 (:instance cantor-sequence-indexes-car-in-range))
           :in-theory (disable cantor-sequence-indexes-is-nested-interval-left-strong
                               cantor-sequence-indexes-car-in-range))))

(defthm cantor-sequence-indexes-cdr-in-range-strong
  (implies (and (posp n)
                (cantor-sequence-indexes n))
           (< (cdr (indexes-to-interval (cantor-sequence-indexes n)))
              (b)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cantor-sequence-indexes-is-nested-interval-right-strong
                            (m 0)
                            (n n))
                 (:instance cantor-sequence-indexes-cdr-in-range))
           :in-theory (disable cantor-sequence-indexes-is-nested-interval-right-strong
                               cantor-sequence-indexes-cdr-in-range))))


(defun cantor-sequence-indexes-critical-pair (n)
  (if (zp n)
      nil
    (let* ((a-b (cantor-sequence-indexes (1- n)))
           (next-n (1+ (max (car a-b) (cdr a-b)))))
      (if (consp a-b)
          (let* ((interval-a-b (indexes-to-interval a-b))
                 (next-a (car interval-a-b))
                 (next-b (cdr interval-a-b)))
            (if (exist-next-two-indexes-in-range next-n next-a next-b)
                nil
              (list next-n next-a next-b)))
        (cantor-sequence-indexes-critical-pair (1- n))))))

(defthm critical-pair-valid-if-null-cantor-sequence-indexes-lemma-1
  (implies (null (cantor-sequence-indexes n))
           (let* ((critical-pair (cantor-sequence-indexes-critical-pair n)))
             (and (consp critical-pair)
                  (not (exist-next-two-indexes-in-range (first critical-pair)
                                                        (second critical-pair)
                                                        (third critical-pair)))))))

(defthm critical-pair-valid-if-null-cantor-sequence-indexes-lemma-2
  (implies (null (cantor-sequence-indexes n))
           (and (posp (first (cantor-sequence-indexes-critical-pair n)))
                (realp (second (cantor-sequence-indexes-critical-pair n)))
                (realp (third (cantor-sequence-indexes-critical-pair n))))))


(defthm critical-pair-valid-if-null-cantor-sequence-indexes-lemma-3
  (implies (null (cantor-sequence-indexes n))
           (<= (a) (second (cantor-sequence-indexes-critical-pair n))))
  :hints (("Goal"
           :in-theory (disable next-two-indexes-in-range))
          ("Subgoal *1/5"
           :use ((:instance cantor-sequence-indexes-car-in-range (n (1- n))))
           :in-theory (disable next-two-indexes-in-range cantor-sequence-indexes-car-in-range))
          ("Subgoal *1/4"
           :use ((:instance cantor-sequence-indexes-car-in-range (n (1- n))))
           :in-theory (disable next-two-indexes-in-range cantor-sequence-indexes-car-in-range))

          ))

(defthm critical-pair-valid-if-null-cantor-sequence-indexes-lemma-4
  (implies (null (cantor-sequence-indexes n))
           (< (second (cantor-sequence-indexes-critical-pair n))
              (third (cantor-sequence-indexes-critical-pair n))))
  :hints (("Goal"
           :in-theory (disable next-two-indexes-in-range))
          ("Subgoal *1/5"
           :use ((:instance cantor-sequence-indexes-is-interval (n (1- n))))
           :in-theory (disable next-two-indexes-in-range cantor-sequence-indexes-is-interval))
          ("Subgoal *1/4"
           :use ((:instance cantor-sequence-indexes-is-interval (n (1- n))))
           :in-theory (disable next-two-indexes-in-range cantor-sequence-indexes-is-interval))
          )
  )

(defthm critical-pair-valid-if-null-cantor-sequence-indexes-lemma-5
  (implies (null (cantor-sequence-indexes n))
           (<= (third (cantor-sequence-indexes-critical-pair n))
               (b)))
  :hints (("Goal"
           :in-theory (disable next-two-indexes-in-range))
          ("Subgoal *1/5"
           :use ((:instance cantor-sequence-indexes-cdr-in-range (n (1- n))))
           :in-theory (disable next-two-indexes-in-range cantor-sequence-indexes-cdr-in-range))
          ("Subgoal *1/4"
           :use ((:instance cantor-sequence-indexes-cdr-in-range (n (1- n))))
           :in-theory (disable next-two-indexes-in-range cantor-sequence-indexes-cdr-in-range))

          ))

(defthm critical-pair-valid-if-null-cantor-sequence-indexes-lemma
  (implies (null (cantor-sequence-indexes n))
           (exists-in-interval-but-not-in-sequence (a) (b)))
  :hints (("Goal"
           :use ((:instance no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence
                            (n (first (cantor-sequence-indexes-critical-pair n)))
                            (A (second (cantor-sequence-indexes-critical-pair n)))
                            (B (third (cantor-sequence-indexes-critical-pair n))))
                 (:instance critical-pair-valid-if-null-cantor-sequence-indexes-lemma-1)
                 (:instance critical-pair-valid-if-null-cantor-sequence-indexes-lemma-2)
                 (:instance critical-pair-valid-if-null-cantor-sequence-indexes-lemma-3)
                 (:instance critical-pair-valid-if-null-cantor-sequence-indexes-lemma-4)
                 (:instance critical-pair-valid-if-null-cantor-sequence-indexes-lemma-5)
                 (:instance exists-in-interval-but-not-in-sequence-monotonic
                            (A (A))
                            (A1 (second (cantor-sequence-indexes-critical-pair n)))
                            (B1 (third (cantor-sequence-indexes-critical-pair n)))
                            (B (B)))
                 )
           :in-theory (disable no-next-two-indexes-in-range-exists-in-interval-but-not-in-sequence
                               critical-pair-valid-if-null-cantor-sequence-indexes-lemma-1
                               critical-pair-valid-if-null-cantor-sequence-indexes-lemma-2
                               critical-pair-valid-if-null-cantor-sequence-indexes-lemma-3
                               critical-pair-valid-if-null-cantor-sequence-indexes-lemma-4
                               critical-pair-valid-if-null-cantor-sequence-indexes-lemma-5
                               exists-in-interval-but-not-in-sequence-monotonic
                               cantor-sequence-indexes
                               cantor-sequence-indexes-critical-pair
                               exists-in-interval-but-not-in-sequence))))

(defun-sk cantor-sequence-indexes-is-sometimes-null ()
  (exists (n)
          (null (cantor-sequence-indexes n))))

;; MAJOR MILESTONE:
;; Now if the cantor sequence of index ever fails, then we have that there's a point in the
;; interval that is not in the sequence

(defthm critical-pair-valid-if-null-cantor-sequence-indexes
  (implies (cantor-sequence-indexes-is-sometimes-null)
           (exists-in-interval-but-not-in-sequence (a) (b))))

;; MILESTONE:
;; Now if the cantor sequence of index never fails, then we know that cantor-sequence-indexes
;; is not null for any n.  This will come in handy!

(defthm cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (cantor-sequence-indexes n))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-sometimes-null-suff))
           :in-theory (disable cantor-sequence-indexes cantor-sequence-indexes-is-sometimes-null-suff)))
  )


(defun cantor-sequence-indexes-simplified (n)
  (if (zp n)
      (cons 0 0)
    (let* ((a-b (cantor-sequence-indexes-simplified (1- n)))
           (next-n (1+ (max (car a-b) (cdr a-b))))
           (interval-a-b (indexes-to-interval a-b))
           (next-a (car interval-a-b))
           (next-b (cdr interval-a-b)))
        (next-two-indexes-in-range next-n next-a next-b))))

(defthm simplify-cantor-sequence
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (equal (cantor-sequence-indexes n)
                  (cantor-sequence-indexes-simplified n)))
  :hints (("Subgoal *1/3"
           :use ((:instance cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null))
           :in-theory (disable cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null))
          )
  )

(defun simplified-cantor-interval (n)
  (if (cantor-sequence-indexes-is-sometimes-null)
      (cons 0 0)
    (indexes-to-interval (cantor-sequence-indexes-simplified n))))

(defthm simplified-cantor-interval-satisfies-nested-interval-reals
  (and (consp (simplified-cantor-interval n))
       (realp (car (simplified-cantor-interval n)))
       (realp (cdr (simplified-cantor-interval n))))
  :rule-classes (:rewrite :type-prescription))

(defthm simplified-cantor-interval-satisfies-nested-intervals-are-intervals
  (implies (posp n)
           (<= (car (simplified-cantor-interval n))
               (cdr (simplified-cantor-interval n))))
  :hints (("Goal"
           :cases ((cantor-sequence-indexes-is-sometimes-null)))
          ("Subgoal 2"
           :use ((:instance cantor-sequence-indexes-is-interval)
                 (:instance a-b-is-open-interval))
           :in-theory (disable cantor-sequence-indexes-is-interval
                               a-b-is-open-interval))
          )
  :rule-classes (:linear :rewrite))

(defthm simplified-cantor-interval-satisfies-nested-intervals-are-nested
   (implies (and (posp m)
                 (posp n)
                 (< m n))
            (and (<= (car (simplified-cantor-interval m)) (car (simplified-cantor-interval n)))
                 (>= (cdr (simplified-cantor-interval m)) (cdr (simplified-cantor-interval n)))))
  :hints (("Goal"
           :cases ((cantor-sequence-indexes-is-sometimes-null)))
          ("Subgoal 2"
           :use ((:instance cantor-sequence-indexes-is-nested-interval-left-strong)
                 (:instance cantor-sequence-indexes-is-nested-interval-right-strong))
           :in-theory (disable cantor-sequence-indexes-is-nested-interval-left-strong
                               cantor-sequence-indexes-is-nested-interval-right-strong))
          )
   :rule-classes (:linear :rewrite))

(defun intersection-point-nonstd ()
  (standard-part (car (simplified-cantor-interval (i-large-integer)))))

(defthm intersection-point-nonstd-in-intersection
  (and (realp (intersection-point-nonstd))
       (implies (posp n)
                (and (<= (car (simplified-cantor-interval n))
                         (intersection-point-nonstd))
                     (<= (intersection-point-nonstd)
                         (cdr (simplified-cantor-interval n))))))
  :hints (("Goal"
           :use ((:functional-instance standard-part-car-interval-in-intersection
                                       (nested-interval simplified-cantor-interval)
                                       (standard-part-car-interval-large intersection-point-nonstd))))
           ("Subgoal 2"
            :by (:instance simplified-cantor-interval-satisfies-nested-intervals-are-nested))
           ("Subgoal 1"
            :by (:instance simplified-cantor-interval-satisfies-nested-intervals-are-intervals))))

(defthm standard-intersection-point-nonstd
  (standardp (intersection-point-nonstd))
  :hints (("Goal"
           :by (:functional-instance standard-part-car-interval-large-is-standard
                                     (nested-interval simplified-cantor-interval)
                                     (standard-part-car-interval-large intersection-point-nonstd)))))

(in-theory (disable intersection-point-nonstd (intersection-point-nonstd)))

(defun-std intersection-point ()
  (intersection-point-nonstd))

(defthm intersection-point-is-the-same
  (equal (intersection-point-nonstd)
         (intersection-point))
  :hints (("Goal"
           :use ((:functional-instance standard-part-car-interval-large-is-same
                                       (nested-interval simplified-cantor-interval)
                                       (standard-part-car-interval-large-classical intersection-point)
                                       (standard-part-car-interval-large intersection-point-nonstd))))))

(defthm intersection-point-in-intersection-simplified-lemma
  (and (realp (intersection-point))
       (implies (posp n)
                (and (<= (car (simplified-cantor-interval n))
                         (intersection-point))
                     (<= (intersection-point)
                         (cdr (simplified-cantor-interval n))))))
  :hints (("Goal"
           :use ((:instance intersection-point-nonstd-in-intersection)
                 (:instance intersection-point-is-the-same))
           :in-theory (disable intersection-point-nonstd-in-intersection
                               intersection-point-is-the-same))))

(defthm simplified-cantor-interval-satisfies-nested-intervals-are-nested-strong
   (implies (and (natp m)
                 (posp n)
                 (< m n))
            (and (<= (car (simplified-cantor-interval m)) (car (simplified-cantor-interval n)))
                 (>= (cdr (simplified-cantor-interval m)) (cdr (simplified-cantor-interval n)))))
  :hints (("Goal"
           :cases ((cantor-sequence-indexes-is-sometimes-null)))
          ("Subgoal 2"
           :use ((:instance cantor-sequence-indexes-is-nested-interval-left-strong)
                 (:instance cantor-sequence-indexes-is-nested-interval-right-strong))
           :in-theory (disable cantor-sequence-indexes-is-nested-interval-left-strong
                               cantor-sequence-indexes-is-nested-interval-right-strong))
          )
   :rule-classes (:linear :rewrite))


; Added by Matt K. after v8-2 for (HIDE (COMMENT ...)) change:
(defattach-system hide-with-comment-p constant-nil-function-arity-0)

(defthm intersection-point-in-intersection-simplified
  (and (realp (intersection-point))
       (implies (natp n)
                (and (<= (car (simplified-cantor-interval n))
                         (intersection-point))
                     (<= (intersection-point)
                         (cdr (simplified-cantor-interval n))))))
  :hints (("Goal"
           :cases ((posp n))
           :in-theory (disable intersection-point
                               intersection-point-is-the-same)
           )
          ("Subgoal 2"
           :use ((:instance intersection-point-in-intersection-simplified-lemma (n 1))
                 (:instance simplified-cantor-interval-satisfies-nested-intervals-are-nested-strong (m 0) (n 1)))
           :in-theory (disable intersection-point
                               intersection-point-is-the-same
                               intersection-point-in-intersection-simplified-lemma
                               simplified-cantor-interval-satisfies-nested-intervals-are-nested-strong
                               simplified-cantor-interval
                               ))
          ("Subgoal 1"
           :use ((:instance intersection-point-in-intersection-simplified-lemma (n n))
                 )
           :in-theory (disable intersection-point
                               intersection-point-is-the-same
                               intersection-point-in-intersection-simplified-lemma
                               simplified-cantor-interval-satisfies-nested-intervals-are-nested-strong
                               simplified-cantor-interval
                               ))

          ))

(in-theory (disable intersection-point (intersection-point)))

;; MAJOR MILESTONE:
;; We have a point in the intersection of all the nested intervals!

(defthm intersection-point-in-intersection
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (and (realp (intersection-point))
                (implies (natp n)
                         (and (<= (car (indexes-to-interval (cantor-sequence-indexes n)))
                                  (intersection-point))
                              (<= (intersection-point)
                                  (cdr (indexes-to-interval (cantor-sequence-indexes n))))))))
  :hints (("Goal"
           :use ((:instance intersection-point-in-intersection-simplified))
           )))




(local (in-theory (disable cantor-sequence-indexes-is-sometimes-null (cantor-sequence-indexes-is-sometimes-null))))

(defthm cantor-sequence-indexes-is-pair-of-natps-type-1-useful
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (natp (car (cantor-sequence-indexes-simplified n))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps))))
  :rule-classes (:type-prescription))

(defthm cantor-sequence-indexes-is-pair-of-natps-type-2-useful
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (natp (cdr (cantor-sequence-indexes-simplified n))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps))))
  :rule-classes (:type-prescription))


(defthm cantor-sequence-indexes-is-pair-of-natps-type-1-more-useful
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (posp (+ 1 (car (cantor-sequence-indexes-simplified n)))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps))))
  :rule-classes (:rewrite :type-prescription))

(defthm cantor-sequence-indexes-is-pair-of-natps-type-2-more-useful
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (posp (+ 1 (cdr (cantor-sequence-indexes-simplified n)))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps))))
  :rule-classes (:rewrite :type-prescription))

(defthm not-sometimes-null-always-next-two-indexes-lemma-1
  (implies (and (posp n)
                (> (car (cantor-sequence-indexes (+ -1 n))) (cdr (cantor-sequence-indexes (+ -1 n))))
                (not (exist-next-two-indexes-in-range (+ 1 (car (cantor-sequence-indexes (+ -1 n))))
                                                      (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n))))
                                                      (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           (null (cantor-sequence-indexes n)))
  :hints (("Goal"
           :induct (cantor-sequence-indexes n)
           :in-theory (disable simplify-cantor-sequence
                               next-two-indexes-in-range
                               exist-next-two-indexes-in-range))))

(defthm not-sometimes-null-always-next-two-indexes-lemma-2
  (implies (and (posp n)
                (<= (car (cantor-sequence-indexes (+ -1 n))) (cdr (cantor-sequence-indexes (+ -1 n))))
                (not (exist-next-two-indexes-in-range (+ 1 (cdr (cantor-sequence-indexes (+ -1 n))))
                                                      (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n))))
                                                      (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n)))))))
           (null (cantor-sequence-indexes n)))
  :hints (("Goal"
           :induct (cantor-sequence-indexes n)
           :in-theory (disable simplify-cantor-sequence
                               next-two-indexes-in-range
                               exist-next-two-indexes-in-range))))

(defthm not-sometimes-null-always-next-two-indexes-1
  (implies (and (posp n)
                (not (cantor-sequence-indexes-is-sometimes-null))
                (> (car (cantor-sequence-indexes-simplified (+ -1 n))) (cdr (cantor-sequence-indexes-simplified (+ -1 n)))))
           (exist-next-two-indexes-in-range (+ 1 (car (cantor-sequence-indexes-simplified (+ -1 n))))
                                            (car (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))
                                            (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null)
                 (:instance not-sometimes-null-always-next-two-indexes-lemma-1))
           :in-theory (disable cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null
                               cantor-sequence-indexes
                               cantor-sequence-indexes-simplified
                               )))
  )

(defthm not-sometimes-null-always-next-two-indexes-2
  (implies (and (posp n)
                (not (cantor-sequence-indexes-is-sometimes-null))
                (<= (car (cantor-sequence-indexes-simplified (+ -1 n))) (cdr (cantor-sequence-indexes-simplified (+ -1 n)))))
           (exist-next-two-indexes-in-range (+ 1 (cdr (cantor-sequence-indexes-simplified (+ -1 n))))
                                            (car (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))
                                            (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null)
                 (:instance not-sometimes-null-always-next-two-indexes-lemma-2))
           :in-theory (disable cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null
                               cantor-sequence-indexes
                               cantor-sequence-indexes-simplified
                               )))
  )

(defthm cantor-sequence-indexes-grow-at-2n-lemma
  (implies (and (natp n)
                (not (cantor-sequence-indexes-is-sometimes-null)))
           (and (<= (1- (* 2 n))
                    (car (cantor-sequence-indexes-simplified n)))
                (<= (* 2 n)
                    (cdr (cantor-sequence-indexes-simplified n)))))
  :hints (("Subgoal *1/2"
           :use ((:instance next-two-indexes-in-range-valid
                            (n (+ 1 (max (car (cantor-sequence-indexes-simplified (+ -1 n)))
                                         (cdr (cantor-sequence-indexes-simplified (+ -1 n))))))
                            (a (car (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n)))))
                            (b (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))))
                 (:instance cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null))
           :in-theory (disable next-two-indexes-in-range-valid
                               cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null
                               indexes-to-interval
                               next-two-indexes-in-range
                               exist-next-two-indexes-in-range)))
  )



(defthm next-index-in-range-minimal
  (implies (and (posp n)
                (natp m)
                (<= n m)
                (< m (next-index-in-range n A B)))
           (not (in-range (seq m) A B)))
  :hints (("Goal"
           :use ((:instance next-index-in-range-valid-lemma))
           :in-theory (disable next-index-in-range-valid-lemma
                               in-range))))

(defthm cantor-sequence-index-lemma
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (natp i)
                (>= i (1+ (max (car (cantor-sequence-indexes-simplified (1- n)))
                               (cdr (cantor-sequence-indexes-simplified (1- n))))))
                (< i (car (cantor-sequence-indexes-simplified n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance next-index-in-range-minimal
                            (n (1+ (max (car (cantor-sequence-indexes-simplified (1- n)))
                                        (cdr (cantor-sequence-indexes-simplified (1- n))))))
                            (m i)
                            (A (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))))
           :in-theory (disable next-index-in-range-minimal
                               indexes-to-interval
                               in-range))))

(defthm max-cantor-sequence-is-useless
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (< (car (cantor-sequence-indexes-simplified n))
              (cdr (cantor-sequence-indexes-simplified n))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance next-two-indexes-in-range-valid
                            (n (1+ (max (car (cantor-sequence-indexes-simplified (1- n)))
                                        (cdr (cantor-sequence-indexes-simplified (1- n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))))
                 (:instance cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null))
           :in-theory (disable next-two-indexes-in-range-valid
                               indexes-to-interval
                               exist-next-two-indexes-in-range
                               next-two-indexes-in-range
                               cantor-sequence-not-null-if-not-cantor-sequence-indexes-is-sometimes-null))))

(defthm max-cantor-sequence-is-useless-stronger
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (natp n))
           (equal (max (car (cantor-sequence-indexes-simplified n))
                       (cdr (cantor-sequence-indexes-simplified n)))
                  (cdr (cantor-sequence-indexes-simplified n))))
  :hints (("Goal"
           :cases ((posp n))
           :in-theory (disable cantor-sequence-indexes-simplified))
          ("Subgoal 1"
           :use ((:instance max-cantor-sequence-is-useless))
           :in-theory (disable max-cantor-sequence-is-useless
                               cantor-sequence-indexes-simplified))))

(defthm cantor-sequence-index-lemma-stronger
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp   n)
                (natp i)
                (> i (cdr (cantor-sequence-indexes-simplified (1- n))))
                (< i (car (cantor-sequence-indexes-simplified n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))))
  :hints (("Goal"
           :use ((:instance max-cantor-sequence-is-useless-stronger (n (1- n)))
                 (:instance cantor-sequence-index-lemma))
           :in-theory (disable max-cantor-sequence-is-useless-stronger
                               cantor-sequence-index-lemma
                               indexes-to-interval
                               cantor-sequence-indexes-simplified))))

(defthm not-sometimes-null-always-next-two-indexes-of-max
  (implies (and (posp n)
                (not (cantor-sequence-indexes-is-sometimes-null)))
           (exist-next-two-indexes-in-range (+ 1 (max (car (cantor-sequence-indexes-simplified (+ -1 n)))
                                                      (cdr (cantor-sequence-indexes-simplified (+ -1 n)))))
                                            (car (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))
                                            (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (+ -1 n))))))
  :hints (("Goal"
           :use ((:instance not-sometimes-null-always-next-two-indexes-1)
                 (:instance not-sometimes-null-always-next-two-indexes-2))
           :in-theory (disable not-sometimes-null-always-next-two-indexes-1
                               not-sometimes-null-always-next-two-indexes-2
                               cantor-sequence-indexes
                               cantor-sequence-indexes-simplified
                               max-cantor-sequence-is-useless-stronger
                               )))
  )

(defthm not-sometimes-null-always-next-two-indexes-no-simplify-of-max
  (implies (and (posp n)
                (not (cantor-sequence-indexes-is-sometimes-null)))
           (exist-next-two-indexes-in-range (+ 1 (max (car (cantor-sequence-indexes (+ -1 n)))
                                                      (cdr (cantor-sequence-indexes (+ -1 n)))))
                                            (car (indexes-to-interval (cantor-sequence-indexes (+ -1 n))))
                                    (cdr (indexes-to-interval (cantor-sequence-indexes (+ -1 n))))))
  :hints (("Goal"
           :use ((:instance not-sometimes-null-always-next-two-indexes-of-max))
           :in-theory (disable not-sometimes-null-always-next-two-indexes-of-max
                               cantor-sequence-indexes
                               cantor-sequence-indexes-simplified
                               EXIST-NEXT-TWO-INDEXES-IN-RANGE
                               INDEXES-TO-INTERVAL
                               ))))


(defthm car-cantor-sequence-increases-lemma
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (<= (1+ (max (car (cantor-sequence-indexes (1- n)))
                        (cdr (cantor-sequence-indexes (1- n)))))
               (car (next-two-indexes-in-range (1+ (max (car (cantor-sequence-indexes (1- n)))
                                                        (cdr (cantor-sequence-indexes (1- n)))))
                                               (car (indexes-to-interval (cantor-sequence-indexes (1- n))))
                                               (cdr (indexes-to-interval (cantor-sequence-indexes (1- n))))))))
  :hints (("goal" :do-not-induct t
           :use ((:instance next-two-indexes-in-range-valid
                            (n (1+ (max (car (cantor-sequence-indexes (1- n)))
                                        (cdr (cantor-sequence-indexes (1- n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (1- n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (1- n))))))
                 (:instance cantor-sequence-indexes-is-pair-of-natps-type-1-more-useful (n (1- n)))
                 (:instance cantor-sequence-indexes-is-pair-of-natps-type-2-more-useful (n (1- n)))
                 (:instance simplify-cantor-sequence (n (1- n))))
    :in-theory (disable next-two-indexes-in-range-valid
                        simplify-cantor-sequence
                        max-cantor-sequence-is-useless-stronger
                        exist-next-two-indexes-in-range
                        indexes-to-interval))))


(defthm car-cantor-sequence-increases
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (< (car (cantor-sequence-indexes (1- n)))
              (car (cantor-sequence-indexes n))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance car-cantor-sequence-increases-lemma)
                 (:instance not-sometimes-null-always-next-two-indexes-no-simplify-of-max))
           :in-theory (disable car-cantor-sequence-increases-lemma
                               not-sometimes-null-always-next-two-indexes-no-simplify-of-max
                               not-sometimes-null-always-next-two-indexes-1
                               not-sometimes-null-always-next-two-indexes-2
                               max-cantor-sequence-is-useless-stronger
                               simplify-cantor-sequence
                               next-two-indexes-in-range-valid
                               next-two-indexes-in-range
                               exist-next-two-indexes-in-range
                               indexes-to-interval))))

(defthm exists-next-two-indexes-then-posp-next-index
  (implies (and (posp n)
                (exist-next-two-indexes-in-range n A B))
           (posp (+ 1 (next-index-in-range n A B))))
  :hints (("Goal"
           :use ((:instance next-index-in-range-valid))
           :in-theory (disable next-index-in-range-valid
                               exists-next-index-in-range
                               ))))

(defthm force-n-to-zero-when-cdr-less-than-car
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (< (cdr (cantor-sequence-indexes (+ -1 n)))
                   (car (cantor-sequence-indexes (+ -1 n)))))
           (equal (+ -1 n) 0))
  :hints (("Goal"
           :use ((:instance max-cantor-sequence-is-useless (n (1- n))))
           :in-theory (disable cantor-sequence-indexes-simplified
                               cantor-sequence-indexes
                               max-cantor-sequence-is-useless))))

(defthm next-two-indexes-in-range-minimal-part-1
  (implies (and (posp n)
                (natp m)
v                (<= n m)
                (< m (car (next-two-indexes-in-range n A B))))
           (not (in-range (seq m) A B)))
  :hints (("Goal"
           :use ((:instance next-index-in-range-minimal
                            (n n)
                            (m m)
                            (A A)
                            (B B))
                 (:instance next-index-in-range-minimal
                            (n (1+ (next-index-in-range n A B)))
                            (m m)
                            (A (seq (next-index-in-range n A B)))
                            (B B))
                 )
           :in-theory (disable ;next-index-in-range
                               in-range))))

(defthm next-two-indexes-in-range-minimal-part-2
  (implies (and (exists-next-index-in-range n A B)
                (posp n)
                (natp m)
                ;(<= n m)
                (< (car (next-two-indexes-in-range n A B)) m)
                (< m (cdr (next-two-indexes-in-range n A B))))
           (not (in-range (seq m) (seq (next-index-in-range n A B)) B)))
  :hints (("Goal"
           :use ((:instance next-index-in-range-minimal
                            (n n)
                            (m m)
                            (A A)
                            (B B))
                 (:instance next-index-in-range-minimal
                            (n (1+ (next-index-in-range n A B)))
                            (m m)
                            (A (seq (next-index-in-range n A B)))
                            (B B))
                 (:instance next-index-in-range-valid)
                 )
           :in-theory (disable next-index-in-range-valid
                               next-index-in-range-valid-lemma
                               exists-next-index-in-range))))

(defthm next-two-indexes-in-range-minimal
  (implies (and (exist-next-two-indexes-in-range n A B)
                (posp n)
                (natp m)
                ;(<= n m)
                (< (car (next-two-indexes-in-range n A B)) m)
                (< m (cdr (next-two-indexes-in-range n A B))))
           (not (in-range (seq m)
                          (seq (car (next-two-indexes-in-range n A B)))
                          (seq (cdr (next-two-indexes-in-range n A B))))))
  :hints (("Goal"
           :use ((:instance next-index-in-range-minimal
                            (n n)
                            (m m)
                            (A A)
                            (B B))
                 (:instance next-index-in-range-minimal
                            (n (1+ (next-index-in-range n A B)))
                            (m m)
                            (A (seq (next-index-in-range n A B)))
                            (B B))
                 (:instance next-two-indexes-in-range-valid)
                 (:instance next-index-in-range-valid)
                 (:instance next-index-in-range-valid
                            (n (1+ (next-index-in-range n A B)))
                            (A (seq (next-index-in-range n A B)))
                            (B B))
                 )
           :in-theory (disable next-index-in-range-valid
                               next-index-in-range-valid-lemma
                               next-two-indexes-in-range-valid
                               exists-next-index-in-range
                               NEXT-TWO-INDEXES-IN-RANGE-MINIMAL-PART-2))))

(defthm not-in-range-monotonic
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (not (in-range x
                               (car (indexes-to-interval (cantor-sequence-indexes (1- n))))
                               (cdr (indexes-to-interval (cantor-sequence-indexes (1- n)))))))
           (not (in-range x
                          (car (indexes-to-interval (cantor-sequence-indexes n)))
                          (cdr (indexes-to-interval (cantor-sequence-indexes n))))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-is-nested-interval-right)
                 (:instance cantor-sequence-indexes-is-nested-interval-left))
           :in-theory (disable cantor-sequence-indexes-is-nested-interval-right
                               cantor-sequence-indexes-is-nested-interval-left
                               cantor-sequence-indexes
                               indexes-to-interval))))

(defthm max-cantor-sequence-is-useless-for-natps
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (natp n))
           (<= (car (cantor-sequence-indexes-simplified n))
               (cdr (cantor-sequence-indexes-simplified n))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance max-cantor-sequence-is-useless))
           :in-theory (disable max-cantor-sequence-is-useless
                               cantor-sequence-indexes-simplified))))

(defthm max-cantor-sequence-no-simplify-is-useless-for-natps
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (natp n))
           (<= (car (cantor-sequence-indexes n))
               (cdr (cantor-sequence-indexes n))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance max-cantor-sequence-is-useless-for-natps)))))

(defthm can-cdr-cantor-sequence-lemma-contradiction
  (implies (and (< (car (next-two-indexes-in-range n A B)) i)
                (posp n)
                (exist-next-two-indexes-in-range n A B))
           (not (< i n)))
  :hints (("Goal"
           :use ((:instance next-two-indexes-in-range-valid))
           :in-theory (disable next-two-indexes-in-range-valid
                               next-two-indexes-in-range
                               exist-next-two-indexes-in-range)
           )))
#|

(defthm car-next-two-indexes-in-range
  (equal (car (next-two-indexes-in-range n A B))
         (next-index-in-range n A B)))
|#

(defthm car-cantor-sequence-indexes
  (implies (and (NOT (CANTOR-SEQUENCE-INDEXES-IS-SOMETIMES-NULL))
                (posp n))
           (equal (car (cantor-sequence-indexes n))
                  (car (next-two-indexes-in-range (1+ (max (car (cantor-sequence-indexes (1- n)))
                                                           (cdr (cantor-sequence-indexes (1- n)))))
                                                  (car (indexes-to-interval (cantor-sequence-indexes (1- n))))
                                                  (cdr (indexes-to-interval (cantor-sequence-indexes (1- n))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance not-sometimes-null-always-next-two-indexes-no-simplify-of-max))
           :in-theory (disable simplify-cantor-sequence
                               exist-next-two-indexes-in-range
                               indexes-to-interval
                               not-sometimes-null-always-next-two-indexes-no-simplify-of-max))
          )
  )

(defthm cdr-cantor-sequence-indexes
  (implies (and (NOT (CANTOR-SEQUENCE-INDEXES-IS-SOMETIMES-NULL))
                (posp n))
           (equal (cdr (cantor-sequence-indexes n))
                  (cdr (next-two-indexes-in-range (1+ (max (car (cantor-sequence-indexes (1- n)))
                                                           (cdr (cantor-sequence-indexes (1- n)))))
                                                  (car (indexes-to-interval (cantor-sequence-indexes (1- n))))
                                                  (cdr (indexes-to-interval (cantor-sequence-indexes (1- n))))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance not-sometimes-null-always-next-two-indexes-no-simplify-of-max))
           :in-theory (disable simplify-cantor-sequence
                               exist-next-two-indexes-in-range
                               indexes-to-interval
                               not-sometimes-null-always-next-two-indexes-no-simplify-of-max))
          )
  )

(defthm car-indexes-to-interval
  (implies (and (posp n)
                (exist-next-two-indexes-in-range n A B))
           (equal (car (indexes-to-interval (next-two-indexes-in-range n A B)))
                  (seq (car (next-two-indexes-in-range n A B))))))


(defthm cdr-indexes-to-interval
  (implies (and (posp n)
                (exist-next-two-indexes-in-range n A B))
           (equal (cdr (indexes-to-interval (next-two-indexes-in-range n A B)))
                  (seq (cdr (next-two-indexes-in-range n A B))))))


(defthm car-cdr-cantor-sequence-lemma
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (posp i)
                (> i (car (cantor-sequence-indexes n)))
                (< i (cdr (cantor-sequence-indexes n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes n)))
                          (cdr (indexes-to-interval (cantor-sequence-indexes n))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance next-two-indexes-in-range-minimal
                            (n (1+ (max (car (cantor-sequence-indexes (1- n)))
                                        (cdr (cantor-sequence-indexes (1- n))))))
                            (A (car (indexes-to-interval (cantor-sequence-indexes (1- n)))))
                            (B (cdr (indexes-to-interval (cantor-sequence-indexes (1- n)))))
                            (m i))
                 (:instance not-sometimes-null-always-next-two-indexes-no-simplify-of-max))
           :in-theory (disable next-two-indexes-in-range-minimal-part-1
                               next-two-indexes-in-range-minimal-part-2
                               next-two-indexes-in-range-minimal
                               next-two-indexes-in-range
                               indexes-to-interval
                               simplify-cantor-sequence
                               cantor-sequence-indexes-simplified
                               max-cantor-sequence-is-useless
                               not-sometimes-null-always-next-two-indexes-no-simplify-of-max
                               exist-next-two-indexes-in-range
                               exists-next-index-in-range
                               in-range
                               ))))

(defthm not-in-range-left-boundary
  (not (in-range a a b)))

(defthm in-range-endpoints-lemma
  (implies (and (posp (car l))
                (posp (cdr l)))
           (and (not (in-range (seq (car l))
                               (car (indexes-to-interval l))
                               (cdr (indexes-to-interval l))))
                (not (in-range (seq (cdr l))
                               (car (indexes-to-interval l))
                               (cdr (indexes-to-interval l)))))))

(defthm cantor-sequence-indexes-is-pair-of-posps
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (and (posp (car (cantor-sequence-indexes-simplified n)))
                (posp (cdr (cantor-sequence-indexes-simplified n)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cantor-sequence-indexes-is-pair-of-natps-type-1-useful (n (1- n)))
                 (:instance cantor-sequence-indexes-is-pair-of-natps-type-1-useful)
                 (:instance car-cantor-sequence-increases)
                 (:instance max-cantor-sequence-is-useless-for-natps)
                 )
           :in-theory (disable cantor-sequence-indexes-is-pair-of-natps-type-1-useful
                               car-cantor-sequence-increases
                               cantor-sequence-indexes-simplified
                               cantor-sequence-indexes
                               max-cantor-sequence-is-useless-for-natps
                               ))
          ))



(defthm cantor-sequence-endpoints-lemma
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (and (not (in-range (seq (car (cantor-sequence-indexes n)))
                               (car (indexes-to-interval (cantor-sequence-indexes n)))
                               (cdr (indexes-to-interval (cantor-sequence-indexes n)))))
                (not (in-range (seq (cdr (cantor-sequence-indexes n)))
                               (car (indexes-to-interval (cantor-sequence-indexes n)))
                               (cdr (indexes-to-interval (cantor-sequence-indexes n)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance in-range-endpoints-lemma
                            (l (cantor-sequence-indexes n)))
                 (:instance cantor-sequence-indexes-is-pair-of-posps)
                 )
           :in-theory (disable cantor-sequence-indexes
                               cantor-sequence-indexes-simplified
                               indexes-to-interval

                               in-range
                               ))))

(defthm car-cdr-cantor-sequence-lemma-strong
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (posp i)
                (>= i (car (cantor-sequence-indexes n)))
                (<= i (cdr (cantor-sequence-indexes n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes n)))
                          (cdr (indexes-to-interval (cantor-sequence-indexes n))))))
  :hints (("Goal"
           :use ((:instance car-cdr-cantor-sequence-lemma)
                 (:instance cantor-sequence-endpoints-lemma))
           :in-theory (disable car-cdr-cantor-sequence-lemma
                               cantor-sequence-endpoints-lemma
                               indexes-to-interval
                               cantor-sequence-indexes
                               simplify-cantor-sequence
                               car-cantor-sequence-indexes
                               cdr-cantor-sequence-indexes
                               in-range
                               max
                               next-two-indexes-in-range
                               ))))

(defthm cantor-sequence-index-lemma-even-stronger
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (posp i)
                (>= i (car (cantor-sequence-indexes-simplified (1- n))))
                (< i (car (cantor-sequence-indexes-simplified n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance cantor-sequence-index-lemma-stronger)
                 (:instance car-cdr-cantor-sequence-lemma-strong (n (1- n))))
           :in-theory (disable cantor-sequence-index-lemma-stronger
                               car-cdr-cantor-sequence-lemma-strong
                               cantor-sequence-indexes-simplified
                               cantor-sequence-indexes
                               indexes-to-interval
                               car-indexes-to-interval
                               cdr-indexes-to-interval))))

(defun natural-induction (n)
  (if (zp n)
      n
    (natural-induction (1- n))))

(defthm cantor-sequence-index-main-lemma-at-boundary
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (not (posp (1- n)))
                (posp i)
                (< i (car (cantor-sequence-indexes-simplified n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))))))

(defthm cantor-sequence-index-main-lemma
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n)
                (posp i)
                (< i (car (cantor-sequence-indexes-simplified n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified (1- n))))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified (1- n)))))))
  :hints (("Goal"
           :do-not-induct t
           :induct (natural-induction n))
          ("Subgoal *1/2"
           :use ((:instance cantor-sequence-index-main-lemma-at-boundary)
                 (:instance cantor-sequence-index-lemma-even-stronger)
                 (:instance not-in-range-monotonic (x (seq i)) (n (1- n))))
           :in-theory (disable indexes-to-interval
                               cantor-sequence-indexes-simplified
                               cantor-sequence-index-main-lemma-at-boundary
                               cantor-sequence-index-lemma-even-stronger
                               not-in-range-monotonic
                               in-range))
          ))

(defthm cantor-sequence-indexes-contradiction
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (natp n)
                (posp i)
                (< i (1+ (* 2 n))))
           (not (in-range (seq i)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified n)))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified n))))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-index-main-lemma (n (1+ n)))
                 (:instance cantor-sequence-indexes-grow-at-2n-lemma  (n (1+ n))))
           :in-theory (disable cantor-sequence-indexes-grow-at-2n-lemma
                               cantor-sequence-index-main-lemma
                               indexes-to-interval
                               cantor-sequence-indexes-simplified
                               in-range))))

;; MAJOR MILESTONE:
;; Now, if the cantor sequence is never null, we find that for each element in the sequence,
;; there is some interval that does not contain the point

(defthm cantor-sequence-not-in-corresponding-interval
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (not (in-range (seq n)
                          (car (indexes-to-interval (cantor-sequence-indexes-simplified n)))
                          (cdr (indexes-to-interval (cantor-sequence-indexes-simplified n))))))
  :hints (("Goal"
           :use ((:instance cantor-sequence-indexes-contradiction))
           :in-theory (disable indexes-to-interval
                               cantor-sequence-indexes-simplified
                               in-range))))

(defthm intersection-point-in-all-open-intervals
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (and (realp (intersection-point))
                (implies (posp n)
                         (in-range (intersection-point)
                                   (car (indexes-to-interval (cantor-sequence-indexes n)))
                                   (cdr (indexes-to-interval (cantor-sequence-indexes n)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance intersection-point-in-intersection (n (1+ n)))
                 (:instance cantor-sequence-indexes-is-nested-interval-left (n (1+ n)))
                 (:instance cantor-sequence-indexes-is-nested-interval-right (n (1+ n)))
                 )
           :in-theory (disable indexes-to-interval
                               cantor-sequence-indexes-is-nested-interval-left
                               cantor-sequence-indexes-is-nested-interval-right
                               cantor-sequence-indexes-simplified
                               cantor-sequence-indexes))))


(defthm intersection-point-not-in-sequence
  (implies (and (not (cantor-sequence-indexes-is-sometimes-null))
                (posp n))
           (not (equal (intersection-point) (seq n))))
  :hints (("Goal"
           :use ((:instance intersection-point-in-all-open-intervals)
                 (:instance cantor-sequence-not-in-corresponding-interval))
           :in-theory (disable intersection-point-in-all-open-intervals
                               cantor-sequence-not-in-corresponding-interval
                               indexes-to-interval
                               cantor-sequence-indexes-simplified
                               cantor-sequence-indexes))))


(defthm intersection-point-not-in-sequence-sk
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (not (exists-in-sequence (intersection-point))))
  )

(defthm intersection-point-not-in-boundary
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (and (realp (intersection-point))
                (< (a) (intersection-point))
                (< (intersection-point) (b))
                ))
  :hints (("Goal" :do-not-induct t
           :use ((:instance intersection-point-in-intersection (n 1))
                 (:instance cantor-sequence-indexes-is-nested-interval-left (n 1))
                 (:instance cantor-sequence-indexes-is-nested-interval-right (n 1))
                 )
           :in-theory (disable (indexes-to-interval)
                               (cantor-sequence-indexes)
                               (cantor-sequence-indexes-simplified)
                               intersection-point-in-intersection
                               intersection-point-in-intersection-simplified
                               intersection-point-in-intersection-simplified-lemma
                               intersection-point-in-all-open-intervals
                               cantor-sequence-indexes-is-nested-interval-left
                               cantor-sequence-indexes-is-nested-interval-right
                               cantor-sequence-indexes))))



;; MAJOR MILESTONE:
;; Now if the cantor sequence of index never fails, then there's an intersection point,
;; and that intersection point is in all the intervals but is not one of the sequence points

(defthm intersection-point-not-in-sequence-if-not-null-cantor-sequence-indexes
  (implies (not (cantor-sequence-indexes-is-sometimes-null))
           (exists-in-interval-but-not-in-sequence (a) (b)))
  :hints (("Goal"
           :use ((:instance exists-in-interval-but-not-in-sequence-suff
                            (x (intersection-point))
                            (a (a))
                            (b (b))
                            )
                 (:instance intersection-point-not-in-boundary))
           :in-theory (disable intersection-point-not-in-boundary))))

;; MAJOR MILESTONE: MAIN THEOREM

(defthm reals-are-not-countable
  (exists-in-interval-but-not-in-sequence (a) (b))
  :hints (("Goal"
           :use ((:instance critical-pair-valid-if-null-cantor-sequence-indexes)
                 (:instance intersection-point-not-in-sequence-if-not-null-cantor-sequence-indexes)))))
