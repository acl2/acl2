(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "make-partition")
(include-book "top-with-meta")

;;; These were originally proved in
;;; riemann-sum-approximates-integral-1.lisp.

(local
 (defthm car-make-partition-rec
   (equal (car (make-partition-rec a delta n))
          a)))

;;; In order to avoid hanging rewrite rules on car, we make the
;;; following a forward-chaining rules.
(defthm car-make-partition
  (equal (car (make-partition a b n))
         a)
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((make-partition a b n)))))

(local
 (defthm car-last-make-partition-rec
   (implies (and (realp a)
                 (realp delta)
                 (integerp n)
                 (<= 0 n))
            (equal (car (last (make-partition-rec a delta n)))
                   (+ a (* delta n))))))

;;; In order to avoid hanging rewrite rules on car, we make the
;;; following a forward-chaining rules.
(defthm car-last-make-partition
  (implies (and (realp a)
                (realp b)
                (< a b)
                (integerp n)
                (< 0 n))
           (equal (car (last (make-partition a b n)))
                  b))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((make-partition a b n)))))

(local
 (defthm partitionp-make-partition-rec
   (implies (and (realp a)
                 (realp delta)
                 (< 0 delta))
            (partitionp (make-partition-rec a delta n)))))

(defthm partitionp-make-partition
  (implies (and (realp a)
                (realp b)
                (< a b)
                (integerp n)
                (< 0 n))
           (partitionp (make-partition a b n))))

;;; This :forward-chaining version of the lemma above is useful when
;;; trying to prove (realp (rcfn (min-x-rec (make-partition a b x)))),
;;; since realp-min-x-rec is a :type-prescription lemma and hence its
;;; partitionp hypothesis must be relieved without rewriting.
(defthm partitionp-make-partition-forward
  (implies (and (realp a)
                (realp b)
                (< a b)
                (integerp n)
                (< 0 n))
           (partitionp (make-partition a b n)))
  :rule-classes
  ((:forward-chaining
    :trigger-terms ((make-partition a b n)))))

(local
 (defthm mesh-make-partition-rec
   (implies (and (realp a)
                 (realp delta)
                 (< 0 delta)
                 (integerp n)
                 (< 1 n))
            (equal (maxlist (deltas (make-partition-rec a delta n)))
                   delta))
   :hints (("Goal" :expand ((make-partition-rec a delta 2)
                            (make-partition-rec (+ a delta) delta 1))))))

(defthm mesh-make-partition
  (implies (and (realp a)
                (realp b)
                (< a b)
                (integerp n)
                (< 1 n))
           (equal (mesh (make-partition a b n))
                  (/ (- b a) n))))
