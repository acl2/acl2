(in-package "ACL2")

(local (include-book "lop1-proofs"))
(include-book "merge") ;BOZO drop

(defund C (k a b)
  (- (bitn a k) (bitn b k)))

(defund PHI (a b d k)
  (if (and (integerp k) (>= k 0))
      (if (= k 0)
	  0
	(if (= d 0)
	    (phi a b (c (1- k) a b) (1- k))
	  (if (= d (- (c (1- k) a b)))
	      (phi a b (- (c (1- k) a b)) (1- k))
	    k)))
    0))

(defthm PHI-MOD
  (implies (and (integerp a)
                (>= a 0)
                (integerp b)
                (>= b 0)
                (integerp d)
                (integerp j)
                (>= j 0)
                (integerp k)
                (>= k j))
           (= (phi a b d j)
              (phi (mod a (expt 2 k)) (mod b (expt 2 k)) d j)))
  :rule-classes ())

(defthm LOP-THM-0
  (implies (and (integerp a)
                (integerp b)
                (integerp n)
                (>= a 0)
                (>= b 0)
                (>= n 0)
                (not (= a b))
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (or (= (phi a b 0 n) (expo (- a b)))
               (= (phi a b 0 n) (1+ (expo (- a b))))))
  :rule-classes ())

