(in-package "ACL2")

(local (include-book "lop1-proofs"))
(include-book "merge") ;BOZO drop

(defund lop (a b d k)
  (let ((c (- (bitn a (1- k)) (bitn b (1- k)))))
    (if (and (integerp k) (>= k 0))
	(if (= k 0)
	    0
	  (if (= d 0)
	      (lop a b c (1- k))
	    (if (= d (- c))
		(lop a b (- c) (1- k))
	      k)))
      0)))

(defthm LOP-MOD
  (implies (and (integerp a)
                (>= a 0)
                (integerp b)
                (>= b 0)
                (integerp d)
                (integerp j)
                (>= j 0)
                (integerp k)
                (>= k j))
           (= (lop a b d j)
              (lop (mod a (expt 2 k)) (mod b (expt 2 k)) d j)))
  :rule-classes ())

(defthm LOP-BNDS
  (implies (and (integerp a)
                (integerp b)
                (integerp n)
                (>= a 0)
                (>= b 0)
                (>= n 0)
                (not (= a b))
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (or (= (lop a b 0 n) (expo (- a b)))
               (= (lop a b 0 n) (1+ (expo (- a b))))))
  :rule-classes ())

