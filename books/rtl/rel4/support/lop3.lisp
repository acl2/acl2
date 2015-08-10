(in-package "ACL2")

(include-book "lop2") ;BOZO yuck!
(local (include-book "lop3-proofs"))

(defund OLAMT (a b e)
  (logxor a (lnot b (1+ e))))

(defund OLAMG (a b e)
  (logand a (lnot b (1+ e))))

(defund OLAMZ (a b e)
  (lnot (logior a (lnot b (1+ e))) (1+ e)))

(defund OLAM1 (a b e)
  (logand (bits (olamt a b e) e 2)
	  (logand (bits (olamg a b e) (1- e) 1)
		  (lnot (bits (olamz a b e) (- e 2) 0) (1- e)))))

(defund OLAM2 (a b e)
  (logand (lnot (bits (olamt a b e) e 2) (1- e))
	  (logand (bits (olamz a b e) (1- e) 1)
		  (lnot (bits (olamz a b e) (- e 2) 0) (1- e)))))

(defund OLAM3 (a b e)
  (logand (bits (olamt a b e) e 2)
	  (logand (bits (olamz a b e) (1- e) 1)
		  (lnot (bits (olamg a b e) (- e 2) 0) (1- e)))))

(defund OLAM4 (a b e)
  (logand (lnot (bits (olamt a b e) e 2) (1- e))
	  (logand (bits (olamg a b e) (1- e) 1)
		  (lnot (bits (olamg a b e) (- e 2) 0) (1- e)))))

(defund OLAM0 (a b e)
  (logior (olam1 a b e)
	  (logior (olam2 a b e)
		  (logior (olam3 a b e)
			  (olam4 a b e)))))

(defund OLAMB (a b e)
  (+ (* 2 (olam0 a b e))
     (lnot (bitn (olamt a b e) 0) 1)))

(defthm OLAMT-NAT
  (implies (and (integerp a)
                (>= a 0)
                )
           (and (integerp (olamt a b e))
                (>= (olamt a b e) 0))))

(defthm OLAMG-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olamg a b e))
                (>= (olamg a b e) 0))))

(defthm OLAMZ-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olamz a b e))
                (>= (olamz a b e) 0))))

(defthm OLAM1-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olam1 a b e))
                (>= (olam1 a b e) 0))))

(defthm OLAM3-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olam3 a b e))
                (>= (olam3 a b e) 0)))
  :rule-classes ())

(defthm OLAM2-NAT
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                )
           (and (integerp (olam2 a b e))
                (>= (olam2 a b e) 0))))

(defthm OLAM4-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olam4 a b e))
                (>= (olam4 a b e) 0))))

(defthm OLAM0-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olam0 a b e))
                (>= (olam0 a b e) 0))))

(defthm OLAMB-NAT
  (implies (and (integerp a)
                (> a 0)
                )
           (and (integerp (olamb a b e))
                (>= (olamb a b e) 0))))

(defthm OLAM1-BND
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1)
                (integerp k)
                (<= k (- e 2))
                (>= k 0))
           (< (olam1 a b e) (expt 2 (- e 1))))
  :rule-classes ())

(defthm OLAM3-BND
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1)
                (integerp k)
                (<= k (- e 2))
                (>= k 0))
           (< (olam3 a b e) (expt 2 (- e 1))))
  :rule-classes ())

(defthm OLAM2-BND
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1)
                (integerp k)
                (<= k (- e 2))
                (>= k 0))
           (< (olam2 a b e) (expt 2 (- e 1))))
  :rule-classes ())

(defthm OLAM4-BND
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1)
                (integerp k)
                (<= k (- e 2))
                (>= k 0))
           (< (olam4 a b e) (expt 2 (- e 1))))
  :rule-classes ())

(defthm OLAM0-BND
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1))
           (< (olam0 a b e) (expt 2 (- e 1))))
  :rule-classes ())

(defthm OLAMB-BND
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1))
           (< (olamb a b e) (expt 2 e)))
  :rule-classes ())

(defthm olop-thm-2
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (olamb a b e) 0))
		  (or (= (expo (- a b)) (expo (olamb a b e)))
		      (= (expo (- a b)) (1- (expo (olamb a b e)))))))
  :rule-classes ())

(include-book "land")
(include-book "lior")
(include-book "lxor")

(defun lamt (a b e)
  (lxor a (lnot b (1+ e)) (1+ e)))

(defun lamg (a b e)
  (land a (lnot b (1+ e)) (1+ e)))

(defun lamz (a b e)
  (lnot (lior a (lnot b (1+ e)) (1+ e)) (1+ e)))

(defun lam1 (a b e)
  (land (bits (lamt a b e) e 2)
	(land (bits (lamg a b e) (1- e) 1)
	      (lnot (bits (lamz a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam2 (a b e)
  (land (lnot (bits (lamt a b e) e 2) (1- e))
	(land (bits (lamz a b e) (1- e) 1)
	      (lnot (bits (lamz a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam3 (a b e)
  (land (bits (lamt a b e) e 2)
	(land (bits (lamz a b e) (1- e) 1)
	      (lnot (bits (lamg a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam4 (a b e)
  (land (lnot (bits (lamt a b e) e 2) (1- e))
	(land (bits (lamg a b e) (1- e) 1)
	      (lnot (bits (lamg a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam0 (a b e)
  (lior (lam1 a b e)
	(lior (lam2 a b e)
	      (lior (lam3 a b e)
		    (lam4 a b e)
		    (1- e))
	      (1- e))
	(1- e)))

(defun lamb (a b e)
  (+ (* 2 (lam0 a b e))
     (lnot (bitn (lamt a b e) 0) 1)))

(in-theory (enable bits-tail bvecp-expo)) ;BOZO yuck!

(defthm lop-thm-2
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (lamb a b e) 0))
		  (or (= (expo (- a b)) (expo (lamb a b e)))
		      (= (expo (- a b)) (1- (expo (lamb a b e)))))))
  :rule-classes ())


