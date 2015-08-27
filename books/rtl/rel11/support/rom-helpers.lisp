(in-package "RTL")

(include-book "definitions")
(local (include-book "bits"))

(defun check-array (name a dim1 dim2)
  (if (zp dim1)
      t
    (and (bvecp (aref1 name a (1- dim1)) dim2)
	 (check-array name a (1- dim1) dim2))))

(defthm check-array-lemma-1
    (implies (and (not (zp dim1))
		  (check-array name a dim1 dim2)
		  (natp i)
		  (< i dim1))
	     (bvecp (aref1 name a i) dim2))
  :rule-classes ())

(defthm check-array-lemma
    (implies (and (bvecp i n)
		  (not (zp (expt 2 n)))
		  (check-array name a (expt 2 n) dim2))
	     (bvecp (aref1 name a i) dim2))
  :hints (("goal" :use (:instance check-array-lemma-1 (dim1 (expt 2 n)))))
  :rule-classes ())


