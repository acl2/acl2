(in-package "RTL")

(include-book "round")

(include-book "arithmetic-5/top" :dir :system)

(defthmd rd-1
  (implies (formatp f)
           (and (natp (prec f))
	        (>= (prec f) 2)
		(natp (bias f))))
  :hints (("Goal" :in-theory (enable formatp expw bias prec))))

(defthmd rd-2
  (implies (and (formatp f)
		(rationalp m)
		(< 0 m)
		(< m 1/2))
	   (< (expo (* (spn f) m)) (1- (expo (spn f)))))
  :hints (("Goal" :use ((:instance expo<= (x m) (n -2))
                        (:instance expo-shift (x m) (n (- 1 (bias f)))))
		  :in-theory (enable spn))))

(defthmd rd-3
  (implies (and (formatp f)
		(rationalp m)
		(< 0 m)
		(< m 1/2)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p)))
	     (< r (spn f))))
  :hints (("Goal" :use (rd-1 rd-2
                        (:instance expo-rnd (x (* (spn f) m)) (n (prec f)))
			(:instance expo-monotone (x (spn f)) (y (rnd (* (spn f) m) mode (prec f))))))))

(defthmd rd-4
  (implies (and (formatp f)
		(rationalp m)
		(< 0 m)
		(< m 1/2)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (d (drnd x mode f)))
	     (< d (spn f))))
  :hints (("Goal" :use (rd-1
                        (:instance drnd-diff (x (* (spn f) m))))
		  :in-theory (enable spn spd)
		  :nonlinearp t)))

(defthmd rd-5
  (implies (and (formatp f)
		(rationalp m)
		(< 0 m)
		(< m 1/2)
                (common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p))
		  (d (drnd x mode f)))
	     (case mode
	       ((rdn rtz) (and (< r (spn f)) (< d (spn f))))
	       ((rup raz) (and (iff (< r (spn f)) (<= m (- 1 (expt 2 (- p)))))
	                       (iff (< d (spn f)) (<= m (- 1 (expt 2 (- 1 p)))))))
	       ((rne rna) (and (iff (< r (spn f)) (< m (- 1 (expt 2 (- (1+ p))))))
	                       (iff (< d (spn f)) (< m (- 1 (expt 2 (- p))))))))))
  :hints (("Goal" :use (rd-1 rd-3 rd-4)
                  :in-theory (enable ieee-rounding-mode-p common-mode-p)
                  :nonlinearp t)))

(defthm rd-6
  (implies (and (rationalp m)
		(>= m 1/2)
		(< m 1))
	   (equal (expo m) -1))
  :hints (("Goal" :use ((:instance expo>= (x m) (n -1))
                        (:instance expo<= (x m) (n -1))))))

(defthm rd-7
  (implies (and (formatp f)
                (rationalp m)
		(>= m 1/2)
		(< m 1))
	   (equal (expo (* (spn f) m)) (1- (expo (spn f)))))
  :hints (("Goal" :in-theory (enable spn) :use (rd-6 (:instance expo-shift (x m) (n (- 1 (bias f))))))))

(defthmd rd-8
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (d (drnd x mode f)))
	     (equal d (rnd x mode (1- p)))))
  :hints (("Goal" :use (rd-1 rd-7)
                  :in-theory (enable drnd))))

(defthmd rd-9
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p)))
	     (iff (< r (spn f))
	          (< (rnd m mode p) 1))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable spn)
                  :use (rd-1 (:instance rnd-shift (k (- 1 (bias f))) (x m) (n (prec f)))))))

(defthmd rd-10
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (d (drnd x mode f)))
	     (iff (< d (spn f))
	          (< (rnd m mode (1- p)) 1))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable spn)
                  :use (rd-8 (:instance rnd-shift (k (- 1 (bias f))) (x m) (n (1- (prec f))))))))

(defthmd rd-a
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(rtz rdn)))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p))
		  (d (drnd x mode f)))
	     (and (< r (spn f)) (< d (spn f)))))
  :hints (("Goal" :use (rd-9 rd-10
                        (:instance rtz-upper-bound (x m) (n (prec f)))
                        (:instance rtz-upper-bound (x m) (n (1- (prec f)))))
	          :in-theory (enable rnd rdn))))

(defthmd rd-b-1
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup))
		(<= m (- 1 (expt 2 (- (prec f))))))
	   (< (rnd m mode (prec f)) 1))
  :hints (("Goal" :in-theory (enable rnd rup)
                  :use (rd-1
		        (:instance raz-upper-bound (x m) (n (prec f)))))))

(defthmd rd-b-2
  (implies (formatp f)
           (and (equal (expo (- 1 (expt 2 (- (prec f))))) -1)
                (exactp (- 1 (expt 2 (- (prec f)))) (prec f))))
  :hints (("Goal" :in-theory (enable exactp2)
                  :use (rd-1
		        (:instance expo<= (x (- 1 (expt 2 (- (prec f))))) (n -1))
			(:instance expo>= (x (- 1 (expt 2 (- (prec f))))) (n -1))))))

(defthmd rd-b-3
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup))
		(> m (- 1 (expt 2 (- (prec f))))))
	   (and (exactp (rnd m mode (prec f)) (prec f))
	        (> (rnd m mode (prec f)) (- 1 (expt 2 (- (prec f)))))))
  :hints (("Goal" :in-theory (enable rnd rup)
                  :use (rd-1
		        (:instance raz-lower-pos (x m) (n (prec f)))))))

(defthmd rd-b-4
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup))
		(> m (- 1 (expt 2 (- (prec f))))))
	   (>= (rnd m mode (prec f)) 1))
  :hints (("Goal" :in-theory (enable rnd rup)
                  :use (rd-1 rd-b-2 rd-b-3
		        (:instance fp+2 (y (rnd m mode (prec f))) (x (- 1 (expt 2 (- (prec f))))) (n (prec f)))))))

(defthmd rd-b-5
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup))
		(<= m (- 1 (expt 2 (- 1 (prec f))))))
	   (< (rnd m mode (1- (prec f))) 1))
  :hints (("Goal" :in-theory (enable rnd rup)
                  :use (rd-1
		        (:instance raz-upper-bound (x m) (n (1- (prec f))))))))

(defthmd rd-b-6
  (implies (formatp f)
           (and (equal (expo (- 1 (expt 2 (- 1 (prec f))))) -1)
                (exactp (- 1 (expt 2 (- 1 (prec f)))) (1- (prec f)))))
  :hints (("Goal" :in-theory (enable exactp2)
                  :use (rd-1
		        (:instance expo<= (x (- 1 (expt 2 (- 1 (prec f))))) (n -1))
			(:instance expo>= (x (- 1 (expt 2 (- 1 (prec f))))) (n -1))))))

(defthmd rd-b-7
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup))
		(> m (- 1 (expt 2 (- 1 (prec f))))))
	   (and (exactp (rnd m mode (1- (prec f))) (1- (prec f)))
	        (> (rnd m mode (1- (prec f))) (- 1 (expt 2 (- 1 (prec f)))))))
  :hints (("Goal" :in-theory (enable rnd rup)
                  :use (rd-1
		        (:instance raz-lower-pos (x m) (n (1- (prec f))))))))

(defthmd rd-b-8
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup))
		(> m (- 1 (expt 2 (- 1 (prec f))))))
	   (>= (rnd m mode (1- (prec f))) 1))
  :hints (("Goal" :in-theory (enable rnd rup)
                  :use (rd-1 rd-b-6 rd-b-7
		        (:instance fp+2 (y (rnd m mode (1- (prec f)))) (x (- 1 (expt 2 (- 1 (prec f))))) (n (1- (prec f))))))))

(defthmd rd-b
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(raz rup)))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p))
		  (d (drnd x mode f)))
	       (and (iff (< r (spn f)) (<= m (- 1 (expt 2 (- p)))))
	            (iff (< d (spn f)) (<= m (- 1 (expt 2 (- 1 p))))))))
  :hints (("Goal" :use (rd-9 rd-10 rd-b-1 rd-b-4 rd-b-5 rd-b-8)
                  :in-theory (enable common-mode-p ieee-rounding-mode-p))))

(defthmd rd-c-1
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(rne rna))
		(< m (- 1 (expt 2 (- (1+ (prec f)))))))
	   (< (rnd m mode (prec f)) 1))
  :hints (("Goal" :in-theory (enable rnd)
                  :use (rd-1
		        (:instance rne-diff (x m) (n (prec f)))
		        (:instance rna-diff (x m) (n (prec f)))))))

(defthmd rd-c-2
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(rne rna))
		(>= m (- 1 (expt 2 (- (1+ (prec f)))))))
	   (equal (rnd m mode (prec f)) 1))
  :hints (("Goal" :in-theory (enable rnd)
                  :use (rd-1
		        (:instance rne-power-2 (x m) (n (prec f)))
		        (:instance rna-power-2 (x m) (n (prec f)))))))

(defthmd rd-c-3
  (implies (and (formatp f)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(rne rna))
		(< m (- 1 (expt 2 (- (prec f))))))
	   (< (rnd m mode (1- (prec f))) 1))
  :hints (("Goal" :in-theory (enable rnd)
                  :use (rd-1
		        (:instance rne-diff (x m) (n (1- (prec f))))
		        (:instance rna-diff (x m) (n (1- (prec f))))))))

(defthmd rd-c-4
  (implies (and (formatp f)
                (> (prec f) 2)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(rne rna))
		(>= m (- 1 (expt 2 (- (prec f))))))
	   (equal (rnd m mode (1- (prec f))) 1))
  :hints (("Goal" :in-theory (enable rnd)
                  :use (rd-1
		        (:instance rne-power-2 (x m) (n (1- (prec f))))
		        (:instance rna-power-2 (x m) (n (1- (prec f))))))))

(defthmd rd-c
  (implies (and (formatp f)
                (> (prec f) 2)
		(rationalp m)
		(>= m 1/2)
		(< m 1)
		(member mode '(rne rna)))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p))
		  (d (drnd x mode f)))
	       (and (iff (< r (spn f)) (< m (- 1 (expt 2 (- (1+ p))))))
	            (iff (< d (spn f)) (< m (- 1 (expt 2 (- p))))))))
  :hints (("Goal" :use (rd-9 rd-10 rd-c-1 rd-c-2 rd-c-3 rd-c-4))))

(defthmd rnd-drnd
  (implies (and (formatp f)
                (> (prec f) 2)
		(rationalp m)
		(< 0 m)
		(< m 1)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p))
		  (d (drnd x mode f)))
	     (case mode
	       ((rdn rtz) (and (< r (spn f)) (< d (spn f))))
	       ((rup raz) (and (iff (< r (spn f)) (<= m (- 1 (expt 2 (- p)))))
	                       (iff (< d (spn f)) (<= m (- 1 (expt 2 (- 1 p)))))))
	       ((rne rna) (and (iff (< r (spn f)) (< m (- 1 (expt 2 (- (1+ p))))))
	                       (iff (< d (spn f)) (< m (- 1 (expt 2 (- p))))))))))
  :hints (("Goal" :use (rd-5 rd-a rd-b rd-c)  
                  :in-theory (enable common-mode-p ieee-rounding-mode-p))))
