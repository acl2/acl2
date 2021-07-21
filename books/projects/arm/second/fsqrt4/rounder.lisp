(in-package "RTL")

(include-book "quotient")

(local-defund lsb () (bitn (qtrunc) 1))

(local-defund grd () (bitn (qtrunc) 0))

(local-defund qrnd* ()
  (if1 (logior1 (logior1 (logand1 (logand1 (log= (rmode) 0) (grd))
                                  (logior1 (lsb) (stk)))
                         (logand1 (logand1 (log= (rmode) 1)
                                           (lognot1 0))
                                  (logior1 (grd) (stk))))
                (logand1 (logand1 (log= (rmode) 2) 0)
                         (logior1 (grd) (stk))))
       (bits (qinc) 53 1)
       (bits (qtrunc) 53 1)))


(local-defund inx* () (logior1 (grd) (stk)))

(local (in-theory (disable (lsb) (grd) (qrnd*) (inx*))))

(local-defthmd rounder-lemma
  (and (equal (qrnd) (qrnd*))
       (equal (inx) (inx*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(lsb grd qrnd* inx* qrnd inx rounder))))

(defund mode ()
  (case (rmode)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

(in-theory (disable (mode)))

(local-defund z* () (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))

(local (in-theory (disable (z*))))

(defthmd expo-qsqrt-x
  (implies (not (specialp))
           (equal (expo (qsqrt (x) (+ 1 (* 2 (n)))))
	          -1))
  :hints (("Goal" :in-theory (enable qsqrt-rto-sqrt n)
                  :use (fnum-vals x-bounds))))

(local-defthmd qrnd-1
  (implies (not (specialp))
           (equal (expo (z*)) (p)))
  :hints (("Goal" :in-theory (enable z*)
                  :nonlinearp t
                  :use (p-vals expo-qsqrt-x
		        (:instance expo-shift (n (1+ (p))) (x (qsqrt (x) (1+ (* 2 (n))))))))))

(local-defthmd qrnd-2
  (implies (not (specialp))
           (and (rationalp (z*))
	        (> (z*) 0)))
  :hints (("Goal" :in-theory (enable z* n)
                  :nonlinearp t
                  :use (p-vals x-bounds fnum-vals
		        (:instance qsqrt-pos (x (x)) (n (1+ (* 2 (n)))))))))

(local-defthmd qrnd-3
  (implies (not (specialp))
           (<= (expt 2 (p)) (z*)))
  :hints (("Goal" :use (qrnd-1 qrnd-2 (:instance expo-lower-bound (x (z*)))))))

(defthmd qrnd-4
  (implies (not (specialp))
           (common-mode-p (mode)))
  :hints (("Goal" :in-theory (enable rmode mode common-mode-p)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd qrnd-5
  (implies (not (specialp))
           (equal (bits (fl (z*)) (1- (p)) 0)
	          (bits (qtrunc) (1- (p)) 0)))
  :hints (("Goal" :in-theory (enable bits z*)
                  :use (qtrunc-rewrite))))

(local-defthmd qrnd-6
  (implies (not (specialp))
           (equal (stk)
	          (if (integerp (z*)) 0 1)))
  :hints (("Goal" :in-theory (enable z*)
                  :use (stk-rewrite))))

(local-defthmd qrnd-7
  (implies (not (specialp))
           (equal (expo (fl (z*))) (p)))
  :hints (("Goal" :use (p-vals qrnd-1 qrnd-2
                        (:instance expo-lower-bound (x (z*)))
                        (:instance expo-upper-bound (x (z*)))
                        (:instance expo-unique (x (fl (z*))) (n (p)))))))

(local-defthmd qrnd-8
  (implies (not (specialp))
           (iff (exactp (z*) (p))
	        (and (= (stk) 0)
		     (= (bitn (fl (z*)) 0) 0))))
  :hints (("Goal" :use (p-vals qrnd-2 qrnd-3 qrnd-4 qrnd-6 qrnd-7
                        (:instance roundup-pos-thm (mode (mode)) (z (z*)) (n (p)))))))

(local-defthmd qrnd-9
  (implies (not (specialp))
           (iff (exactp (qsqrt (x) (1+ (* 2 (n)))) (p))
	        (and (= (stk) 0)
		     (= (bitn (fl (z*)) 0) 0))))
  :hints (("Goal" :use (p-vals qrnd-8
                        (:instance exactp-shift (k (1+ (p))) (n (p)) (x (qsqrt (x) (1+ (* 2 (n)))))))
		  :in-theory (enable z*))))

(defthmd inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (exactp (qsqrt (x) (1+ (* 2 (n)))) (p))
		      0 1)))
  :hints (("Goal" :use (p-vals qrnd-5 qrnd-9
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 0))
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 0)))
		  :in-theory (enable rounder-lemma inx* grd))))

(local-defthmd qrnd-10
  (implies (not (specialp))
           (equal (rnd (z*) (mode) (p))
	          (if (roundup-pos (fl (z*)) (p) (stk) (mode) (p))
		      (fp+ (rtz (fl (z*)) (p)) (p))
		    (rtz (fl (z*)) (p)))))
  :hints (("Goal" :use (p-vals qrnd-2 qrnd-3 qrnd-4 qrnd-6 qrnd-7
                        (:instance roundup-pos-thm (mode (mode)) (z (z*)) (n (p)))))))

(in-theory (disable sgn-ddecode))

(local-defthmd qrnd-11
  (implies (not (specialp))
           (equal (qrnd)
	          (if (roundup-pos (fl (z*)) (p) (stk) (mode) (p))
		      (bits (qinc) 53 1)
		    (bits (qtrunc) 53 1))))
  :hints (("Goal" :in-theory (enable stk-rewrite roundup-pos qrnd* rounder-lemma lsb grd mode
                                     mode rmode)
                  :use (qrnd-5 p-vals
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 0))
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 0))
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 1))
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 1))))))

(local-defthmd qrnd-12
  (implies (and (not (specialp)) (eql (p) k))
           (equal (rtz (fl (z*)) k)
	          (* 2 (bits (fl (z*)) (p) 1))))
  :hints (("Goal" :use (qrnd-2 qrnd-7 (:instance bits-rtz (x (fl (z*))) (n (1+ (p))) (k (p)))))))

(local-defthmd qrnd-13
  (implies (not (specialp))
           (equal (mod (rtz (fl (z*)) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (fl (z*)) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :in-theory (e/d (qrnd-12) (ACL2::|(equal (mod a n) (mod b n))|))
                  :use (p-vals
		        (:instance mod-mult (m (* 2 (bits (fl (z*)) (1- (p)) 1))) (a (bitn (fl (z*)) (p))) (n (expt 2 (p))))
		        (:instance bitn-plus-bits (x (fl (z*))) (n (p)) (m 1))))))

(local-defthmd qrnd-14
  (implies (not (specialp))
           (equal (mod (rtz (fl (z*)) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qtrunc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-13 qrnd-5 p-vals
                        (:instance bits-bits (x (fl (z*))) (i (1- (p))) (j 0) (k (1- (p))) (l 1))
                        (:instance bits-bits (x (qtrunc)) (i (1- (p))) (j 0) (k (1- (p))) (l 1))))))

(local-defthmd qrnd-15
  (implies (and (not (specialp))
                (not (roundup-pos (fl (z*)) (p) (stk) (mode) (p))))
           (equal (mod (rnd (z*) (mode) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qtrunc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-14 qrnd-10))))

(local-defthmd qrnd-16
  (implies (and (not (specialp))
                (not (roundup-pos (fl (z*)) (p) (stk) (mode) (p))))
           (equal (mod (rnd (z*) (mode) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-15 qrnd-11 p-vals
                        (:instance bits-bits (x (qtrunc)) (i 53) (j 1) (k (- (p) 2)) (l 0))))))

(local-defthmd qrnd-17
  (implies (not (specialp))
           (equal (fp+ (rtz (fl (z*)) (p)) (p))
	          (+ (rtz (fl (z*)) (p)) 2)))
  :hints (("Goal" :in-theory (enable fp+)
                  :use (p-vals qrnd-7))))

(local-defthmd qrnd-18
  (implies (not (specialp))
           (equal (fp+ (rtz (fl (z*)) (p)) (p))
	          (+ (* 2 (bits (fl (z*)) (p) 1)) 2)))
  :hints (("Goal" :in-theory (enable qrnd-12) :use (qrnd-17 p-vals))))

(local-defthmd qrnd-19
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (bits (fl (z*)) (p) 0) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals (:instance bits-plus-bitn (x (fl (z*))) (n (p)) (m 0))))))

(local-defthmd qrnd-20
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (bits (fl (z*)) (1- (p)) 0) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-19
                        (:instance bitn-plus-bits (x (fl (z*))) (n (p)) (m 0))
			(:instance mod-mult (m (+ (- (bits (fl (z*)) (1- (p)) 0) (bitn (fl (z*)) 0)) 2))
			                    (a (bitn (fl (z*)) (p)))
					    (n (expt 2 (p))))))))

(local-defthmd qrnd-21
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (mod (fl (z*)) (expt 2 (p))) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-20) :in-theory (enable bits))))

(local-defthmd qrnd-22
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (fl (z*)) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-21
                        (:instance mod-sum (a (- 2 (bitn (fl (z*)) 0))) (b (fl (z*))) (n (expt 2 (p))))))))

(local-defthmd qrnd-23
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (mod (+ (fl (z*)) 2) (expt 2 (p))) (bitn (fl (z*)) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-22
                        (:instance mod-sum (a (- (bitn (fl (z*)) 0))) (b (+ 2 (fl (z*)))) (n (expt 2 (p))))))))

(local-defthm qrnd-24
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (or (= (stk) 1)
	       (= (bitn (qtrunc) 0) 1)))
  :rule-classes ()
  :hints (("Goal" :use (p-vals qrnd-5
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 0)) 
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 0)))
		  :in-theory (enable roundup-pos))))

(local-defthmd qrnd-26
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (+ (fl (z*)) 2) (expt 2 (p)))
	          (mod (qinc) (expt 2 (p)))))
  :hints (("Goal" :in-theory (enable z*) :use (p-vals qinc-rewrite))))

(local-defthmd qrnd-27
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (mod (qinc) (expt 2 (p))) (bitn (fl (z*)) 0)) (expt 2 (p)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (qrnd-23 qrnd-26))))

(local-defthm qrnd-28
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (and (integerp (p))
	        (integerp 0)
		(< 0 (p))))
  :rule-classes ()
  :hints (("Goal" :use (p-vals))))

(local-defthmd qrnd-29
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (bitn (qinc) 0)
                  (bitn (+ (fl (z*)) 2) 0)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (qrnd-26 qrnd-28 p-vals
		        (:instance bitn-mod (x (qinc)) (n (p)) (k 0))
			(:instance bitn-mod (x (+ (fl (z*)) 2)) (n (p)) (k 0))))))

(local-defthmd qrnd-30
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (bitn (qinc) 0)
                  (bitn (fl (z*)) 0)))
  :hints (("Goal" :use (qrnd-29
		        (:instance bitn-plus-mult (x (fl (z*))) (m 1) (k 1) (n 0))))))

(local-defthmd qrnd-31
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (mod (qinc) (expt 2 (p))) (bitn (qinc) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-27 qrnd-30 p-vals))))

(local-defthmd qrnd-32
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (bits (qinc) (1- (p)) 0) (bitn (qinc) 0)) (expt 2 (p)))))
  :hints (("Goal" :in-theory (enable bits) :use (qrnd-31 p-vals))))

(local-defthmd qrnd-33
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (* 2 (bits (qinc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-32 p-vals (:instance bits-plus-bitn (x (qinc)) (n (1- (p))) (m 0))))))

(local-defthmd qrnd-34
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (rnd (z*) (mode) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qinc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-10 qrnd-18 qrnd-33))))

(local-defthmd qrnd-35
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (mode) (p)))
           (equal (mod (rnd (z*) (mode) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-34 qrnd-11 p-vals
                        (:instance bits-bits (x (qinc)) (i 53) (j 1) (k (- (p) 2)) (l 0))))))

(local-defthmd qrnd-36
  (implies (not (specialp))
           (equal (mod (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-35 qrnd-16 p-vals)
                  :in-theory '(z*))))

(defthmd rnd-qsqrt-qrnd
  (implies (not (specialp))
           (equal (mod (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)) (expt 2 (p)))
	          (* 2 (bits (qrnd) (- (p) 2) 0))))
  :hints (("Goal" :use (qrnd-36 p-vals (:instance bits-bounds (x (qrnd)) (i (- (p) 2)) (j 0))))))

(local-defthmd rnd-1-1
  (implies (and (not (specialp))
                (not (= (mode) 'rup)))
	   (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
  	           1)))
  :hints (("Goal" :use (p-vals qsqrt-x-upper expo-qsqrt-x qrnd-4
                        (:instance rtz-upper-pos (x (qsqrt (x) (1+ (* 2 (n))))) (n (p)))
                        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
			(:instance rne-diff (x (qsqrt (x) (1+ (* 2 (n))))) (n (p))))
		  :in-theory (enable rmode mode rdn rnd))))

(local-defthmd rnd-1-2
  (implies (and (not (specialp))
                (= (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (> (qsqrt (x) (1+ (* 2 (n))))
	      (- 1 (expt 2 (- (p))))))
  :hints (("Goal" :use (fnum-vals quotf-error-b)
		  :in-theory (enable n p f dp sp hp prec))))

(local-defthmd rnd-1-3
  (implies (and (not (specialp))
                (= (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (equal (rup (qsqrt (x) (1+ (* 2 (n)))) (p))
	          1))
  :hints (("Goal" :use (p-vals rnd-1-2 expo-qsqrt-x x-bounds fnum-vals qsqrt-x-upper
                        (:instance qsqrt-pos (x (x)) (n (1+ (* 2 (n)))))
			(:instance raz-squeeze (a (- 1 (expt 2 (- (p))))) (x (qsqrt (x) (1+ (* 2 (n))))) (n (p)))
                        (:instance raz-expo-upper (x (qsqrt (x) (1+ (* 2 (n))))) (n (p))))
		  :in-theory (enable rup n))))

(local-defthmd rnd-1-4
  (implies (and (not (specialp))
                (< (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (< (* (expt 2 (* 2 (n))) (quotf))
	      (* (expt 2 (* 2 (n))) (- 1 (expt 2 (- (1+ (p))))))))
  :hints (("Goal" :use (fnum-vals)
                  :nonlinearp t
		  :in-theory (enable n p f dp sp hp prec))))

(local-defthmd rnd-1-5
  (implies (and (not (specialp))
                (< (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (<= (* (expt 2 (* 2 (n))) (quotf))
	       (1- (* (expt 2 (* 2 (n))) (- 1 (expt 2 (- (1+ (p)))))))))
  :hints (("Goal" :use (fnum-vals rnd-1-4
                        (:instance int-quot (j (n))))
		  :in-theory (enable quotf n p f dp sp hp prec))))

(defthmd rnd-1-6
  (implies (and (not (specialp))
                (< (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (<= (quotf)
	       (- (- 1 (expt 2 (- (1+ (p)))))
	          (expt 2 (- (* 2 (n)))))))
  :hints (("Goal" :use (fnum-vals rnd-1-5)
                  :nonlinearp t
		  :in-theory (enable quotf n p f dp sp hp prec))))

(local-defthmd quotf-bounds
  (implies (not (specialp))
           (and (<= (quotf) 1)
                (>= (quotf) 1/2)))
  :hints (("Goal" :in-theory (enable quotf n inv quot-bnds-inv)
                  :use ((:instance inv-lemma (j (n)))))))

(local-defthmd rnd-1-7
  (implies (and (not (specialp))
                (< (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (and (< 0 (+ (quotf) (* 2/3 (expt 4 (- (n))))))
	        (<= (+ (quotf) (* 2/3 (expt 4 (- (n)))))
		    (- 1 (+ (expt 2 (- (1+ (p)))) (* 1/3 (expt 2 (- (* 2 (n))))))))
		(rationalp (+ (quotf) (* 2/3 (expt 4 (- (n))))))
		(rationalp (- 1 (+ (expt 2 (- (1+ (p)))) (* 1/3 (expt 2 (- (* 2 (n))))))))
		(rationalp (x))
		(<= (x) (expt (+ (quotf) (* 2/3 (expt 4 (- (n))))) 2))))
  :hints (("Goal" :use (fnum-vals rnd-1-6 quotf-error-a quotf-bounds)
		  :in-theory (e/d  (expt n p f dp sp hp prec)))))

(local-defthmd rnd-1-8
  (implies (and (rationalp x) (rationalp a) (rationalp b)
                (< 0 a)
		(<= a b)
		(<= x (expt a 2)))
	   (<= x (expt b 2)))
  :hints (("Goal" :in-theory (enable expt) :nonlinearp t)))

(local-defthmd rnd-1-9
  (implies (and (not (specialp)) (>= (quotf) 1/2)
                (< (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (<= (x)
	       (expt (- 1 (+ (expt 2 (- (1+ (p)))) (* 1/3 (expt 2 (- (* 2 (n))))))) 2)))
  :hints (("Goal" :use (rnd-1-7
                        (:instance rnd-1-8 (a (+ (quotf) (* 2/3 (expt 4 (- (n))))))
			                   (b (- 1 (+ (expt 2 (- (1+ (p)))) (* 1/3 (expt 2 (- (* 2 (n))))))))
					   (x (x)))))))

(local-defthmd rnd-1-10
  (implies (and (not (specialp))
                (< (quotf) (- 1 (expt 2 (- (1+ (p)))))))
	   (< (x) (- 1 (expt 2 (- (p))))))
  :hints (("Goal" :use (fnum-vals rnd-1-9)
                  :in-theory (enable n p f dp sp hp prec))))

(local-defthmd rnd-1-11
  (implies (and (not (specialp))
                (< (x) (- 1 (expt 2 (- (p))))))
	   (< (x) (* (- 1 (expt 2 (- (p)))) (- 1 (expt 2 (- (p)))))))
  :hints (("Goal" :use (p-vals rnd-1-10 exactp-x
                        (:instance fp-2 (x (- 1 (expt 2 (- (p))))) (y (x)) (n (p)))))))

(local-defthmd rnd-1-12
  (implies (and (not (specialp))
                (< (x) (- 1 (expt 2 (- (p))))))
	   (< (qsqrt (x) (1+ (* 2 (n))))
	      (- 1 (expt 2 (- (p))))))
  :hints (("Goal" :use (fnum-vals rnd-1-11
                        (:instance exactp-cmp-qsqrt (q (- 1 (expt 2 (- (p))))) (x (x)) (n (1+ (* 2 (n))))))
                  :in-theory (enable p prec n f sp dp hp))))

(local-defthmd rnd-1-13
  (implies (and (not (specialp))
                (< (x) (- 1 (expt 2 (- (p))))))
	   (< (rup (qsqrt (x) (1+ (* 2 (n)))) (p))
	      1))
  :hints (("Goal" :use (fnum-vals rnd-1-12
                        (:instance qsqrt-pos (x (x)) (n (1+ (* 2 (n)))))
			(:instance raz-monotone (x (qsqrt (x) (1+ (* 2 (n))))) (y (- 1 (expt 2 (- (p))))) (n (p))))
		  :in-theory (enable rup n p f dp sp hp prec))))

(defthmd rnd-1-rup-qmax
  (implies (not (specialp))
           (iff (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	               1)
	        (and (equal (mode) 'rup)
	             (equal (quotf) (- 1 (expt 2 (- (1+ (p)))))))))
  :hints (("Goal" :use (rnd-1-1 rnd-1-3 rnd-1-10 rnd-1-13 quotf-upper)
		  :in-theory (enable rnd))))

(defthmd rnd-1-rup-xmax
  (implies (not (specialp))
           (iff (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	               1)
	        (and (equal (mode) 'rup)
                     (equal (x) (- 1 (expt 2 (- (p))))))))
  :hints (("Goal" :use (fnum-vals rnd-1-1 rnd-1-10 rnd-1-13 quotf-upper rnd-1-rup-qmax x-bounds exactp-x
                        (:instance qsqrt-pos (x (x)) (n (1+ (* 2 (n)))))
                        (:instance fp-2 (x 1) (y (x)) (n (p))))
		  :in-theory (enable rnd rup n p f dp sp hp prec))))

(local-defthmd rup-expinc-1
  (implies (not (specialp))
           (equal (expinc-1)
	          (if (and (= (mode) 'rup)
		           (= (classa) 4)
			   (= (q 1) 0))
		      1 0)))
  :hints (("Goal" :in-theory (enable expinc-0 expinc-1 q q-1 firstiter rmode mode)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defun allq0 (j)
  (if (zp j)
      t
    (and (= (q j) 0)
         (allq0 (1- j)))))

(local (in-theory (disable (allq0))))

(local-defthmd rup-expinc-2
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n)))
           (equal (expinc j)
	          (if (and (= (mode) 'rup)
		           (= (classa) 4)
			   (allq0 j))
		      1 0)))
  :hints (("Goal" :in-theory (enable expinc))
          ("Subgoal *1/1" :in-theory (enable expinc rup-expinc-1))
          ("Subgoal *1/2" :in-theory (enable expinc rup-expinc-1))))

(local-defthmd rup-expinc-3
  (implies (not (specialp))
           (equal (expinc (n))
	          (if (and (= (mode) 'rup)
		           (= (classa) 4)
			   (allq0 (1- (n)))
			   (= (q (n)) (if (= (fnum) 1) -2 -1)))
		      1 0)))
  :hints (("Goal" :in-theory (enable n expinc)
                  :use (fnum-vals
		        (:instance expinc (j (n)))
		        (:instance rup-expinc-2 (j (1- (n))))))))

(local-defthmd rup-expinc-4
  (implies (and (not (specialp))
                (natp j)
		(allq0 j))
	   (equal (quot j) 1))	   
  :hints (("Subgoal *1/5" :expand ((quot j)))
          ("Subgoal *1/1" :expand ((quot 0)))))

(local-defthmd rup-expinc-5
  (implies (and (not (specialp))
                (= (expinc (n)) 1))
	   (and (equal (mode) 'rup)
	        (equal (quotf) (- 1 (expt 2 (- (1+ (p))))))))
  :hints (("Goal" :in-theory (enable quotf n p prec f sp dp hp)
                  :use (fnum-vals rup-expinc-3
		        (:instance rup-expinc-4 (j (1- (n))))
			(:instance quot (j (n)))))))

(local-defthmd rup-expinc-6
  (implies (and (not (specialp))
                (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1))
	   (equal (x) (- 1 (expt 2 (- (p))))))
  :hints (("Goal" :use (p-vals exactp-x x-bounds rnd-1-13 rnd-1-1
                        (:instance fp-2 (y (x)) (x 1) (n (p))))
		  :in-theory (enable rnd))))

(local-defthmd rup-expinc-7
  (implies (and (not (specialp))
		(natp j)
		(allq0 j)
		(not (zp k))
		(<= k j))
	   (equal (q k) 0)))

(local-defthmd rup-expinc-8
  (implies (and (not (specialp))
		(natp j)
		(allq0 j))
	   (equal (i j) 8))
  :hints (("Goal" :in-theory (enable i i-1 firstiter q q-1)
                  :use ((:instance rup-expinc-7 (k 1))
		        (:instance rup-expinc-7 (k 2))))))

(local-defthmd rup-expinc-9
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1)
		(natp j)
		(allq0 j))
	   (equal (r j) (- (expt 2 (- (* 2 j) (p))))))
  :hints (("Goal" :in-theory (enable rup-expinc-4 rup-expinc-6 r)
                  :use (p-vals))))

(local-defthmd rup-expinc-10
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1)
		(natp j)
		(< j (1- (n)))
		(allq0 j))
	   (>= (* 4 (r j)) (ms4 (i j) j 0)))
  :hints (("Goal" :in-theory (enable ms4 n p prec dp sp hp f rup-expinc-8 rup-expinc-9)
                  :nonlinearp t
                  :use (fnum-vals))))

(local-defthmd rup-expinc-11
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1)
		(natp j)
		(< j (1- (n)))
		(allq0 j))
	   (>= (q (1+ j)) 0))
  :hints (("Goal" :in-theory (enable select-digit-s4 ms4 n p prec dp sp hp f inv approx-inv approx-bounds)
                  :use (fnum-vals rup-expinc-10 (:instance inv-lemma (j (1+ j)))))))

(local-defthmd rup-expinc-12
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1)
		(natp j)
		(< j (1- (n)))
		(allq0 j))
	   (allq0 (1+ j)))
  :hints (("Goal" :in-theory (enable inv quot-bnds-inv quot rup-expinc-4 n p prec dp sp hp f)
                  :use (fnum-vals rup-expinc-11
		        (:instance inv-lemma (j (1+ j)))))))

(local-defthmd rup-expinc-13
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1)
		(natp j)
		(< j (n)))
	   (allq0 j))
  :hints (("Goal" :in-theory (enable quot) :induct (quot j))
          ("Subgoal *1/2" :in-theory (enable n)
	                  :use (fnum-vals (:instance rup-expinc-12 (j (1- j)))))))

(local-defthmd rup-expinc-14
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1))
	   (and (= (mode) 'rup)
	        (allq0 (1- (n)))
	        (= (q (n)) (if (= (fnum) 1) -2 -1))))
  :hints (("Goal" :in-theory (enable quotf n quot f dp sp hp p prec)
	          :use (fnum-vals rnd-1-rup-qmax
		        (:instance rup-expinc-4 (j (1- (n))))
		        (:instance rup-expinc-13 (j (1- (n))))))))

(local-defthmd rup-expinc-15
  (implies (and (not (specialp))
	        (not (= (classa) 4)))
	   (equal (expa) 0))
  :hints (("Goal" :in-theory (enable normp denormp)
	          :use (a-class spec-class spec-fields))))

(local-defthmd rup-expinc-16
  (implies (not (specialp))
	   (exactp (mana) (1- (p))))
  :hints (("Goal" :in-theory (enable bvecp p prec sigw f dp sp hp)
                  :use (fnum-vals bvecp-mana
		        (:instance expo<= (x (mana)) (n (- (p) 2)))
			(:instance exactp-<= (m (1+ (expo (mana)))) (n (1- (p))))
                        (:instance exact-bits-1 (x (mana)) (k 0) (n (1+ (expo (mana)))))))))

(local-defthmd rup-expinc-17
  (implies (and (not (specialp))
	        (not (= (classa) 4)))
	   (exactp (siga) (1- (p))))
  :hints (("Goal" :use (p-vals rup-expinc-15 rup-expinc-16 siga-mana
		        (:instance exactp-shift (x (mana)) (k (- 52 (expo (mana)))) (n (1- (p))))))))

(local-defthmd rup-expinc-18
  (implies (and (not (specialp))
	        (not (= (classa) 4)))
	   (exactp (sig (a)) (1- (p))))
  :hints (("Goal" :use (p-vals rup-expinc-17 siga-rewrite
		        (:instance exactp-shift (x (siga)) (k -52) (n (1- (p))))))))

(local-defthmd rup-expinc-19
  (implies (and (not (specialp))
	        (not (= (classa) 4)))
	   (exactp (x) (1- (p))))
  :hints (("Goal" :in-theory (enable x)
                  :use (p-vals rup-expinc-18
		        (:instance exactp-shift (x (sig (a))) (k -1) (n (1- (p))))
		        (:instance exactp-shift (x (sig (a))) (k -2) (n (1- (p))))))))

(local-defthmd rup-expinc-20
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1))
	   (equal (classa) 4))
  :hints (("Goal" :in-theory (enable rup-expinc-6)
	          :use (p-vals rup-expinc-19))))

(local-defthmd rup-expinc-21
  (implies (and (not (specialp))
		(= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	           1))
	   (equal (expinc (n)) 1))
  :hints (("Goal" :in-theory (enable rup-expinc-3)
	          :use (rup-expinc-14 rup-expinc-20))))

(defthmd rup-expinc
  (implies (not (specialp))
           (equal (expinc (n))
	          (if (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	                     1)
	              1 0)))
  :hints (("Goal" :expand ((expinc (n)) (expinc-1) (expinc 1) (expinc 0))
                  :use (rnd-1-rup-qmax rup-expinc-5 rup-expinc-21)))) 
		  
(defthmd rnd-inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (= (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
		         (qsqrt (a) (1+ (* 2 (n)))))
		      0 1)))
  :hints (("Goal" :use (qrnd-4 sqrt-a-x p-vals
                        (:instance exactp-shift (k (1+ (- (expq) (bias (f))))) (x (qsqrt (x) (1+ (* 2 (n))))) (n (p)))
                        (:instance rnd-exactp-b (x (qsqrt (a) (1+ (* 2 (n))))) (mode (mode)) (n (p))))
		  :in-theory (enable inx-rewrite))))

(local-defthmd rnd-qsqrt-a-1
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
	   (equal (expo (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)))
	          -1))
  :hints (("Goal" :use (qrnd-4 expo-qsqrt-x p-vals
                        (:instance expo-rnd (x (qsqrt (x) (1+ (* 2 (n))))) (mode (mode)) (n (p)))))))

(local-defthmd rnd-qsqrt-a-2
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (equal (expo (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)))
	          (p)))
  :hints (("Goal" :use (qrnd-4 p-vals rnd-qsqrt-a-1
                        (:instance expo-shift (x (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))) (n (1+ (p))))
			(:instance rnd-shift (x (qsqrt (x) (1+ (* 2 (n))))) (k (1+ (p))) (n (p)) (mode (mode)))))))

(local-defthmd rnd-qsqrt-a-2
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (equal (expo (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)))
	          (p)))
  :hints (("Goal" :use (qrnd-4 p-vals rnd-qsqrt-a-1
                        (:instance expo-shift (x (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))) (n (1+ (p))))
			(:instance rnd-shift (x (qsqrt (x) (1+ (* 2 (n))))) (k (1+ (p))) (n (p)) (mode (mode)))))))

(local-defthmd rnd-qsqrt-a-3
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (> (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)) 0))
  :hints (("Goal" :use (qrnd-4 x-bounds p-vals
                        (:instance qsqrt-pos (x (x)) (n (1+ (* 2 (n)))))
			(:instance rnd-positive (x (qsqrt (x) (1+ (* 2 (n))))) (mode (mode)) (n (p)))))))

(local-defthmd rnd-qsqrt-a-4
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (and (>= (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p))
	            (expt 2 (p)))
		(< (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p))
		   (expt 2 (1+ (p))))))
  :hints (("Goal" :use (rnd-qsqrt-a-2 rnd-qsqrt-a-3 p-vals
                        (:instance expo-upper-bound (x (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p))))
                        (:instance expo-lower-bound (x (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p))))))))

(local-defthmd rnd-qsqrt-a-5
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (equal (fl (/ (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p))
	                 (expt 2 (p))))
	          1))
  :hints (("Goal" :use (rnd-qsqrt-a-4 p-vals) :nonlinearp t)))

(local-defthmd rnd-qsqrt-a-6
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (equal (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p))
	          (+ (expt 2 (p)) (* 2 (bits (qrnd) (- (p) 2) 0)))))
  :hints (("Goal" :use (rnd-qsqrt-a-5 rnd-qsqrt-qrnd p-vals
                        (:instance mod-def (x (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)))
			                   (y (expt 2 (p))))))))

(defthmd exprnd-rewrite
  (implies (not (specialp))
           (equal (exprnd)
	          (if (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	                     1)
		      (1+ (expq))
		    (expq))))
  :hints (("Goal" :use (expq-bounds fnum-vals)
                  :in-theory (enable dp sp hp f prec p expw bvecp exprnd rup-expinc))))

(local-defthmd rnd-qsqrt-a-8
  (implies (and (not (specialp))
                (not (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1)))
           (equal (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	          (* (expt 2 (- (exprnd) (+ (bias (f)) (1- (p)))))
		     (+ (expt 2 (1- (p))) (bits (qrnd) (- (p) 2) 0)))))
  :hints (("Goal" :use (rnd-qsqrt-a-6 qrnd-4 fnum-vals sqrt-a-x
                        (:instance rnd-shift (x (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) (mode (mode)) (n (p))
			                     (k (- (exprnd) (+ (bias (f)) (p))))))
                  :in-theory (enable bias n dp sp hp f prec p expw exprnd-rewrite))))

(local-defthmd rnd-qsqrt-a-9
  (implies (and (not (specialp))
                (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1))
           (equal (bits (qrnd) (- (p) 2) 0) 0))
  :hints (("Goal" :use (rnd-qsqrt-qrnd qrnd-4 fnum-vals
                        (:instance rnd-shift (x (qsqrt (x) (1+ (* 2 (n))))) (mode (mode)) (n (p))
			                     (k (1+ (p)))))
                  :in-theory (enable bias n dp sp hp f prec p expw exprnd-rewrite))))

(local-defthmd rnd-qsqrt-a-10
  (implies (and (not (specialp))
                (= (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p)) 1))
           (equal (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	          (* (expt 2 (- (exprnd) (+ (bias (f)) (1- (p)))))
		     (+ (expt 2 (1- (p))) (bits (qrnd) (- (p) 2) 0)))))
  :hints (("Goal" :use (sqrt-a-x qrnd-4 fnum-vals rnd-qsqrt-a-9
                        (:instance rnd-shift (x (qsqrt (x) (1+ (* 2 (n))))) (mode (mode)) (n (p))
			                     (k (- (exprnd) (bias (f))))))
                  :in-theory (enable bias n dp sp hp f prec p expw exprnd-rewrite))))

(defthmd rnd-qsqrt-a
  (implies (not (specialp))
           (equal (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	          (* (expt 2 (- (exprnd) (+ (bias (f)) (1- (p)))))
		     (+ (expt 2 (1- (p))) (bits (qrnd) (- (p) 2) 0)))))
  :hints (("Goal" :use (rnd-qsqrt-a-8 rnd-qsqrt-a-10))))
