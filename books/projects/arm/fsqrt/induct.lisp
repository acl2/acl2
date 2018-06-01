(in-package "RTL")

(include-book "algorithm")

(local-defund mp2 (j)
  (case (i j)
    (0 (bits 12 6 0))
    (1 (bits (if1 (log= j 2) 15 13) 6 0))
    (2 (bits 15 6 0))
    (3 (bits 16 6 0))
    (4 (bits 18 6 0))
    (5 (bits 20 6 0))
    (6 (bits 20 6 0))
    (7 (bits 22 6 0))
    (8 (bits 24 6 0))
    (t 0)))

(local-defund mp1 (j)
  (case (i j)
    (0 (bits 4 6 0))
    (1 (bits 4 6 0))
    (2 (bits 4 6 0))
    (3 (bits 6 6 0))
    (4 (bits 6 6 0))
    (5 (bits 8 6 0))
    (6 (bits 8 6 0))
    (7 (bits 8 6 0))
    (8 (bits 8 6 0))
    (t 0)))

(local-defund mz0 (j)
  (case (i j)
    (0 (bits -4 6 0))
    (1 (bits -4 6 0))
    (2 (bits -4 6 0))
    (3 (bits -6 6 0))
    (4 (bits -6 6 0))
    (5 (bits -6 6 0))
    (6 (bits -8 6 0))
    (7 (bits -8 6 0))
    (8 (bits -8 6 0))
    (t 0)))

(local-defund mn1 (j)
  (case (i j)
    (0 (bits (if1 (log= j 1) -11 -12) 6 0))
    (1 (bits -13 6 0))
    (2 (bits -15 6 0))
    (3 (bits -16 6 0))
    (4 (bits -18 6 0))
    (5 (bits -20 6 0))
    (6 (bits -20 6 0))
    (7 (bits -22 6 0))
    (8 (bits -24 6 0))
    (t 0)))

(local-defun q* (j)
  (if1 (log>= (si (rs7 (1- j)) 7) (si (mp2 (1- j)) 7))
       2
     (if1 (log>= (si (rs7 (1- j)) 7) (si (mp1 (1- j)) 7))
          1
        (if1 (log>= (si (rs7 (1- j)) 7) (si (mz0 (1- j)) 7))
             0
           (if1 (log>= (si (rs7 (1- j)) 7) (si (mn1 (1- j)) 7))
                -1
	      -2)))))

(local-in-theory (disable (rp4) (rn4) (rs8) (rs7) (mp2) (mp1) (mz0) (mn1)))

(local-defthmd nextdigit-lemma
  (implies (and (not (zp j)) (not (= j 1)))
           (equal (q j) (q* j)))
  :hints (("goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(nextdigit q q* rp4 rn4 rs8 rs7 mp2 mp1 mz0 mn1))))

(defund qpn-inv (j)
  (and (= (* (expt 2 54) (1- (quot j)))
          (- (qp j) (qn j)))
       (= (bits (qp j) (- 53 (* 2 j)) 0) 0)
       (= (bits (qn j) (- 53 (* 2 j)) 0) 0)))

(defund rpn-inv (j)
  (and (integerp (* (expt 2 55) (r j)))
       (= (mod (* (expt 2 55) (r j)) (expt 2 59))
          (mod (- (rp j) (rn j)) (expt 2 59)))
       (= (bits (rp j) (- 52 (p)) 0) 0)
       (= (bits (rn j) (- 52 (p)) 0) 0)))

(defund inv (j)
  (and (r-bnds-inv j)
       (quot-bnds-inv j)
       (or (zp j)
           (and (approx-inv (1- j))
               (qpn-inv j)
               (rpn-inv j)))))

(defund hyp (j)
  (if (zp j)
      (inv 0)
    (and (inv j)
         (hyp (1- j)))))

(in-theory (disable (approx) (approx-bounds) (approx-inv) (r-bnds-inv) (quot-bnds-inv) (qpn-inv) (rpn-inv) (inv) (hyp)))

(defthmd hyp-0
  (implies (and (not (specialp))
                (zp j))
	   (hyp j))
  :hints (("Goal" :in-theory (enable hyp inv r-bnds-inv quot-bnds-inv quot)
                  :use (r0-bounds))))

(local-defthmd hyp-inv
  (implies (and (natp j)
                (natp k)
		(<= k j)
		(hyp j))
	   (inv k))
  :hints (("Goal" :in-theory (enable hyp) :induct (hyp j))))

(in-theory (disable (srt-hyp) (srt-inv) (hyp) (inv)))

(defthmd hyp-srt-hyp
  (implies (and (natp j)
                (hyp j)
		(approx-inv j))
           (srt-hyp j))
  :hints (("Goal" :in-theory (enable srt-hyp srt-inv hyp inv))))

(local-defthmd r-bnds
  (implies (and (natp j)
		(hyp j)
		(approx-inv j))
           (r-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory (enable hyp-srt-hyp)
                  :use (srt-step))))

(local-defthmd r-bnds
  (implies (and (natp j)
		(hyp j)
		(approx-inv j))
           (r-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory (enable hyp-srt-hyp)
           :use (srt-step))))

(local-defthmd quot-bnds
  (implies (and (natp j)
		(hyp j)
		(approx-inv j))
           (quot-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory (enable hyp-srt-hyp)
                  :use (srt-step))))

(defthmd firstiter-1
  (implies (not (specialp))
           (equal (qp 1) 0))
  :hints (("Goal" :in-theory (enable qp qp-1))))

(defthmd firstiter-2
  (implies (not (specialp))
           (equal (expodd)
	          (if (evenp (si (expshft) 13))
		      0 1)))
  :hints (("Goal" :in-theory (enable expodd si bitn-rec-0))))

(local-defthmd firstiter-3
  (implies (and (not (specialp))
		(= (bitn (siga) 51) 1))
	   (and (< (siga) (expt 2 53))
	        (>= (siga) (+ (expt 2 52) (expt 2 51)))))
  :hints (("Goal" :use (siga-bounds
                        (:instance bitn-0-1 (x (siga)) (n 52))
                        (:instance bitn-0-1 (x (siga)) (n 51))
                        (:instance bitn-plus-bits (x (siga)) (n 52) (m 0))
                        (:instance bitn-plus-bits (x (siga)) (n 51) (m 0))
			(:instance bits-bounds (x (siga)) (i 50) (j 0)))
		  :in-theory (enable bvecp))))

(local-defthmd firstiter-4
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 1))
	   (equal (q 1) -1))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1))))

(local-defthmd firstiter-5
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 1))
	   (and (<= 3/8 (x))
	        (< (x) 1/2)))
  :hints (("Goal" :in-theory (enable firstiter-2 x siga-rewrite)
                  :use (firstiter-3)
                  :nonlinearp t)))

(local-defthmd firstiter-6
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 1))
	   (and (<= (m (i 0) 0 -1) (* 4 (r 0)))
	        (> (m (i 0) 0 0) (* 4 (r 0)))))
  :hints (("Goal" :in-theory (enable m i digtab r0-rewrite)
                  :use (firstiter-5)
                  :nonlinearp t)))

(local-defthmd firstiter-7
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 1))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable  firstiter-2 firstiter-4 approx-inv maxk approx approx-bounds)
                  :use (firstiter-6))))

(local-defthmd firstiter-8
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 1))
	   (equal (q 1) 0))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1))))

(local-defthmd firstiter-9
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 1))
	   (and (<= 3/4 (x))
	        (< (x) 1)))
  :hints (("Goal" :in-theory (enable firstiter-2 x siga-rewrite)
                  :Use (firstiter-3)
                  :nonlinearp t)))

(local-defthmd firstiter-10
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 1))
	   (and (<= (m (i 0) 0 0) (* 4 (r 0)))
	        (> (m (i 0) 0 1) (* 4 (r 0)))))
  :hints (("Goal" :in-theory (enable m i digtab r0-rewrite)
                  :use (firstiter-9)
                  :nonlinearp t)))

(local-defthmd firstiter-11
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 1))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable  firstiter-2 firstiter-8 approx-inv maxk approx approx-bounds)
                  :use (firstiter-10))))

(local-defthmd firstiter-12
  (implies (and (not (specialp))
		(= (bitn (siga) 51) 0))
	   (and (< (siga) (- (expt 2 53) (expt 2 51)))
	        (>= (siga) (expt 2 52))))
  :hints (("Goal" :use (siga-bounds
                        (:instance bitn-0-1 (x (siga)) (n 52))
                        (:instance bitn-0-1 (x (siga)) (n 51))
                        (:instance bitn-plus-bits (x (siga)) (n 52) (m 0))
                        (:instance bitn-plus-bits (x (siga)) (n 51) (m 0))
			(:instance bits-bounds (x (siga)) (i 50) (j 0)))
		  :in-theory (enable bvecp))))

(local-defthmd firstiter-13
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 0))
	   (equal (q 1) -2))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1))))

(local-defthmd firstiter-14
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 0))
	   (and (<= 1/4 (x))
	        (< (x) 3/8)))
  :hints (("Goal" :in-theory (enable firstiter-2 x siga-rewrite)
                  :use (firstiter-12)
                  :nonlinearp t)))

(local-defthmd firstiter-15
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 0))
	   (> (m (i 0) 0 -1) (* 4 (r 0))))
  :hints (("Goal" :in-theory (enable m i digtab r0-rewrite)
                  :use (firstiter-14)
                  :nonlinearp t)))

(local-defthmd firstiter-16
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 0))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable  firstiter-2 firstiter-13 approx-inv maxk approx approx-bounds)
                  :use (firstiter-15))))

(local-defthmd firstiter-17
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 0))
	   (equal (q 1) -1))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1))))

(local-defthmd firstiter-18
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 0))
	   (and (<= 1/2 (x))
	        (< (x) 3/4)))
  :hints (("Goal" :in-theory (enable firstiter-2 x siga-rewrite)
                  :use (firstiter-12)
                  :nonlinearp t)))

(local-defthmd firstiter-19
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 0))
	   (and (<= (m (i 0) 0 -1) (* 4 (r 0)))
	        (> (m (i 0) 0 0) (* 4 (r 0)))))
  :hints (("Goal" :in-theory (enable m i digtab r0-rewrite)
                  :use (firstiter-18)
                  :nonlinearp t)))

(local-defthmd firstiter-20
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 0))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable  firstiter-2 firstiter-17 approx-inv maxk approx approx-bounds)
                  :use (firstiter-19))))

(local-defthmd firstiter-21
  (implies (not (specialp))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable firstiter-2)
                  :use (firstiter-7 firstiter-11 firstiter-16 firstiter-20
		        (:instance bitn-0-1 (x (siga)) (n 51))))))

(local-defthmd firstiter-22
  (implies (not (specialp))
	   (qpn-inv 1))
  :hints (("Goal" :in-theory (enable qpn-inv firstiter firstiter-1 firstiter-2 qn qn-1 quot)
                  :use (firstiter-4 firstiter-8 firstiter-13 firstiter-17
		        (:instance bitn-0-1 (x (siga)) (n 51))))))

(local-defthmd firstiter-23
  (implies (not (specialp))
           (equal (rp 1)
	          (+ (expt 2 59) (* (expt 2 57) (r 0)))))
  :hints (("Goal" :in-theory (enable bvecp rp rp-1 r0-rewrite x cat firstiter firstiter-2)
                  :nonlinearp t
                  :use (siga-bounds siga-rewrite))))

(local-defthmd firstiter-24
  (implies (not (specialp))
           (equal (- (rp 1) (rn 1))
	          (if (>= (q 1) 0)
		      (+ (expt 2 59) (* (expt 2 55) (r 1)))
		    (* (expt 2 55) (r 1)))))
  :hints (("Goal" :in-theory (enable bvecp firstiter firstiter-2 firstiter-23 rn rn-1 quot)
                  :use (firstiter-4 firstiter-8 firstiter-13 firstiter-17
		        (:instance r-recurrence (j 0))))))

(local-defthm integerp-rp-1
  (implies (not (specialp))
           (integerp (rp 1)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable firstiter rp-1 rp))))

(local-defthm integerp-rn-1
  (implies (not (specialp))
           (integerp (rn 1)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable firstiter rn-1 rn))))

(local-defthmd firstiter-25
  (implies (not (specialp))
           (equal (mod (- (rp 1) (rn 1)) (expt 2 59))
	          (mod (* (expt 2 55) (r 1)) (expt 2 59))))
  :hints (("Goal" :use (firstiter-24
		        (:instance mod-mult (m (* (expt 2 55) (r 1))) (a 1) (n (expt 2 59)))))))

(local-defthmd firstiter-26
  (implies (not (specialp))
           (equal (bits (rn 1) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable bvecp firstiter firstiter-2 rn rn-1 quot)
                  :use (p-vals firstiter-4 firstiter-8 firstiter-13 firstiter-17))))

(local-defthmd firstiter-27
  (implies (and (not (specialp))
                (= (expodd) 1))
           (equal (bits (rp 1) (- 52 (p)) 0)
	          (* 8 (bits (siga) (- 49 (p)) 0))))
  :hints (("Goal" :in-theory (enable firstiter rp rp-1)
                  :use (p-vals))
	  ("Subgoal 1" :in-theory (enable cat))
	  ("Subgoal 2" :in-theory (enable cat))))

(local-defthmd firstiter-28
  (implies (not (specialp))
           (equal (bits (siga) (- 49 (p)) 0)
	          0))
  :hints (("Goal" :use (p-vals exactp-siga
                        (:instance bits-plus-mult-2
			           (x 0) (y (* (expt 2 (- (p) 53)) (siga))) (n (- 49 (p))) (k (- 53 (p))) (m 0))))))

(local-defthmd firstiter-29
  (implies (and (not (specialp))
                (= (expodd) 0))
           (equal (bits (rp 1) (- 52 (p)) 0)
	          (* 16 (bits (siga) (- 48 (p)) 0))))
  :hints (("Goal" :in-theory (enable firstiter rp rp-1)
                  :use (p-vals))
	  ("Subgoal 1" :in-theory (enable cat))
	  ("Subgoal 2" :in-theory (enable cat))))

(local-defthmd firstiter-30
  (implies (not (specialp))
           (equal (bits (siga) (- 48 (p)) 0)
	          0))
  :hints (("Goal" :use (p-vals exactp-siga
                        (:instance bits-plus-mult-2
			           (x 0) (y (* (expt 2 (- (p) 53)) (siga))) (n (- 48 (p))) (k (- 53 (p))) (m 0))))))

(local-defthmd firstiter-31
  (implies (not (specialp))
           (equal (bits (rp 1) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable firstiter-2)
                  :use (p-vals firstiter-27 firstiter-28 firstiter-29 firstiter-30))))

(local-defthmd firstiter-32
  (implies (not (specialp))
	   (rpn-inv 1))
  :hints (("Goal" :in-theory (enable rpn-inv)
                  :use (firstiter-24 firstiter-25 firstiter-26 firstiter-31))))

(local-defthmd firstiter-33
  (implies (not (specialp))
	   (quot-bnds-inv 1))
  :hints (("Goal" :in-theory (enable firstiter-2 quot-bnds-inv quot)
                  :use (firstiter-4 firstiter-8 firstiter-13 firstiter-17
		        (:instance bitn-0-1 (x (siga)) (n 51))))))

(local-defthmd firstiter-34
  (implies (not (specialp))
	   (r-bnds-inv 1))
  :hints (("Goal" :use (firstiter-21 (:instance hyp-0 (j 0)) (:instance r-bnds (j 0))))))

(defthmd hyp-1
  (implies (not (specialp))
	   (hyp 1))
  :hints (("Goal" :use (firstiter-21 firstiter-22 firstiter-32 firstiter-33 firstiter-34 (:instance hyp-0 (j 0)))
                  :in-theory (enable hyp inv))))


(local-defthmd approx-inv-1
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (q (+ 1 j))
	          (maxk (approx j) (i j) j)))
  :hints (("Goal" :in-theory (enable q* nextdigit-lemma mn1 mz0 mp1 mp2 maxk approx m digtab))))

(local-defund x* (j)
  (- (rp4 j) (rn4 j)))

(local-defund y* (j)
  (* (expt 2 50)
     (- (bits (rp4 j) 58 50)
        (bits (rn4 j) 58 50))))

(local-defund y** (j)
  (- (bits (rp4 j) 58 50)
     (bits (rn4 j) 58 50)))

(local-in-theory (disable (x*) (y*) (y**)))

(defthmd ash-rewrite
  (equal (ash i c)
         (fl (* (ifix i) (expt 2 c))))
  :hints (("Goal" :in-theory (enable floor fl ash))))

(defthm integerp-rp-j
  (integerp (rp j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :expand ((rp j)) :use (fnum-vals) :in-theory (enable rp-1 firstiter nextrem))))

(defthm integerp-rn-j
  (integerp (rn j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :expand ((rn j)) :use (fnum-vals) :in-theory (enable rn-1 firstiter nextrem))))

(local-defthmd approx-inv-2
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (x* j) (expt 2 59))
	          (mod (* 4 (- (rp j) (rn j))) (expt 2 59))))
  :hints (("Goal" :in-theory (enable ash-rewrite x* rp4 rn4 bits-mod)
                  :use ((:instance mod-sum (a (- (mod (* 4 (rn j)) (expt 2 59)))) (b (* 4 (rp j))) (n (expt 2 59)))
		        (:instance mod-diff (a (* 4 (rp j))) (b (* 4 (rn j))) (n (expt 2 59)))))))

(local-defthmd approx-inv-3
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (* 4 (- (rp j) (rn j))) (expt 2 59))
	          (mod (* (expt 2 57) (r j)) (expt 2 59))))
  :hints (("Goal" :in-theory (enable inv rpn-inv)
                  :use ((:instance mod-mod-times (a (- (rp j) (rn j))) (b 4) (n (expt 2 59)))
		        (:instance mod-mod-times (a (* (expt 2 55) (r j))) (b 4) (n (expt 2 59)))
			(:instance hyp-inv (k j))))))

(local-defthmd approx-inv-4
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (x* j) (expt 2 59))
	          (mod (* (expt 2 57) (r j)) (expt 2 59))))
  :hints (("Goal" :use (approx-inv-2 approx-inv-3))))

(local-defthmd bvecp-rp-j
  (bvecp (rp j) 59)
  :hints (("Goal" :expand ((rp j)) :use (fnum-vals) :in-theory (enable rp-1 firstiter nextrem))))

(local-defthm bvecp-rn-j
  (bvecp (rn j) 59)
  :hints (("Goal" :expand ((rn j)) :use (fnum-vals) :in-theory (enable rn-1 firstiter nextrem))))

(local-defthmd approx-inv-5
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (< (abs (- (x* j) (y* j)))
              (expt 2 50)))
  :hints (("Goal" :in-theory (enable rp4 rn4 x* y* bits-bits bvecp)
                  :use (bvecp-rp-j bvecp-rn-j
		        (:instance bits-plus-bits (x (rp4 j)) (n 58) (p 50) (m 0))
		        (:instance bits-plus-bits (x (rn4 j)) (n 58) (p 50) (m 0))
			(:instance bits-bounds (x (rp4 j)) (i 49) (j 0))
			(:instance bits-bounds (x (rn4 j)) (i 49) (j 0))))))

(local-defthmd approx-inv-6
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (< (abs (* (expt 2 57) (r j)))
              (- (expt 2 58) (expt 2 50))))
  :hints (("Goal" :in-theory (enable hyp inv r-bnds-inv blo bhi quot-bnds-inv)
                  :nonlinearp t)))

(local-defthmd approx-inv-7
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (si (mod (x* j) (expt 2 59)) 59)
	          (* (expt 2 57) (r j))))
  :hints (("Goal" :use (approx-inv-4 approx-inv-6
                        (:instance si-bits (x (* (expt 2 57) (r j))) (n 59)))
		  :in-theory (enable bits-mod))))

(local-defthmd approx-inv-8
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (< (abs (- (* (expt 2 57) (r j))
	              (si (mod (y* j) (expt 2 59)) 59)))
	      (expt 2 50)))
  :hints (("Goal" :use (approx-inv-4 approx-inv-5 approx-inv-6 approx-inv-7
                        (:instance si-approx (x (x* j)) (y (y* j)) (n 59))))))

(local-defthmd approx-inv-9
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (si (mod (y* j) (expt 2 59)) 59)
	          (* (expt 2 50)
		     (si (mod (y** j) (expt 2 9)) 9))))
  :hints (("Goal" :in-theory (enable bvecp y* y**)
                  :use ((:instance mod-prod (k (expt 2 50)) (m (y** j)) (n (expt 2 9)))
		        (:instance si-shift (r (mod (y** j) (expt 2 9))) (k 50) (n 9))))))

(local-defthmd approx-inv-10
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (< (abs (- (* (expt 2 57) (r j))
	              (* (expt 2 50)
		         (si (mod (y** j) (expt 2 9)) 9))))
	      (expt 2 50)))
  :hints (("Goal" :use (approx-inv-8 approx-inv-9))))

(local-defthmd approx-inv-11
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (rs8 j)
	          (mod (fl (/ (y** j) 2)) (expt 2 8))))
  :hints (("Goal" :in-theory (enable bits-mod y** rs8 lognot)
                  :use ((:instance bits-plus-bitn (x (rp4 j)) (n 58) (m 50))
		        (:instance bits-plus-bitn (x (rn4 j)) (n 58) (m 50))
			(:instance bitn-0-1 (x (rp4 j)) (n 50))
			(:instance bitn-0-1 (x (rn4 j)) (n 50))))))

(local-defthmd approx-inv-12
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (rs8 j)
	          (bits (y** j) 8 1)))
  :hints (("Goal" :in-theory (enable approx-inv-11)
                  :use ((:instance bits-mod-fl (x (y** j)) (i 9) (j 1))))))

(local-defthmd approx-inv-13
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (rs7 j)
	          (bits (y** j) 8 2)))
  :hints (("Goal" :in-theory (enable approx-inv-12 rs7))))

(local-defthmd approx-inv-14
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(integerp m))
           (iff (>= (si (rs7 j) 7) m)
	        (>= (si (bits (y** j) 8 0) 9) (* 4 m))))
  :hints (("Goal" :in-theory (enable approx-inv-13 si bitn-bits bits-bits)
                  :use ((:instance bits-plus-bits (x (y** j)) (n 8) (p 2) (m 0))
		        (:instance bits-bounds (x (y** j)) (i 1) (j 0))))))

(local-defthmd approx-inv-15
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(integerp m))
           (iff (>= (si (rs7 j) 7) m)
	        (>= (si (mod (y** j) (expt 2 9)) 9) (* 4 m))))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use (approx-inv-14))))

(local-defthmd approx-inv-16
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2)))
	   (integerp (* 8 (m (i j) j k))))
  :hints (("Goal" :in-theory (enable m digtab))))

(local-defthmd approx-inv-17
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (m (i j) j k)))
	   (< (si (mod (y** j) (expt 2 9)) 9)
	      (* 32 (m (i j) j k))))
  :hints (("Goal" :in-theory (enable approx)
                  :use (approx-inv-16
                        (:instance approx-inv-15 (m (* 8 (m (i j) j k))))))))

(local-defthmd approx-inv-18
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (m (i j) j k)))
	   (<= (si (mod (y** j) (expt 2 9)) 9)
	       (1- (* 32 (m (i j) j k)))))
  :hints (("Goal" :in-theory (enable si)
                  :use (approx-inv-16 approx-inv-17))))

(local-defthmd approx-inv-19
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (m (i j) j k)))
	   (< (* (expt 2 57) (r j))
	      (* (expt 2 55) (m (i j) j k))))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-10 approx-inv-18))))

(local-defthmd approx-inv-20
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (m (i j) j k)))
	   (< (* 4 (r j))
	      (m (i j) j k)))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-19))))

(local-defthmd approx-inv-21
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(>= (approx j) (m (i j) j k)))
	   (>= (si (mod (y** j) (expt 2 9)) 9)
	       (* 32 (m (i j) j k))))
  :hints (("Goal" :in-theory (enable approx)
                  :use (approx-inv-16
                        (:instance approx-inv-15 (m (* 8 (m (i j) j k))))))))

(local-defthmd approx-inv-22
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(>= (approx j) (m (i j) j k)))
	   (> (* (expt 2 57) (r j))
	      (* (expt 2 55) (- (m (i j) j k) 1/32))))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-10 approx-inv-21))))

(local-defthmd approx-inv-23
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(>= (approx j) (m (i j) j k)))
	   (> (* 4 (r j))
	      (- (m (i j) j k) 1/32)))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-22))))

(defthmd approx-inv-lemma
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (approx-inv j))
  :hints (("Goal" :in-theory (enable approx-inv approx-bounds)
                  :use (approx-inv-1
		        (:instance approx-inv-20 (k -1))
		        (:instance approx-inv-23 (k -1))
			(:instance approx-inv-20 (k 0))
		        (:instance approx-inv-23 (k 0))
			(:instance approx-inv-20 (k 1))
		        (:instance approx-inv-23 (k 1))
			(:instance approx-inv-20 (k 2))
		        (:instance approx-inv-23 (k 2))))))

(defthmd r-quot-bnds-inv-lemma
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (and (r-bnds-inv (1+ j))
	        (quot-bnds-inv (1+ j))))
  :hints (("Goal" :use (r-bnds quot-bnds approx-inv-lemma))))

(local-defthmd qpn-inv-1
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j)))
	   (bvecp (qp j) 54))
  :hints (("Goal" :induct (quot j) :in-theory (enable hyp quot nextroot qp qp-1))))

(local-defthmd qpn-inv-2
  (implies (and (not (specialp))
                (not (zp j))
		(<= j 27)
		(hyp j))
	   (equal (qp j) (* (expt 2 (- 54 (* 2 j))) (bits (qp j) 53 (- 54 (* 2 j))))))
  :hints (("Goal" :in-theory (enable inv hyp qpn-inv)
                  :use (qpn-inv-1
		        (:instance hyp-inv (k j))
		        (:instance bits-plus-bits (x (qp j)) (n 53) (p (- 54 (* 2 j))) (m 0))))))

(local-defthmd qpn-inv-3
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (qp (+ 1 j)) 53 (- 54 (* 2 j)))
	          (bits (qp j) 53 (- 54 (* 2 j)))))
  :hints (("Goal" :in-theory (enable bits-cat qp nextroot))))

(local-defthmd qpn-inv-4
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (bits (qp j) (- 53 (* 2 j)) (- 52 (* 2 j))) 0)
	        (equal (bits (qp j) (- 51 (* 2 j)) 0) 0)))
  :hints (("Goal" :in-theory (enable inv qpn-inv)
                  :use ((:instance hyp-inv (k j))
		        (:instance bits-plus-bits (x (qp j)) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))))))

(local-defthmd qpn-inv-5
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (qp (+ 1 j)) (- 53 (* 2 j)) (- 52 (* 2 j)))
	          (if (> (q (1+ j)) 0)
		      (q (1+ j)) 0)))
  :hints (("Goal" :in-theory (enable bits-cat qp nextroot inv qpn-inv bits-bits)
                  :use (qpn-inv-4
		        (:instance hyp-inv (k j))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd qpn-inv-6
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (qp (+ 1 j)) (- 51 (* 2 j)) 0) 0))
  :hints (("Goal" :in-theory (enable bits-cat qp nextroot inv qpn-inv bits-bits)
                  :use (qpn-inv-4
		        (:instance hyp-inv (k j))))))

(local-defthmd qpn-inv-7
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (qp (+ 1 j))
	          (+ (qp j)
		     (if (> (q (1+ j)) 0)
		         (* (expt 2 (- 52 (* 2 j))) (q (1+ j)))
		       0))))
  :hints (("Goal" :use (qpn-inv-2 qpn-inv-3 qpn-inv-5 qpn-inv-6
                        (:instance qpn-inv-1 (j (1+ j)))
			(:instance bits-plus-bits (x (qp (1+ j))) (n 53) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-plus-bits (x (qp (1+ j))) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))))))

(local-defthmd qpn-inv-8
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j)))
	   (bvecp (qn j) 54))
  :hints (("Goal" :induct (quot j) :in-theory (enable firstiter hyp quot nextroot qn qn-1))))

(local-defthmd qpn-inv-9
  (implies (and (not (specialp))
                (not (zp j))
		(<= j 27)
		(hyp j))
	   (equal (qn j) (* (expt 2 (- 54 (* 2 j))) (bits (qn j) 53 (- 54 (* 2 j))))))
  :hints (("Goal" :in-theory (enable inv hyp qpn-inv)
                  :use (qpn-inv-8
		        (:instance hyp-inv (k j))
		        (:instance bits-plus-bits (x (qn j)) (n 53) (p (- 54 (* 2 j))) (m 0))))))

(local-defthmd qpn-inv-10
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (qn (+ 1 j)) 53 (- 54 (* 2 j)))
	          (bits (qn j) 53 (- 54 (* 2 j)))))
  :hints (("Goal" :in-theory (enable bits-cat qn nextroot))))

(local-defthmd qpn-inv-11
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (bits (qn j) (- 53 (* 2 j)) (- 52 (* 2 j))) 0)
	        (equal (bits (qn j) (- 51 (* 2 j)) 0) 0)))
  :hints (("Goal" :in-theory (enable inv qpn-inv)
                  :use ((:instance hyp-inv (k j))
		        (:instance bits-plus-bits (x (qn j)) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))))))

(local-defthmd qpn-inv-12
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (qn (+ 1 j)) (- 53 (* 2 j)) (- 52 (* 2 j)))
	          (if (<= (q (1+ j)) 0)
		      (- (q (1+ j))) 0)))
  :hints (("Goal" :in-theory (enable bits-cat qn nextroot inv qpn-inv bits-bits)
                  :use (qpn-inv-11
		        (:instance hyp-inv (k j))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd qpn-inv-13
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (qn (+ 1 j)) (- 51 (* 2 j)) 0) 0))
  :hints (("Goal" :in-theory (enable bits-cat qn nextroot inv qpn-inv bits-bits)
                  :use (qpn-inv-11
		        (:instance hyp-inv (k j))))))

(local-defthmd qpn-inv-14
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (qn (+ 1 j))
	          (+ (qn j)
		     (if (<= (q (1+ j)) 0)
		         (* (expt 2 (- 52 (* 2 j))) (- (q (1+ j))))
		       0))))
  :hints (("Goal" :use (qpn-inv-9 qpn-inv-10 qpn-inv-12 qpn-inv-13
                        (:instance q-vals (j (1+ j)))
			(:instance qpn-inv-8 (j (1+ j)))
			(:instance bits-plus-bits (x (qn (1+ j))) (n 53) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-plus-bits (x (qn (1+ j))) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))))))

(local-defthmd qpn-inv-15
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (* (expt 2 54) (1- (quot (1+ j))))
                  (- (qp (1+ j)) (qn (1+ j)))))
  :hints (("Goal" :in-theory (enable inv qpn-inv qpn-inv-7 qpn-inv-14 quot)
                  :use ((:instance hyp-inv (k j))))))

(defthmd qpn-inv-lemma
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (qpn-inv (1+ j)))
  :hints (("Goal" :use (fnum-vals qpn-inv-6 qpn-inv-13 qpn-inv-15)
                  :in-theory (enable n qpn-inv))))

(local-defund dcar-0 (j)
  (setbits (setbitn (bits 0 58 0) 59 56 1) 59 55 2 (qp j)))

(local-defund dsum-0 (j)
  (setbits (bits 0 58 0) 59 55 2 (qn j)))

(local-defund dcar (j)
  (if1 (log> (q (+ j 1)) 0)
       (setbits (dcar-0 j) 59 (+ (- 53 (* 2 j)) 1) (- 53 (* 2 j)) (q (+ j 1)))
     (dcar-0 j)))

(local-defund dsum (j)
  (if1 (log> (q (+ j 1)) 0)
       (dsum-0 j)
     (if1 (log< (q (+ j 1)) 0)
          (setbits (dsum-0 j) 59 (+ (- 53 (* 2 j)) 1) (- 53 (* 2 j)) (- (q (+ j 1))))
	(dsum-0 j))))

(local-defund dqcar (j)
  (case (q (+ j 1))
    (1 (dsum j))
    (2 (bits (ash (dsum j) 1) 58 0))
    (-1 (dcar j))
    (-2 (bits (ash (dcar j) 1) 58 0))
    (t 0)))

(local-defund dqsum (j)
  (case (q (+ j 1))
    (1 (dcar j))
    (2 (bits (ash (dcar j) 1) 58 0))
    (-1 (dsum j))
    (-2 (bits (ash (dsum j) 1) 58 0))
    (t 0)))

(local-defund sum1 (j)
  (logxor (logxor (rn4 j) (rp4 j)) (dqcar j)))

(local-defund car1-0 (j)
  (bits (ash (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                     (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                             (dqcar j) ))
             1)
        58 0))

(local-defund car1 (j)
  (IF1 (log= (fnum) 0)
       (setbitn (car1-0 j) 59 42 0)
     (if1 (log= (fnum) 1)
          (setbitn (car1-0 j) 59 29 0)
        (car1-0 j))))

(local-defund sum2 (j)
  (logxor (logxor (sum1 j) (car1 j))
          (bits (lognot (dqsum j)) 58 0)))

(local-defund car2-0 (j)
  (bits (ash (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                     (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                             (bits (lognot (dqsum j)) 58 0)))
             1)
        58 0))

(local-defund car2 (j)
  (case (fnum)
    (2 (setbitn (car2-0 j) 59 0 1))
    (1 (setbitn (car2-0 j) 59 29 1))
    (0 (setbitn (car2-0 j) 59 42 1))
    (t (car2-0 j))))

(local-defund rp* (j)
  (if1 (log= (q (+ j 1)) 0)
       (rp4 j)
     (case (fnum)
       (2 (car2 j))
       (1 (setbits (rp j) 59 58 29 (bits (car2 j) 58 29)))
       (0 (setbits (rp j) 59 58 42 (bits (car2 j) 58 42)))
       (t (rp j)))))

(local-defund rn* (j)
  (if1 (log= (q (+ j 1)) 0)
       (rn4 j)
     (case (fnum)
       (2 (sum2 j))
       (1 (setbits (rn j) 59 58 29 (bits (sum2 j) 58 29)))
       (0 (setbits (rn j) 59 58 42 (bits (sum2 j) 58 42)))
       (t (rn j)))))

(local-in-theory (disable (dcar-0) (dsum-0) (dcar) (dsum) (dqcar) (dqsum) (sum1) (car1-0) (car1) (sum2) (car2-0) (car2) (rp*) (rn*)))


(local-defthm hack-1
  (implies (integerp j)
           (equal (+ -1 J 1) j)))

(local-defthmd nextrem-lemma
  (implies (not (zp j))
           (and (equal (rp (+ j 1)) (rp* j))
	        (equal (rn (+ j 1)) (rn* j))))
  :hints (("Goal" :do-not '(preprocess) :expand ((rp (+ j 1)) (rn (+ j 1)) :lambdas)
                  :in-theory '(hack-1 log= log> log< nextrem rp4 rn4 dcar-0 dsum-0 dcar dsum dqcar dqsum sum1 car1-0
		               car1 sum2 car2-0 car2 rp* rn* rp rn zp))))

(local-defthmd rpn-inv-1
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dcar-0 j)
	          (+ (expt 2 56)
		     (* 4 (qp j)))))
  :hints (("Goal" :in-theory (enable hyp dcar-0 cat bvecp)
                  :nonlinearp t
                  :use (qpn-inv-1 (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-2
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dcar-0 j)
	          (+ (expt 2 56)
		     (* (expt 2 (- 56 (* 2 j)))
		        (bits (qp j) 53 (- 54 (* 2 j)))))))
  :hints (("Goal" :in-theory (enable rpn-inv-1) :use (qpn-inv-2))))

(local-defthmd rpn-inv-3
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dcar j) 58 (- 55 (* 2 j)))
	          (bits (dcar-0 j) 58 (- 55 (* 2 j)))))
  :hints (("Goal" :in-theory (enable hyp bits-cat dcar bvecp))))

(local-defthmd rpn-inv-4
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dcar-0 j) (- 54 (* 2 j)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rpn-inv-2)
                  :use ((:instance bits-shift-up-2 (k (- 56 (* 2 j)))
		                                   (x (+ (expt 2 (* 2 j)) (bits (qp j) 53 (- 54 (* 2 j)))))
						   (i -2))))))

(local-defthmd rpn-inv-5
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dcar-0 j) (- 54 (* 2 j)) (- 53 (* 2 j)))
	          0))
  :hints (("Goal" :in-theory (enable rpn-inv-2)
                  :use ((:instance bits-shift-up-1 (k (- 56 (* 2 j)))
		                                   (x (+ (expt 2 (* 2 j)) (bits (qp j) 53 (- 54 (* 2 j)))))
						   (i (- 54 (* 2 j)))
						   (j (- 53 (* 2 j))))))))

(local-defthmd rpn-inv-6
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dcar j) (- 54 (* 2 j)) (- 53 (* 2 j)))
	          (if (> (q (+ j 1)) 0)
		      (q (+ j 1)) 0)))
  :hints (("Goal" :in-theory (enable hyp bits-cat dcar bvecp) :use (rpn-inv-5 (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-7
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dcar j) (- 52 (* 2 j)) 0)
	          (bits (dcar-0 j) (- 52 (* 2 j)) 0)))
  :hints (("Goal" :in-theory (enable hyp bits-cat dcar bvecp))))

(local-defthmd rpn-inv-8
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (bvecp (dcar j) 59)
	        (bvecp (dcar-0 j) 59)))
  :hints (("Goal" :in-theory (enable dcar dcar-0))))

(local-defthmd rpn-inv-9
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dcar j)
	          (+ (dcar-0 j)
		     (if (> (q (+ j 1)) 0)
		         (* (expt 2 (- 53 (* 2 j)))
			    (q (+ j 1)))
		       0))))
  :hints (("Goal" :use (rpn-inv-8 rpn-inv-7 rpn-inv-6 rpn-inv-5 rpn-inv-4 rpn-inv-3
                        (:instance bits-plus-bits (x (dcar j)) (n 58) (p (- 55 (* 2 j))) (m 0))
                        (:instance bits-plus-bits (x (dcar j)) (n (- 54 (* 2 j))) (p (- 53 (* 2 j))) (m 0))
                        (:instance bits-plus-bits (x (dcar-0 j)) (n 58) (p (- 55 (* 2 j))) (m 0))
                        (:instance bits-plus-bits (x (dcar-0 j)) (n (- 54 (* 2 j))) (p (- 53 (* 2 j))) (m 0))))))

(local-defthmd rpn-inv-10
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dcar j)
	          (+ (expt 2 56)
		     (* 4 (qp j))
		     (if (> (q (+ j 1)) 0)
		         (* (expt 2 (- 53 (* 2 j)))
			    (q (+ j 1)))
		       0))))
  :hints (("Goal" :use (rpn-inv-9 rpn-inv-1))))

(local-defthmd rpn-inv-11
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dsum-0 j)
	          (* 4 (qn j))))
  :hints (("Goal" :in-theory (enable hyp dsum-0 cat bvecp)
                  :nonlinearp t
                  :use (qpn-inv-8 (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-12
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dsum-0 j)
	          (* (expt 2 (- 56 (* 2 j)))
		     (bits (qn j) 53 (- 54 (* 2 j))))))
  :hints (("Goal" :in-theory (enable rpn-inv-11) :use (qpn-inv-9))))

(local-defthmd rpn-inv-13
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dsum j) 58 (- 55 (* 2 j)))
	          (bits (dsum-0 j) 58 (- 55 (* 2 j)))))
  :hints (("Goal" :in-theory (enable hyp bits-cat dsum bvecp))))

(local-defthmd rpn-inv-14
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dsum-0 j) (- 54 (* 2 j)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rpn-inv-12)
                  :use ((:instance bits-shift-up-2 (k (- 56 (* 2 j)))
		                                   (x (bits (qn j) 53 (- 54 (* 2 j))))
						   (i -2))))))

(local-defthmd rpn-inv-15
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dsum-0 j) (- 54 (* 2 j)) (- 53 (* 2 j)))
	          0))
  :hints (("Goal" :in-theory (enable rpn-inv-12)
                  :use ((:instance bits-shift-up-1 (k (- 56 (* 2 j)))
		                                   (x (bits (qn j) 53 (- 54 (* 2 j))))
						   (i (- 54 (* 2 j)))
						   (j (- 53 (* 2 j))))))))

(local-defthmd rpn-inv-16
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dsum j) (- 54 (* 2 j)) (- 53 (* 2 j)))
	          (if (<= (q (+ j 1)) 0)
		      (- (q (+ j 1))) 0)))
  :hints (("Goal" :in-theory (enable hyp bits-cat dsum bvecp) :use (rpn-inv-15 (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-17
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dsum j) (- 52 (* 2 j)) 0)
	          (bits (dsum-0 j) (- 52 (* 2 j)) 0)))
  :hints (("Goal" :in-theory (enable hyp bits-cat dsum bvecp))))

(local-defthmd rpn-inv-18
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (bvecp (dsum j) 59)
	        (bvecp (dsum-0 j) 59)))
  :hints (("Goal" :in-theory (enable dsum dsum-0))))

(local-defthmd rpn-inv-19
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dsum j)
	          (+ (dsum-0 j)
		     (if (<= (q (+ j 1)) 0)
		         (* (expt 2 (- 53 (* 2 j)))
			    (- (q (+ j 1))))
		       0))))
  :hints (("Goal" :use (rpn-inv-18 rpn-inv-17 rpn-inv-16 rpn-inv-15 rpn-inv-14 rpn-inv-13
                        (:instance bits-plus-bits (x (dsum j)) (n 58) (p (- 55 (* 2 j))) (m 0))
                        (:instance bits-plus-bits (x (dsum j)) (n (- 54 (* 2 j))) (p (- 53 (* 2 j))) (m 0))
                        (:instance bits-plus-bits (x (dsum-0 j)) (n 58) (p (- 55 (* 2 j))) (m 0))
                        (:instance bits-plus-bits (x (dsum-0 j)) (n (- 54 (* 2 j))) (p (- 53 (* 2 j))) (m 0))))))

(local-defthmd rpn-inv-20
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (dsum j)
	          (+ (* 4 (qn j))
		     (if (<= (q (+ j 1)) 0)
		         (* (expt 2 (- 53 (* 2 j)))
			    (- (q (+ j 1))))
		       0))))
  :hints (("Goal" :use (rpn-inv-19 rpn-inv-11))))

(local-defund d (j)
  (+ (* 2 (quot j))
     (* (expt 4 (- (1+ j)))
        (q (1+ j)))))

(local-defthmd rpn-inv-21
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (- (dcar j) (dsum j))
	          (* (expt 2 55) (d j))))
  :hints (("Goal" :in-theory (enable rpn-inv-10 rpn-inv-20 d hyp inv qpn-inv))))

(local-defthmd rpn-inv-22
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (mod (- (rp4 j) (rn4 j))
		       (expt 2 59))
		  (mod (* 4 (- (rp j) (rn j)))
		       (expt 2 59))))
  :hints (("Goal" :use ((:instance mod-sum (b (* 4 (rp j))) (a (- (mod (* 4 (rn j)) (expt 2 59)))) (n (expt 2 59)))
                        (:instance mod-diff (b (* 4 (rn j))) (a (* 4 (rp j))) (n (expt 2 59))))
                  :in-theory (enable ash bits-mod rp4 rn4))))

(local-defthm rpn-inv-23
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (integerp (* (expt 2 55) (r j)))
                (= (mod (* (expt 2 55) (r j)) (expt 2 59))
                   (mod (- (rp j) (rn j)) (expt 2 59)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable hyp inv rpn-inv))))

(local-defthmd rpn-inv-24
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (mod (* 4 (- (rp j) (rn j)))
		       (expt 2 59))
		  (mod (* (expt 2 57) (r j))
		       (expt 2 59))))
  :hints (("Goal" :use (rpn-inv-23
		        (:instance mod-mod-times (a (- (rp j) (rn j))) (b 4) (n (expt 2 59)))
                        (:instance mod-mod-times (a (* (expt 2 55) (r j))) (b 4) (n (expt 2 59)))))))

(local-defthmd rpn-inv-25
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (mod (- (rp4 j) (rn4 j))
		       (expt 2 59))
		  (mod (* (expt 2 57) (r j))
		       (expt 2 59))))
  :hints (("Goal" :use (rpn-inv-22 rpn-inv-24))))

(local-defthmd rpn-inv-26
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
		       (expt 2 59))
		  (mod (* (expt 2 55) (r (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :use (nextrem-lemma rpn-inv-25 r-recurrence)
                  :in-theory (enable rp* rn*))))

(local-defthm rpn-inv-27
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (equal (bits (rp j) (- 52 (p)) 0) 0)
	        (equal (bits (rn j) (- 52 (p)) 0) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable hyp inv rpn-inv))))

(local-defthmd rpn-inv-28
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (and (equal (rp (+ 1 j))
	               (bits (* 4 (rp j)) 58 0))
	        (equal (rn (+ 1 j))
	               (bits (* 4 (rn j)) 58 0))))
  :hints (("Goal" :use (nextrem-lemma)
                  :in-theory (enable rp* rn* rp4 rn4 ash-rewrite))))

(local-defthmd rpn-inv-29
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (and (equal (bits (rp (1+ j)) (- 52 (p)) 0) 0)
	        (equal (bits (rn (1+ j)) (- 52 (p)) 0) 0)))
  :hints (("Goal" :use (rpn-inv-27 p-vals
                        (:instance bits-shift-up-2 (x (rp j)) (k 2) (i (- 50 (p))))
                        (:instance bits-shift-up-2 (x (rn j)) (k 2) (i (- 50 (p))))
			(:instance bits-bits (x (rp j)) (i (- 52 (p))) (j 0) (k (- 50 (p))) (l 0))
			(:instance bits-bits (x (rn j)) (i (- 52 (p))) (j 0) (k (- 50 (p))) (l 0)))
                  :in-theory (e/d (rpn-inv-28)))))

(local-defthmd rpn-inv-30
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (* 2 (quot j)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (int-quot
                        (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-31
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (* (expt 4 (- (1+ j))) (q (1+ j))))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance q-vals (j (1+ j)))
                        (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-32
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (d j))))
  :hints (("Goal" :in-theory (enable d)
                  :use (rpn-inv-30 rpn-inv-31))))

(local-defthmd rpn-inv-33
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (q (1+ j)) (d j))))
  :hints (("Goal" :use (rpn-inv-32 (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-34
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) 4 (r j))))
  :hints (("Goal" :in-theory (enable hyp inv rpn-inv))))

(local-defthmd rpn-inv-35
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (r (+ 1 j))
	          (- (* 4 (r j))
		     (* (q (1+ j)) (d j)))))
  :hints (("Goal" :in-theory (enable d)
                  :use (r-recurrence))))

(local-defthmd rpn-inv-36
  (implies (and (integerp n) (integerp m))
           (integerp (- n m))))

(local-defthmd rpn-inv-37
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (* (expt 2 55) (r (+ 1 j)))
	          (- (* (expt 2 55) 4 (r j))
		     (* (expt 2 55) (q (1+ j)) (d j)))))
  :hints (("Goal" :use (rpn-inv-35))))

(local-defthmd rpn-inv-38
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (r (1+ j)))))
  :hints (("Goal" :use (rpn-inv-37 rpn-inv-34 rpn-inv-33
                        (:instance rpn-inv-36 (n (* (expt 2 55) 4 (r j))) (m (* (expt 2 55) (q (1+ j)) (d j))))))))

(local-defthmd rpn-inv-39
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (rpn-inv (1+ j)))
  :hints (("Goal" :use (rpn-inv-26 rpn-inv-29 rpn-inv-38)
                  :in-theory (enable rpn-inv))))

(local-defthmd rpn-inv-40
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (bvecp (dcar j) 57))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (rpn-inv-2 rpn-inv-9
		        (:instance q-vals (j (1+ j)))
			(:instance bvecp-member (x j) (n 5))
			(:instance bits-bounds (x (qp j)) (i 53) (j (- 54 (* 2 j))))))))

(local-defthmd rpn-inv-41
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (bvecp (dsum j) 56))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (rpn-inv-12 rpn-inv-19
		        (:instance q-vals (j (1+ j)))
			(:instance bvecp-member (x j) (n 5))
			(:instance bits-bounds (x (qn j)) (i 53) (j (- 54 (* 2 j))))))))

(local-defthmd rpn-inv-42
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (- (dqcar j) (dqsum j))
	          (- (* (expt 2 55) (q (1+ j)) (d j)))))
  :hints (("Goal" :in-theory (enable ash-rewrite bvecp dqcar dqsum)
                  :use (rpn-inv-21 rpn-inv-40 rpn-inv-41
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-43
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (rp4 j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rp4 ash-rewrite inv rpn-inv)
                  :use (p-vals
		        (:instance bits-bits (x (rp4 j)) (i (- 54 (p))) (j 0) (k (- 52 (p))) (l 0))
		        (:instance hyp-inv (k j))
		        (:instance bits-shift-up-2 (x (rp j)) (k 2) (i (- 52 (p))))))))

(local-defthmd rpn-inv-44
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (rn4 j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rn4 ash-rewrite inv rpn-inv)
                  :use (p-vals
		        (:instance bits-bits (x (rn4 j)) (i (- 54 (p))) (j 0) (k (- 52 (p))) (l 0))
		        (:instance hyp-inv (k j))
		        (:instance bits-shift-up-2 (x (rn j)) (k 2) (i (- 52 (p))))))))

(local-defthmd rpn-inv-45
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dcar j) (- 52 (* 2 j)) 0)
	          0))
  :hints (("Goal" :use (rpn-inv-4 rpn-inv-7 (:instance bits-bits (x (dcar-0 j)) (i (- 54 (* 2 j))) (j 0) (k (- 52 (* 2 j))) (l 0))))))

(local-defthmd rpn-inv-46
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (dcar j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :use (rpn-inv-45 fnum-vals (:instance bits-bits (x (dcar j)) (i (- 52 (* 2 j))) (j 0) (k (- 52 (p))) (l 0)))
                  :in-theory (enable dp sp hp p prec f n))))

(local-defthmd rpn-inv-47
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (bits (dsum j) (- 52 (* 2 j)) 0)
	          0))
  :hints (("Goal" :use (rpn-inv-14 rpn-inv-17 (:instance bits-bits (x (dsum-0 j)) (i (- 54 (* 2 j))) (j 0) (k (- 52 (* 2 j))) (l 0))))))

(local-defthmd rpn-inv-48
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (dsum j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :use (rpn-inv-47 fnum-vals (:instance bits-bits (x (dsum j)) (i (- 52 (* 2 j))) (j 0) (k (- 52 (p))) (l 0)))
                  :in-theory (enable dp sp hp p prec f n))))

(local-defthmd rpn-inv-49
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (and (bvecp (rp4 j) 59)
	        (bvecp (rn4 j) 59)))
  :hints (("Goal" :in-theory (enable rp4 rn4))))

(local-defthmd rpn-inv-50
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (dsum j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :use (rpn-inv-47 fnum-vals (:instance bits-bits (x (dsum j)) (i (- 52 (* 2 j))) (j 0) (k (- 52 (p))) (l 0)))
                  :in-theory (enable dp sp hp p prec f n))))

(local-defthmd rpn-inv-51
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (and (equal (bits (dcar j) (- 51 (p)) 0)
	               0)
		(equal (bits (dsum j) (- 51 (p)) 0)
	               0)))
  :hints (("Goal" :use (rpn-inv-46 rpn-inv-48 p-vals
                        (:instance bits-bits (x (dcar j)) (i (- 52 (p))) (j 0) (k (- 51 (p))) (l 0))
                        (:instance bits-bits (x (dsum j)) (i (- 52 (p))) (j 0) (k (- 51 (p))) (l 0))))))

(local-defthmd rpn-inv-52
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (and (equal (bits (dqcar j) (- 52 (p)) 0)
	               0)
		(equal (bits (dqsum j) (- 52 (p)) 0)
	               0)))
  :hints (("Goal" :use (rpn-inv-46 rpn-inv-48 rpn-inv-51 p-vals
                        (:instance bits-shift-up-2 (x (dcar j)) (k 1) (i (- 51 (p))))
                        (:instance bits-shift-up-2 (x (dsum j)) (k 1) (i (- 51 (p)))))
		  :in-theory (enable ash-rewrite dqcar dqsum))))

(local-defthmd rpn-inv-53
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (and (bvecp (dqcar j) 59)
	        (bvecp (dqsum j) 59)))
  :hints (("Goal" :use (rpn-inv-8 rpn-inv-18)
		  :in-theory (enable n dqcar dqsum))))

(local-defun top (x) (bits x 58 (- 53 (p))))

(local-defthmd rpn-inv-54
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (lognot (top (sum1 j)))
	          (logxor (logxor (lognot (top (rn4 j))) (top (rp4 j))) (top (dqcar j)))))
  :hints (("Goal" :use (p-vals) :in-theory (enable bits-logxor lognot-logxor sum1))))

(local-defthmd rpn-inv-55
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (lognot (top (sum1 j))) (+ (p) 5) 0)
	          (bits (logxor (logxor (lognot (top (rn4 j))) (top (rp4 j))) (top (dqcar j))) (+ (p) 5) 0)))
  :hints (("Goal" :use (rpn-inv-54))))

(local-defthmd rpn-inv-56
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (lognot (sum1 j)))
	          (logxor (logxor (top (lognot (rn4 j))) (top (rp4 j))) (top (dqcar j)))))
  :hints (("Goal" :use (p-vals rpn-inv-55) :in-theory (enable bits-bits bits-logxor bits-lognot-bits))))

(local-defthmd rpn-inv-57
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car1 j) 58 (- 54 (p)))
	          (bits (car1-0 j) 58 (- 54 (p)))))
  :hints (("Goal" :use (p-vals fnum-vals) :in-theory (enable car1 dp sp hp f p prec))))

(local-defthmd rpn-inv-58
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bitn (car1-0 j) 0)
	          0))
  :hints (("Goal" :in-theory (enable bitn-bits car1-0 ash-rewrite)
                  :use ((:instance bitn-shift-up (x (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                            (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                                    (dqcar j) )))
		                                 (k 1)
					         (n -1))))))

(local-defthmd rpn-inv-59
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bitn (car1 j) (- 53 (p)))
	          0))
  :hints (("Goal" :use (p-vals fnum-vals) :in-theory (enable rpn-inv-58 car1 dp sp hp f p prec))))

(local-defthmd rpn-inv-60
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car1-0 j) 58 (- 54 (p)))
	          (bits (top (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                            (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                    (dqcar j) )))
		        (+ (p) 4) 0)))
  :hints (("Goal" :use (p-vals
                        (:instance bits-shift-up-1 (x (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                              (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                                      (dqcar j) )))
						   (k 1)
						   (i 58)
						   (j (- 54 (p)))))
		  :in-theory (enable car1-0 ash-rewrite bits-bits))))

(local-defthmd rpn-inv-61
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car1-0 j) 58 (- 54 (p)))
	          (mod (top (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                    (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                            (dqcar j) )))
		       (expt 2 (+ (p) 5)))))
  :hints (("Goal" :use (p-vals rpn-inv-60)
                  :in-theory (e/d (bits-mod) (top)))))

(local-defthmd rpn-inv-62
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (car1 j))
	          (mod (* 2 (top (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                         (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                 (dqcar j) ))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals rpn-inv-57 rpn-inv-59 rpn-inv-61
                        (:instance bits-plus-bitn (x (car1 j)) (n 58) (m (- 53 (p))))
			(:instance mod-prod (k 2)
			                    (m (top (logior (logand (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                            (logand (logior (bits (lognot (rn4 j) ) 58 0) (rp4 j) )
                                                                    (dqcar j) ))))
					    (n (expt 2 (+ (p) 5))))))))

(local-defthmd rpn-inv-63
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (logior (logand (bits (lognot (rn4 j)) 58 0) (rp4 j))
                                       (logand (logior (bits (lognot (rn4 j)) 58 0) (rp4 j))
                               (dqcar j))))
		  (logior (logand (top (lognot (rn4 j))) (top (rp4 j)))
                          (logand (logior (top (lognot (rn4 j))) (top (rp4 j)))
                                  (top (dqcar j))))))
  :hints (("Goal" :use (p-vals)
                  :in-theory (enable bits-bits bits-logior bits-logand))))

(local-defthmd rpn-inv-64
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (car1 j))
	          (mod (* 2 (logior (logand (top (lognot (rn4 j))) (top (rp4 j)))
                                    (logand (logior (top (lognot (rn4 j))) (top (rp4 j)))
                                            (top (dqcar j)))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals rpn-inv-62 rpn-inv-63))))

(local-defthmd rpn-inv-65
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum1 j)))
	                  (top (car1 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ (logxor (logxor (top (lognot (rn4 j))) (top (rp4 j))) (top (dqcar j)))
		          (* 2 (logior (logand (top (lognot (rn4 j))) (top (rp4 j)))
                                       (logand (logior (top (lognot (rn4 j))) (top (rp4 j)))
                                               (top (dqcar j))))))
	               (expt 2 (+ (p) 6)))))					       
  :hints (("Goal" :use (p-vals rpn-inv-56 rpn-inv-64
                        (:instance mod-sum (a (logxor (logxor (top (lognot (rn4 j))) (top (rp4 j))) (top (dqcar j))))
			                   (b (* 2 (logior (logand (top (lognot (rn4 j))) (top (rp4 j)))
                                                           (logand (logior (top (lognot (rn4 j))) (top (rp4 j)))
                                                                   (top (dqcar j))))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-66
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum1 j)))
	                  (top (car1 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ (top (lognot (rn4 j))) (top (rp4 j)) (top (dqcar j)))
	               (expt 2 (+ (p) 6)))))					       
  :hints (("Goal" :use (p-vals rpn-inv-65
                        (:instance logand-logior (x (top (dqcar j))) (y (top (lognot (rn4 j)))) (z (top (rp4 j))))
                        (:instance add-3 (x (top (lognot (rn4 j)))) (y (top (rp4 j))) (z (top (dqcar j))))))))

(local-defthmd rpn-inv-67
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum1 j)))
	                  (top (car1 j))
			  1)
	               (expt 2 (+ (p) 6)))
	          (mod (- (top (car1 j)) (top (sum1 j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bits-lognot)
                  :use (p-vals
                        (:instance mod-mult (m (- (top (car1 j)) (top (sum1 j)))) (a 1) (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-68
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum1 j)))
	                  (top (car1 j))
			  1)
	               (expt 2 (+ (p) 6)))
	          (mod (+ 1 (top (lognot (rn4 j))) (top (rp4 j)) (top (dqcar j)))
	               (expt 2 (+ (p) 6)))))					       
  :hints (("Goal" :use (p-vals rpn-inv-66
                        (:instance mod-sum (a 1) (b (+ (top (lognot (sum1 j))) (top (car1 j)))) (n (expt 2 (+ (p) 6))))
			(:instance mod-sum (a 1) (b (+ (top (lognot (rn4 j))) (top (rp4 j)) (top (dqcar j)))) (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-70
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (top (car1 j)) (top (sum1 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ 1 (top (lognot (rn4 j))) (top (rp4 j)) (top (dqcar j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p-vals rpn-inv-68 rpn-inv-67))))

(local-defthmd rpn-inv-71
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (top (car1 j)) (top (sum1 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bits-lognot)
                  :use (p-vals rpn-inv-70
		        (:instance mod-mult (m (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j)))) (a 1) (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-72
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (lognot (top (sum2 j)))
	          (logxor (logxor (top (lognot (dqsum j))) (lognot (top (sum1 j)))) (top (car1 j)))))
  :hints (("Goal" :use (p-vals) :in-theory (enable bits-logxor lognot-logxor sum2))))

(local-defthmd rpn-inv-73
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (lognot (top (sum2 j))) (+ (p) 5) 0)
	          (bits (logxor (logxor (top (lognot (dqsum j))) (lognot (top (sum1 j)))) (top (car1 j))) (+ (p) 5) 0)))
  :hints (("Goal" :use (rpn-inv-72))))

(local-defthmd rpn-inv-74
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (lognot (sum2 j)))
	          (logxor (logxor (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j))))))
  :hints (("Goal" :use (p-vals rpn-inv-73) :in-theory (enable bits-bits bits-logxor bits-lognot-bits))))

(local-defthmd rpn-inv-75
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car2 j) 58 (- 54 (p)))
	          (bits (car2-0 j) 58 (- 54 (p)))))
  :hints (("Goal" :use (p-vals fnum-vals) :in-theory (enable car2 dp sp hp f p prec))))

(local-defthmd rpn-inv-76
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bitn (car2 j) (- 53 (p)))
	          1))
  :hints (("Goal" :use (p-vals fnum-vals) :in-theory (enable car2 dp sp hp f p prec))))

(local-defthmd rpn-inv-77
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car2-0 j) 58 (- 54 (p)))
	          (bits (top (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                                     (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                                             (bits (lognot (dqsum j)) 58 0))))
		        (+ (p) 4) 0)))
  :hints (("Goal" :use (p-vals
                        (:instance bits-shift-up-1 (x (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                                                              (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                                                                      (bits (lognot (dqsum j)) 58 0))))
						   (k 1)
						   (i 58)
						   (j (- 54 (p)))))
		  :in-theory (enable car2-0 ash-rewrite bits-bits))))

(local-defthmd rpn-inv-78
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car2-0 j) 58 (- 54 (p)))
	          (mod (top (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                                    (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                                            (bits (lognot (dqsum j)) 58 0))))
		       (expt 2 (+ (p) 5)))))
  :hints (("Goal" :use (p-vals rpn-inv-77)
                  :in-theory (e/d (bits-mod) (top)))))

(local-defthmd rpn-inv-79
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (car2 j))
	          (mod (1+ (* 2 (top (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                                             (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                                                     (bits (lognot (dqsum j)) 58 0))))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals rpn-inv-75 rpn-inv-76 rpn-inv-78
                        (:instance bits-plus-bitn (x (car2 j)) (n 58) (m (- 53 (p))))
			(:instance mod-prod (k 2)
			                    (m (top (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                                                            (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                                                                    (bits (lognot (dqsum j)) 58 0)))))
					    (n (expt 2 (+ (p) 5))))))))

(local-defthmd rpn-inv-80
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (logior (logand (bits (lognot (sum1 j)) 58 0) (car1 j))
                               (logand (logior (bits (lognot (sum1 j)) 58 0) (car1 j))
                                       (bits (lognot (dqsum j)) 58 0))))
		  (logior (logand (top (lognot (sum1 j))) (top (car1 j)))
                          (logand (logior (top (lognot (sum1 j))) (top (car1 j)))
                                  (top (lognot (dqsum j)))))))
  :hints (("Goal" :use (p-vals)
                  :in-theory (enable bits-bits bits-logior bits-logand))))

(local-defthmd rpn-inv-81
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (top (car2 j))
	          (mod (1+ (* 2 (logior (logand (top (lognot (sum1 j))) (top (car1 j)))
                                        (logand (logior (top (lognot (sum1 j))) (top (car1 j)))
                                                (top (lognot (dqsum j)))))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals rpn-inv-79 rpn-inv-80))))

(local-defthmd rpn-inv-82
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum2 j)))
	                  (top (car2 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ (logxor (logxor (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j))))
		          (* 2 (logior (logand (top (lognot (sum1 j))) (top (car1 j)))
                                       (logand (logior (top (lognot (sum1 j))) (top (car1 j)))
                                               (top (lognot (dqsum j))))))
			  1)
	               (expt 2 (+ (p) 6)))))					       
  :hints (("Goal" :use (p-vals rpn-inv-74 rpn-inv-81
                        (:instance mod-sum (a (logxor (logxor (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j)))))
			                   (b (1+ (* 2 (logior (logand (top (lognot (sum1 j))) (top (car1 j)))
                                                               (logand (logior (top (lognot (sum1 j))) (top (car1 j)))
                                                                       (top (lognot (dqsum j))))))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-83
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum2 j)))
	                  (top (car2 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ 1 (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j)))
	               (expt 2 (+ (p) 6)))))					       
  :hints (("Goal" :use (p-vals rpn-inv-82
                        (:instance logand-logior (x (top (lognot (dqsum j)))) (y (top (lognot (sum1 j)))) (z (top (car1 j))))
                        (:instance add-3 (x (top (lognot (dqsum j)))) (y (top (lognot (sum1 j)))) (z (top (car1 j))))))))

(local-defthmd rpn-inv-84
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum2 j)))
	                  (top (car2 j))
			  1)
	               (expt 2 (+ (p) 6)))
	          (mod (- (top (car2 j)) (top (sum2 j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bits-lognot)
                  :use (p-vals
                        (:instance mod-mult (m (- (top (car2 j)) (top (sum2 j)))) (a 1) (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-85
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (top (lognot (sum2 j)))
	                  (top (car2 j))
			  1)
	               (expt 2 (+ (p) 6)))
	          (mod (+ 2 (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j)))
	               (expt 2 (+ (p) 6)))))					       
  :hints (("Goal" :use (p-vals rpn-inv-83
                        (:instance mod-sum (a 1) (b (+ (top (lognot (sum2 j))) (top (car2 j)))) (n (expt 2 (+ (p) 6))))
			(:instance mod-sum (a 1) (b (+ 1 (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j))))
			                   (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-86
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (top (car2 j)) (top (sum2 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ 2 (top (lognot (dqsum j))) (top (lognot (sum1 j))) (top (car1 j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p-vals rpn-inv-84 rpn-inv-85))))

(local-defthmd rpn-inv-87
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (top (car2 j)) (top (sum2 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (- (top (car1 j)) (+ (top (sum1 j)) (top (dqsum j))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bits-lognot)
                  :use (p-vals rpn-inv-86
		        (:instance mod-mult (m (- (top (car1 j)) (+ (top (sum1 j)) (top (dqsum j))))) (a 2) (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-88
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (top (car2 j)) (top (sum2 j)))
	               (expt 2 (+ (p) 6)))
	          (mod (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j)) (- (top (dqsum j))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals rpn-inv-71 rpn-inv-87
		        (:instance mod-sum (a (- (top (dqsum j)))) (b (- (top (car1 j)) (top (sum1 j)))) (n (expt 2 (+ (p) 6))))
		        (:instance mod-sum (a (- (top (dqsum j)))) (b (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j))))
			                   (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-89
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (* (expt 2 (- 53 (p))) (- (top (car2 j)) (top (sum2 j))))
	               (expt 2 59))
	          (mod (* (expt 2 (- 53 (p))) (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j)) (- (top (dqsum j)))))
		       (expt 2 59))))
  :hints (("Goal" :use (p-vals rpn-inv-88
		        (:instance mod-prod (m (- (top (car2 j)) (top (sum2 j)))) (n (expt 2 (+ (p) 6))) (k (expt 2 (- 53 (p)))))
		        (:instance mod-prod (m (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j)) (- (top (dqsum j))))) (n (expt 2 (+ (p) 6)))
			                    (k (expt 2 (- 53 (p)))))))))

(local-defthmd rpn-inv-90
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (* (expt 2 (- 53 (p))) (+ (top (rp4 j)) (- (top (rn4 j))) (top (dqcar j)) (- (top (dqsum j)))))
	          (+ (- (rp4 j) (rn4 j)) (- (dqcar j) (dqsum j)))))	          
  :hints (("Goal" :use (p-vals rpn-inv-89 rpn-inv-52 rpn-inv-53 rpn-inv-49 rpn-inv-43 rpn-inv-44
		        (:instance bits-plus-bits (x (dqcar j)) (n 58) (p (- 53 (p))) (m 0))
		        (:instance bits-plus-bits (x (dqsum j)) (n 58) (p (- 53 (p))) (m 0))
		        (:instance bits-plus-bits (x (rp4 j)) (n 58) (p (- 53 (p))) (m 0))
		        (:instance bits-plus-bits (x (rn4 j)) (n 58) (p (- 53 (p))) (m 0)))
		  :in-theory (enable n bvecp top))))

(local-defthmd rpn-inv-91
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (* (expt 2 (- 53 (p))) (- (top (car2 j)) (top (sum2 j))))
	               (expt 2 59))
	          (mod (+ (- (rp4 j) (rn4 j)) (- (dqcar j) (dqsum j)))
		       (expt 2 59))))
  :hints (("Goal" :use (p-vals rpn-inv-90 rpn-inv-89)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd rpn-inv-92
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (- (rp4 j) (rn4 j)) (- (dqcar j) (dqsum j)))
	               (expt 2 59))
	          (mod (+ (* (expt 2 57) (r j)) (- (dqcar j) (dqsum j)))
		       (expt 2 59))))
  :hints (("Goal" :in-theory (enable n)
                  :use (rpn-inv-25
                        (:instance mod-sum (a (- (dqcar j) (dqsum j))) (b (- (rp4 j) (rn4 j))) (n (expt 2 59)))
                        (:instance mod-sum (a (- (dqcar j) (dqsum j))) (b (* (expt 2 57) (r j))) (n (expt 2 59)))))))

(local-defthmd rpn-inv-93
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (+ (* (expt 2 57) (r j)) (- (dqcar j) (dqsum j)))
	          (* (expt 2 55) (r (1+ j)))))
  :hints (("Goal" :in-theory (enable rpn-inv-35 n)
                  :use (rpn-inv-42))))

(local-defthmd rpn-inv-94
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (* (expt 2 (- 53 (p))) (- (top (car2 j)) (top (sum2 j))))
	               (expt 2 59))
	          (mod (* (expt 2 55) (r (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :use (rpn-inv-91 rpn-inv-92 rpn-inv-93)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd rpn-inv-95
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (bvecp (car2 j) 59))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable car2))))

(local-defthmd rpn-inv-96
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (bvecp (sum2 j) 59))
  :hints (("Goal" :in-theory (enable sum2 car2 sum1 car1 car1-0)
                  :use (rpn-inv-49 rpn-inv-53))))
  
(local-defthmd rpn-inv-97
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (* (expt 2 (- 53 (p))) (- (top (car2 j)) (top (sum2 j))))
	          (- (rp (1+ j)) (rn (1+ j)))))
  :hints (("Goal" :use (nextrem-lemma fnum-vals rpn-inv-27 rpn-inv-95 rpn-inv-96
                        (:instance bits-bounds (x (car2 j)) (i 58) (j (- 53 (p))))
                        (:instance bits-bounds (x (sum2 j)) (i 58) (j (- 53 (p)))))
                  :in-theory (enable n f sp dp hp p prec rp* rn* cat bvecp))))

(local-defthmd rpn-inv-98
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 59))
	          (mod (* (expt 2 55) (r (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :use (rpn-inv-94 rpn-inv-97)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd rpn-inv-99
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (and (equal (bits (rp (1+ j)) (- 52 (p)) 0) 0)
	        (equal (bits (rn (1+ j)) (- 52 (p)) 0) 0)))
  :hints (("Goal" :use (nextrem-lemma fnum-vals rpn-inv-27 rpn-inv-95 rpn-inv-96
                        (:instance bits-bounds (x (car2 j)) (i 58) (j (- 53 (p))))
                        (:instance bits-bounds (x (sum2 j)) (i 58) (j (- 53 (p)))))
                  :in-theory (enable n f sp dp hp p prec rp* rn* bvecp))))

(defthmd rpn-inv-lemma
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (rpn-inv (1+ j)))
  :hints (("Goal" :use (rpn-inv-98 rpn-inv-38 rpn-inv-39 rpn-inv-99)
                  :in-theory (enable n rpn-inv))))

(defthmd hyp-step
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (hyp (1+ j)))
  :hints (("Goal" :use (rpn-inv-lemma approx-inv-lemma r-quot-bnds-inv-lemma qpn-inv-lemma)
                  :in-theory (enable hyp inv))))

(defthmd induct-lemma
  (implies (and (not (specialp))
                (natp j)
		(<= j (n)))
           (hyp j))
  :hints (("Goal" :induct (quot j) :in-theory (enable quot))
          ("Subgoal *1/2" :use (hyp-1 (:instance hyp-step (j (1- j)))))
	  ("Subgoal *1/1" :use (hyp-0))))

(defthmd inv-lemma
  (implies (and (not (specialp))
                (natp j)
		(<= j (n)))
           (inv j))
  :hints (("Goal" :use (induct-lemma) :in-theory (enable hyp))))

(defund quotf () (quot (n)))

(defund rf () (r (n)))

(in-theory (disable (quotf) (rf)))


