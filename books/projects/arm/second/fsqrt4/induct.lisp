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

(defund root-inv (j)
  (and (bvecp (root j) 55)
       (bvecp (rootm1 j) 55)
       (= (root j) (* (expt 2 54) (quot j)))
       (= (rootm1 j) (- (root j) (expt 2 (- 54 (* 2 j)))))
       (= (bits (root j) (- 53 (* 2 j)) 0) 0)
       (= (bits (rootm1 j) (- 53 (* 2 j)) 0) 0)))

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
               (root-inv j)
               (rpn-inv j)))))

(defund hyp (j)
  (if (zp j)
      (inv 0)
    (and (inv j)
         (hyp (1- j)))))

(in-theory (disable (approx) (approx-bounds) (approx-inv) (r-bnds-inv) (quot-bnds-inv) (root-inv) (rpn-inv) (inv) (hyp)))

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
	   (and (equal (q 1) -1)
                (equal (root 1) (* (expt 2 52) 3))
                (equal (rootm1 1) (expt 2 53))))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1 root root-1 rootm1 rootm1-1))))

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
	   (and (<= (ms4 (i 0) 0 -1) (* 4 (r 0)))
	        (> (ms4 (i 0) 0 0) (* 4 (r 0)))))
  :hints (("Goal" :in-theory (enable ms4 i r0-rewrite)
                  :use (firstiter-5)
                  :nonlinearp t)))

(local-defthmd firstiter-7
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 1))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable ms4 firstiter-2 firstiter-4 approx-inv select-digit-s4 approx approx-bounds)
                  :use (firstiter-6))))

(local-defthmd firstiter-8
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 1))
	   (and (equal (q 1) 0)
                (equal (root 1) (expt 2 54))
                (equal (rootm1 1) (* (expt 2 52) 3))))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1 root root-1 rootm1 rootm1-1))))

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
	   (and (<= (ms4 (i 0) 0 0) (* 4 (r 0)))
	        (> (ms4 (i 0) 0 1) (* 4 (r 0)))))
  :hints (("Goal" :in-theory (enable ms4 i r0-rewrite)
                  :use (firstiter-9)
                  :nonlinearp t)))

(local-defthmd firstiter-11
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 1))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable ms4 firstiter-2 firstiter-8 approx-inv select-digit-s4 approx approx-bounds)
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
	   (and (equal (q 1) -2)
                (equal (root 1) (expt 2 53))
                (equal (rootm1 1) (expt 2 52))))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1 root root-1 rootm1 rootm1-1))))

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
	   (> (ms4 (i 0) 0 -1) (* 4 (r 0))))
  :hints (("Goal" :in-theory (enable ms4 i r0-rewrite)
                  :use (firstiter-14)
                  :nonlinearp t)))

(local-defthmd firstiter-16
  (implies (and (not (specialp))
                (= (expodd) 1)
		(= (bitn (siga) 51) 0))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable ms4 firstiter-2 firstiter-13 approx-inv select-digit-s4 approx approx-bounds)
                  :use (firstiter-15))))

(local-defthmd firstiter-17
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 0))	   
	   (and (equal (q 1) -1)
                (equal (root 1) (* (expt 2 52) 3))
                (equal (rootm1 1) (expt 2 53))))
  :hints (("Goal" :in-theory (enable expodd firstiter q q-1 root root-1 rootm1 rootm1-1))))

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
	   (and (<= (ms4 (i 0) 0 -1) (* 4 (r 0)))
	        (> (ms4 (i 0) 0 0) (* 4 (r 0)))))
  :hints (("Goal" :in-theory (enable ms4 i r0-rewrite)
                  :use (firstiter-18)
                  :nonlinearp t)))

(local-defthmd firstiter-20
  (implies (and (not (specialp))
                (= (expodd) 0)
		(= (bitn (siga) 51) 0))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable ms4 firstiter-2 firstiter-17 approx-inv select-digit-s4 approx approx-bounds)
                  :use (firstiter-19))))

(local-defthmd firstiter-21
  (implies (not (specialp))
	   (approx-inv 0))
  :hints (("Goal" :in-theory (enable firstiter-2)
                  :use (firstiter-7 firstiter-11 firstiter-16 firstiter-20
		        (:instance bitn-0-1 (x (siga)) (n 51))))))

(local-defthmd firstiter-22
  (implies (not (specialp))
	   (root-inv 1))
  :hints (("Goal" :in-theory (enable root-inv firstiter firstiter-2 quot)
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
	          (select-digit-s4 (approx j) (i j) j)))
  :hints (("Goal" :in-theory (enable q* nextdigit-lemma mn1 mz0 mp1 mp2 select-digit-s4 approx ms4))))

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
	   (integerp (* 8 (ms4 (i j) j k))))
  :hints (("Goal" :in-theory (enable ms4))))

(local-defthmd approx-inv-17
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (ms4 (i j) j k)))
	   (< (si (mod (y** j) (expt 2 9)) 9)
	      (* 32 (ms4 (i j) j k))))
  :hints (("Goal" :in-theory (enable approx)
                  :use (approx-inv-16
                        (:instance approx-inv-15 (m (* 8 (ms4 (i j) j k))))))))

(local-defthmd approx-inv-18
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (ms4 (i j) j k)))
	   (<= (si (mod (y** j) (expt 2 9)) 9)
	       (1- (* 32 (ms4 (i j) j k)))))
  :hints (("Goal" :in-theory (enable si)
                  :use (approx-inv-16 approx-inv-17))))

(local-defthmd approx-inv-19
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (ms4 (i j) j k)))
	   (< (* (expt 2 57) (r j))
	      (* (expt 2 55) (ms4 (i j) j k))))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-10 approx-inv-18))))

(local-defthmd approx-inv-20
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(< (approx j) (ms4 (i j) j k)))
	   (< (* 4 (r j))
	      (ms4 (i j) j k)))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-19))))

(local-defthmd approx-inv-21
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(>= (approx j) (ms4 (i j) j k)))
	   (>= (si (mod (y** j) (expt 2 9)) 9)
	       (* 32 (ms4 (i j) j k))))
  :hints (("Goal" :in-theory (enable approx)
                  :use (approx-inv-16
                        (:instance approx-inv-15 (m (* 8 (ms4 (i j) j k))))))))

(local-defthmd approx-inv-22
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(>= (approx j) (ms4 (i j) j k)))
	   (> (* (expt 2 57) (r j))
	      (* (expt 2 55) (- (ms4 (i j) j k) 1/32))))
  :hints (("Goal" :nonlinearp t
                  :use (approx-inv-10 approx-inv-21))))

(local-defthmd approx-inv-23
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(member k '(-1 0 1 2))
		(>= (approx j) (ms4 (i j) j k)))
	   (> (* 4 (r j))
	      (- (ms4 (i j) j k) 1/32)))
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

(local-defthmd root-inv-1
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j)))
	   (and (bvecp (root j) 55)
                (bvecp (rootm1 j) 55)))
  :hints (("Goal" :induct (quot j) :in-theory (enable hyp quot nextroot root rootm1))
          ("Subgoal *1/10" :use (firstiter-22) :in-theory (enable inv root-inv))
          ("Subgoal *1/9" :use (firstiter-22) :in-theory (enable inv root-inv))))

(local-defthmd root-inv-2
  (implies (and (not (specialp))
                (not (zp j))
		(<= j 27)
		(hyp j))
	   (and (equal (root j) (* (expt 2 (- 54 (* 2 j))) (bits (root j) 54 (- 54 (* 2 j)))))
	        (equal (rootm1 j) (* (expt 2 (- 54 (* 2 j))) (bits (rootm1 j) 54 (- 54 (* 2 j)))))))
  :hints (("Goal" :in-theory (enable inv hyp root-inv)
                  :use (root-inv-1
		        (:instance hyp-inv (k j))
		        (:instance bits-plus-bits (x (root j)) (n 54) (p (- 54 (* 2 j))) (m 0))
		        (:instance bits-plus-bits (x (rootm1 j)) (n 54) (p (- 54 (* 2 j))) (m 0))))))

(local-defthmd root-inv-3
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (bits (root j) (- 53 (* 2 j)) (- 52 (* 2 j))) 0)
	        (equal (bits (root j) (- 51 (* 2 j)) 0) 0)
                (equal (bits (rootm1 j) (- 53 (* 2 j)) (- 52 (* 2 j))) 0)
	        (equal (bits (rootm1 j) (- 51 (* 2 j)) 0) 0)))
  :hints (("Goal" :in-theory (enable inv root-inv)
                  :use ((:instance hyp-inv (k j))
		        (:instance bits-plus-bits (x (root j)) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))
		        (:instance bits-plus-bits (x (rootm1 j)) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))))))

(local-defthmd root-inv-4
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (= (root j) (* (expt 2 54) (quot j)))
                (= (rootm1 j) (- (root j) (expt 2 (- 54 (* 2 j)))))))
  :hints (("Goal" :in-theory (enable hyp inv root-inv))))

(local-defthmd root-inv-5
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (bits (root (+ 1 j)) 54 (- 54 (* 2 j)))
	               (if (>= (q (1+ j)) 0)
		           (bits (root j) 54 (- 54 (* 2 j)))
			 (bits (rootm1 j) 54 (- 54 (* 2 j)))))
	        (equal (bits (root (+ 1 j)) (- 53 (* 2 j)) (- 52 (* 2 j)))
	               (if (>= (q (1+ j)) 0)
		           (q (1+ j))
		         (+ 4 (q (1+ j)))))
	        (equal (bits (root (+ 1 j)) (- 51 (* 2 j)) 0)
		       0)))
  :hints (("Goal" :in-theory (enable bits-cat root nextroot inv root-inv bits-bits)
                  :use (root-inv-3
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd root-inv-6
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (root (+ 1 j)) (* (expt 2 54) (quot (1+ j))))
	        (equal (bits (root (+ 1 j)) (- 51 (* 2 j)) 0)
		       0)))
  :hints (("Goal" :in-theory (enable bvecp quot)
                  :use (root-inv-2 root-inv-4 root-inv-5
		        (:instance root-inv-1 (j (1+ j)))
		        (:instance bits-plus-bits (x (root (1+ j))) (n 54) (p (- 54 (* 2 j))) (m 0))
		        (:instance bits-plus-bits (x (root (1+ j))) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd root-inv-7
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (bits (rootm1 (+ 1 j)) 54 (- 54 (* 2 j)))
	               (if (> (q (1+ j)) 0)
		           (bits (root j) 54 (- 54 (* 2 j)))
			 (bits (rootm1 j) 54 (- 54 (* 2 j)))))
	        (equal (bits (rootm1 (+ 1 j)) (- 53 (* 2 j)) (- 52 (* 2 j)))
	               (if (> (q (1+ j)) 0)
		           (1- (q (1+ j)))
		         (+ 3 (q (1+ j)))))
	        (equal (bits (rootm1 (+ 1 j)) (- 51 (* 2 j)) 0)
		       0)))
  :hints (("Goal" :in-theory (enable bits-cat rootm1 nextroot inv root-inv bits-bits)
                  :use (root-inv-3
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd root-inv-8
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (and (equal (rootm1 (+ 1 j)) (- (root (1+ j)) (expt 2 (- 52 (* 2 j)))))
	        (equal (bits (rootm1 (+ 1 j)) (- 51 (* 2 j)) 0)
		       0)))
  :hints (("Goal" :in-theory (enable bvecp quot)
                  :use (root-inv-2 root-inv-4 root-inv-6 root-inv-7
		        (:instance root-inv-1 (j (1+ j)))
		        (:instance bits-plus-bits (x (rootm1 (1+ j))) (n 54) (p (- 54 (* 2 j))) (m 0))
		        (:instance bits-plus-bits (x (rootm1 (1+ j))) (n (- 53 (* 2 j))) (p (- 52 (* 2 j))) (m 0))
			(:instance bvecp-member (x j) (n 5))
		        (:instance q-vals (j (1+ j)))))))

(defthmd root-inv-lemma
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (root-inv (1+ j)))
  :hints (("Goal" :use (fnum-vals root-inv-6 root-inv-8 (:instance root-inv-1 (j (1+ j))))
                  :in-theory (enable n root-inv))))



(local-defund rp4* (j) (bits (ash (rp j) 2) 58 0))

(local-defund rn4* (j) (bits (ash (rn j) 2) 58 0))

(local-defund dcomp* (j)
  (case (q (+ j 1))
    (1 (let ((dcomp (setbits (bits 0 58 0) 59 56 2 (root j))))
         (setbits dcomp 59 (+ (- 53 (* 2 j)) 2) (- 53 (* 2 j)) 1)))
    (2 (let ((dcomp (setbits (bits 0 58 0) 59 57 3 (root j))))
         (setbits dcomp 59 (+ (- 54 (* 2 j)) 2) (- 54 (* 2 J)) 2)))
    (-1 (BITS 0 58 0))
    (-2 (BITS 0 58 0))
    (t (BITS 0 58 0))))

(local-defthmd bvecp-dcomp*
  (bvecp (dcomp* j) 59)
  :hints (("Goal" :in-theory (enable dcomp*))))
  
(local-defund d* (j)
  (case (q (+ j 1))
    (1 (bits (lognot (dcomp* j)) 58 0))
    (2 (bits (lognot (dcomp* j)) 58 0))
    (-1 (setbits (setbits (bits 0 58 0) 59 56 2 (rootm1 j)) 59 (+ (- 53 (* 2 j)) 2) (- 53 (* 2 j)) 7))
    (-2 (setbits (setbits (bits 0 58 0) 59 57 3 (rootm1 j)) 59 (+ (- 54 (* 2 j)) 2) (- 54 (* 2 j)) 6))
    (t (bits 0 58 0))))

(local-defthmd bvecp-d*
  (bvecp (d* j) 59)
  :hints (("Goal" :in-theory (enable d*))))
  
(local-defund sum* (j) (logxor (logxor (rp4* j) (rn4* j)) (d* j)))

(local-defund car* (j)
  (logior (logand (rp4* j) (bits (lognot (rn4* j)) 58 0))
          (logand (logior (rp4* j) (bits (lognot (rn4* j)) 58 0))
                  (d* j))))

(local-defund rp* (j)
  (if1 (log= (q (+ j 1)) 0)
       (rp4* j)
     (case (fnum)
       (2 (SETBITS (SETBITN (bits 0 58 0) 59 0 (LOG> (Q (+ j 1)) 0)) 59 58 1 (BITS (CAR* J) 57 0)))
       (1 (SETBITS (SETBITN (bits 0 58 0) 59 29 (LOG> (Q (+ j 1)) 0)) 59 58 30 (BITS (CAR* J) 57 29)))
       (0 (SETBITS (SETBITN (bits 0 58 0) 59 42 (LOG> (Q (+ j 1)) 0)) 59 58 43 (BITS (CAR* J) 57 42)))
       (t (bits 0 58 0)))))

(local-defund rn* (j)
  (if1 (log= (q (+ j 1)) 0)
       (rn4* j)
     (case (fnum)
       (2 (sum* j))
       (1 (SETBITS (bits 0 58 0) 59 58 29 (BITS (SUM* J) 58 29)))
       (0 (SETBITS (bits 0 58 0) 59 58 42 (BITS (SUM* J) 58 42)))
       (t (bits 0 58 0)))))

(local-in-theory (disable (rp4*) (rn*) (dcomp*) (d*) (sum*) (car*) (rp*) (rn*)))

(local-defthm hack-1
  (implies (integerp j)
           (equal (+ -1 J 1) j)))

(local-defthmd nextrem-lemma
  (implies (not (zp j))
           (and (equal (rp (+ j 1)) (rp* j))
	        (equal (rn (+ j 1)) (rn* j))))
  :hints (("Goal" :do-not '(preprocess) :expand ((rp (+ j 1)) (rn (+ j 1)) :lambdas)
                  :in-theory '(hack-1 log= log> log< nextrem rp4* rn4* dcomp* d* sum* car* rp* rn* rp rn zp))))

(local-defthmd rpn-inv-1
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

(local-defthm rpn-inv-2
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (integerp (* (expt 2 55) (r j)))
                (= (mod (* (expt 2 55) (r j)) (expt 2 59))
                   (mod (- (rp j) (rn j)) (expt 2 59)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable hyp inv rpn-inv))))

(local-defthmd rpn-inv-3
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (mod (* 4 (- (rp j) (rn j)))
		       (expt 2 59))
		  (mod (* (expt 2 57) (r j))
		       (expt 2 59))))
  :hints (("Goal" :use (rpn-inv-2
		        (:instance mod-mod-times (a (- (rp j) (rn j))) (b 4) (n (expt 2 59)))
                        (:instance mod-mod-times (a (* (expt 2 55) (r j))) (b 4) (n (expt 2 59)))))))

(local-defthmd rpn-inv-4
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (mod (- (rp4 j) (rn4 j))
		       (expt 2 59))
		  (mod (* (expt 2 57) (r j))
		       (expt 2 59))))
  :hints (("Goal" :use (rpn-inv-1 rpn-inv-3))))

(local-defthmd rpn-inv-5
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
		       (expt 2 59))
		  (mod (* (expt 2 55) (r (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :use (nextrem-lemma rpn-inv-4)
                  :in-theory (enable rp* rn* rp4* rn4* rp4 rn4 r-recurrence))))

(local-defthm rpn-inv-6
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (equal (bits (rp j) (- 52 (p)) 0) 0)
	        (equal (bits (rn j) (- 52 (p)) 0) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable hyp inv rpn-inv))))

(local-defthmd rpn-inv-7
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
                  :in-theory (enable rp* rn* rp4* rn4* rp4 rn4 ash-rewrite))))

(local-defthmd rpn-inv-8
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (and (equal (bits (rp (1+ j)) (- 52 (p)) 0) 0)
	        (equal (bits (rn (1+ j)) (- 52 (p)) 0) 0)))
  :hints (("Goal" :use (rpn-inv-6 p-vals
                        (:instance bits-shift-up-2 (x (rp j)) (k 2) (i (- 50 (p))))
                        (:instance bits-shift-up-2 (x (rn j)) (k 2) (i (- 50 (p))))
			(:instance bits-bits (x (rp j)) (i (- 52 (p))) (j 0) (k (- 50 (p))) (l 0))
			(:instance bits-bits (x (rn j)) (i (- 52 (p))) (j 0) (k (- 50 (p))) (l 0)))
                  :in-theory (e/d (rpn-inv-7)))))

(local-defthmd rpn-inv-9
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (* 2 (quot j)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (int-quot
                        (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-10
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (* (expt 4 (- (1+ j))) (q (1+ j))))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance q-vals (j (1+ j)))
                        (:instance bvecp-member (x j) (n 5))))))

(local-defund factor (j)
  (+ (* 2 (quot j))
     (* (expt 4 (- (1+ j)))
        (q (1+ j)))))

(local-in-theory (disable (factor)))

(local-defthmd rpn-inv-11
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (factor j))))
  :hints (("Goal" :in-theory (enable factor)
                  :use (rpn-inv-9 rpn-inv-10))))

(local-defthmd rpn-inv-12
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (q (1+ j)) (factor j))))
  :hints (("Goal" :use (rpn-inv-11 (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-13
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) 4 (r j))))
  :hints (("Goal" :in-theory (enable hyp inv rpn-inv))))

(local-defthmd rpn-inv-14
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (r (+ 1 j))
	          (- (* 4 (r j))
		     (* (q (1+ j)) (factor j)))))
  :hints (("Goal" :in-theory (enable factor)
                  :use (r-recurrence))))

(local-defthmd rpn-inv-15
  (implies (and (integerp n) (integerp m))
           (integerp (- n m))))

(local-defthmd rpn-inv-16
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (equal (* (expt 2 55) (r (+ 1 j)))
	          (- (* (expt 2 55) 4 (r j))
		     (* (expt 2 55) (q (1+ j)) (factor j)))))
  :hints (("Goal" :use (rpn-inv-14))))

(local-defthmd rpn-inv-17
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (integerp (* (expt 2 55) (r (1+ j)))))
  :hints (("Goal" :use (rpn-inv-16 rpn-inv-13 rpn-inv-12
                        (:instance rpn-inv-15 (n (* (expt 2 55) 4 (r j))) (m (* (expt 2 55) (q (1+ j)) (factor j))))))))

(local-defthmd rpn-inv-18
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(= (q (1+ j)) 0))
           (rpn-inv (1+ j)))
  :hints (("Goal" :use (rpn-inv-5 rpn-inv-8 rpn-inv-17)
                  :in-theory (enable rpn-inv))))

(local-defthmd rpn-inv-19
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (and (bvecp (root j) 55)
                (bvecp (rootm1 j) 55)))
  :hints (("Goal" :use (root-inv-1) :in-theory (enable hyp))))

(local-defthmd rpn-inv-20
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 8 (rootm1 j)) 57 (+ 57 (* -2 j)))
	          (* (expt 2 (- (* 2 j) 54))
		     (rootm1 j))))
  :hints (("goal" :in-theory (enable inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
			(:instance bits-plus-bits (x (rootm1 j)) (n 54) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-shift-up-1 (x (rootm1 j)) (k 3) (i 57) (j (- 57 (* 2 j))))))))

(local-defthmd rpn-inv-21
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 8 (rootm1 j)) (+ 53 (* -2 j)) 0)
	          0))
  :hints (("goal" :in-theory (enable inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
			(:instance bits-plus-bits (x (* 8 (rootm1 j))) (n (- 56 (* 2 j))) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-shift-up-2 (x (rootm1 j)) (k 3) (i (- 53 (* 2 j))))))))

(local-defthmd rpn-inv-22
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 4 (rootm1 j)) 56 (+ 56 (* -2 j)))
	          (* (expt 2 (- (* 2 j) 54))
		     (rootm1 j))))
  :hints (("goal" :in-theory (enable inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
			(:instance bits-plus-bits (x (rootm1 j)) (n 54) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-shift-up-1 (x (rootm1 j)) (k 2) (i 56) (j (- 56 (* 2 j))))))))

(local-defthmd rpn-inv-23
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 4 (rootm1 j)) (+ 52 (* -2 j)) 0)
	          0))
  :hints (("goal" :in-theory (enable inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
			(:instance bits-plus-bits (x (rootm1 j)) (n (- 53 (* 2 j))) (p (- 51 (* 2 j))) (m 0))
			(:instance bits-shift-up-2 (x (rootm1 j)) (k 2) (i (- 50 (* 2 j))))))))

(local-defthmd rpn-inv-24
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(bvecp j 5)
		(hyp j)
		(< (q (1+ j)) 0))
	   (equal (d* j)
	          (- (- (* 4 (q (1+ j)) (rootm1 j)))
		     (* (expt 2 (- 53 (* 2 j))) (q (1+ j)) (+ 8 (q (1+ j)))))))
  :hints (("Goal" :in-theory (enable cat d*)
                  :use (rpn-inv-19 (:instance q-vals (j (1+ j)))))
          ("Subgoal 4.1'" :in-theory (enable rpn-inv-20 rpn-inv-21))
          ("Subgoal 4.1''" :use ((:instance bvecp-member (x j) (n 5))))	  
          ("Subgoal 2.1'" :in-theory (enable rpn-inv-22 rpn-inv-23))	  
          ("Subgoal 2.1''" :use ((:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-25
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(< (q (1+ j)) 0))
	   (equal (d* j)
	          (- (- (* 4 (q (1+ j)) (rootm1 j)))
		     (* (expt 2 (- 53 (* 2 j))) (q (1+ j)) (+ 8 (q (1+ j)))))))
  :hints (("Goal" :in-theory (enable bvecp rpn-inv-24))))

(defthmd rpn-inv-26
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
           (and (equal (root j) (* (expt 2 54) (quot j)))
                (equal (rootm1 j) (- (root j) (expt 2 (- 54 (* 2 j)))))))
  :hints (("Goal" :in-theory (enable inv root-inv)
                  :use ((:instance hyp-inv (k j))))))

(local-defthmd rpn-inv-27
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(< (q (1+ j)) 0))
	   (equal (d* j)
	          (- (* (expt 2 55)
		        (q (1+ j))
			(factor j)))))
  :hints (("Goal" :in-theory (enable bvecp rpn-inv-25 rpn-inv-26 factor)
                  :use ((:instance q-vals (j (1+ j)))
		        (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-28
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(< (q (1+ j)) 0))
	   (integerp (* (expt 2 (- (p) 53))
	                (d* j))))
  :hints (("Goal" :in-theory (enable rpn-inv-27 bvecp cat n p f dp sp hp prec factor)
                  :use (fnum-vals int-quot
                        (:instance q-vals (j (1+ j)))
			(:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-29
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(< (q (1+ j)) 0))
	   (equal (bits (d* j) 58 (- 53 (p)))
	          (* (expt 2 (- (p) 53))
	             (d* j))))
  :hints (("Goal" :in-theory (enable n p f dp sp hp prec factor)
                  :use (fnum-vals bvecp-d* rpn-inv-28
		        (:instance bits-bounds (x (d* j)) (i (- 52 (p))) (j 0))
                        (:instance bits-plus-bits (x (d* j)) (n 58) (p (- 53 (p))) (m 0))))))

(local-defthmd rpn-inv-30
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(< (q (1+ j)) 0))
	   (equal (bits (d* j) 58 (- 53 (p)))
	          (- (* (expt 2 (+ (p) 2))
		        (q (1+ j))
			(factor j)))))
  :hints (("Goal" :in-theory (enable rpn-inv-27 n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-29
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-31
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 4 (root j)) 56 (+ 56 (* -2 j)))
	          (* (expt 2 (- (* 2 j) 54))
		     (root j))))
  :hints (("goal" :in-theory (enable bvecp inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
		        (:instance bvecp-member (x j) (n 5))
			(:instance bits-plus-bits (x (root j)) (n 54) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-shift-up-1 (x (root j)) (k 2) (i 56) (j (- 56 (* 2 j))))))))

(local-defthmd rpn-inv-32
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 4 (root j)) (+ 52 (* -2 j)) 0)
	          0))
  :hints (("goal" :in-theory (enable inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
			(:instance bits-plus-bits (x (root j)) (n (- 53 (* 2 j))) (p (- 51 (* 2 j))) (m 0))
			(:instance bits-shift-up-2 (x (root j)) (k 2) (i (- 50 (* 2 j))))))))

(local-defthmd rpn-inv-33
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 8 (root j)) 57 (+ 57 (* -2 j)))
	          (* (expt 2 (- (* 2 j) 54))
		     (root j))))
  :hints (("goal" :in-theory (enable bvecp inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
		        (:instance bvecp-member (x j) (n 5))
			(:instance bits-plus-bits (x (root j)) (n 54) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-shift-up-1 (x (root j)) (k 3) (i 57) (j (- 57 (* 2 j))))))))

(local-defthmd rpn-inv-34
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j))
	   (equal (bits (* 8 (root j)) (+ 53 (* -2 j)) 0)
	          0))
  :hints (("goal" :in-theory (enable inv root-inv)
                  :use (rpn-inv-19
		        (:instance hyp-inv (k j))
			(:instance bits-plus-bits (x (* 8 (root j))) (n (- 56 (* 2 j))) (p (- 54 (* 2 j))) (m 0))
			(:instance bits-shift-up-2 (x (root j)) (k 3) (i (- 53 (* 2 j))))))))

(local-defthmd rpn-inv-35
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(bvecp j 5)
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (dcomp* j)
	          (+ (* 4 (q (1+ j)) (root j))
		     (* (expt 2 (- 53 (* 2 j))) (q (1+ j)) (q (1+ j))))))
  :hints (("Goal" :in-theory (enable cat dcomp*)
                  :use (rpn-inv-19 (:instance q-vals (j (1+ j)))))		  
          ("Subgoal 4.1'" :in-theory (enable rpn-inv-31 rpn-inv-32))
          ("Subgoal 4.1''" :use ((:instance bvecp-member (x j) (n 5))))	  
          ("Subgoal 2.1'" :in-theory (enable rpn-inv-33 rpn-inv-34))	  
          ("Subgoal 2.1''" :use ((:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-36
  (implies (and (not (specialp))
                (not (zp j))
		(< j 27)
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (dcomp* j)
	          (* (expt 2 55)
		     (q (1+ j))
		     (factor j))))
  :hints (("Goal" :in-theory (enable bvecp rpn-inv-35 rpn-inv-26 factor)
                  :use ((:instance q-vals (j (1+ j)))
		        (:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-37
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (integerp (* (expt 2 (- (p) 53))
	                (dcomp* j))))
  :hints (("Goal" :in-theory (enable rpn-inv-36 bvecp cat n p f dp sp hp prec factor)
                  :use (fnum-vals int-quot
                        (:instance q-vals (j (1+ j)))
			(:instance bvecp-member (x j) (n 5))))))

(local-defthmd rpn-inv-38
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (bits (dcomp* j) 58 (- 53 (p)))
	          (* (expt 2 (- (p) 53))
	             (dcomp* j))))
  :hints (("Goal" :in-theory (enable n p f dp sp hp prec factor)
                  :use (fnum-vals bvecp-dcomp* rpn-inv-37
		        (:instance bits-bounds (x (dcomp* j)) (i (- 52 (p))) (j 0))
                        (:instance bits-plus-bits (x (dcomp* j)) (n 58) (p (- 53 (p))) (m 0))))))

(local-defthmd rpn-inv-39
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (bits (dcomp* j) 58 (- 53 (p)))
	          (* (expt 2 (+ (p) 2))
		     (q (1+ j))
		     (factor j))))
  :hints (("Goal" :in-theory (enable rpn-inv-36 n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-38
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-40
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (bits (d* j) 58 (- 53 (p)))
	          (bits (lognot (dcomp* j)) 58 (- 53 (p)))))
  :hints (("Goal" :in-theory (enable bits-bits bvecp d* n p f dp sp hp prec)
                  :use (fnum-vals bvecp-dcomp*
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-41
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (bits (d* j) 58 (- 53 (p)))
	          (- (1- (expt 2 (+ (p) 6)))
	             (bits (dcomp* j) 58 (- 53 (p))))))
  :hints (("Goal" :in-theory (enable bvecp d* bits-lognot n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-40 bvecp-dcomp*
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-42
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (bits (d* j) 58 (- 53 (p)))
	          (- (1- (expt 2 (+ (p) 6)))
	             (* (expt 2 (+ (p) 2))
		        (q (1+ j))
		        (factor j)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-39 rpn-inv-41 bvecp-dcomp*
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-42
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (bits (d* j) 58 (- 53 (p)))
	          (- (1- (expt 2 (+ (p) 6)))
	             (* (expt 2 (+ (p) 2))
		        (q (1+ j))
		        (factor j)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-39 rpn-inv-41 bvecp-dcomp*
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-43
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (mod (- (1- (expt 2 (+ (p) 6)))
	                  (* (expt 2 (+ (p) 2))
		             (q (1+ j))
		             (factor j)))
	               (expt 2 (+ (p) 6)))
	          (mod (1- (- (* (expt 2 (+ (p) 2))
		              (q (1+ j))
		              (factor j))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (e/d (bvecp n p f dp sp hp prec) (ACL2::|(mod (- x) y)|))
                  :use (fnum-vals
		        (:instance mod-mult (a 1) (n (expt 2 (+ (p) 6)))
			                    (m  (1- (- (* (expt 2 (+ (p) 2))
		                                          (q (1+ j))
		                                          (factor j))))))
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd rpn-inv-44
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(> (q (1+ j)) 0))
	   (equal (mod (bits (d* j) 58 (- 53 (p)))
	               (expt 2 (+ (p) 6)))
	          (mod (1- (- (* (expt 2 (+ (p) 2))
		              (q (1+ j))
		              (factor j))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (rpn-inv-43 rpn-inv-42) :in-theory (theory 'minimal-theory))))

(local-defthmd rpn-inv-45
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
	   (equal (mod (bits (d* j) 58 (- 53 (p)))
	               (expt 2 (+ (p) 6)))
	          (mod (- (- (* (expt 2 (+ (p) 2))
		             (q (1+ j))
		             (factor j)))
			  (if (> (q (1+ j)) 0) 1 0))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (rpn-inv-44 rpn-inv-30))))

(local-defthmd rpn-inv-46
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (equal (bits (rp4 j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rp4 ash-rewrite inv rpn-inv)
                  :use (p-vals
		        (:instance bits-bits (x (rp4 j)) (i (- 54 (p))) (j 0) (k (- 52 (p))) (l 0))
		        (:instance hyp-inv (k j))
		        (:instance bits-shift-up-2 (x (rp j)) (k 2) (i (- 52 (p))))))))

(local-defthmd rpn-inv-47
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (equal (bits (rn4 j) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rn4 ash-rewrite inv rpn-inv)
                  :use (p-vals
		        (:instance bits-bits (x (rn4 j)) (i (- 54 (p))) (j 0) (k (- 52 (p))) (l 0))
		        (:instance hyp-inv (k j))
		        (:instance bits-shift-up-2 (x (rn j)) (k 2) (i (- 52 (p))))))))

(local-defthmd bvecp-rp4
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (bvecp (rp4 j) 59))
  :hints (("Goal" :in-theory (enable rp4))))

(local-defthmd bvecp-rn4
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (bvecp (rn4 j) 59))
  :hints (("Goal" :in-theory (enable rn4))))

(local-defthmd rpn-inv-48
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (equal (bits (rp4 j) 58 (- 53 (p)))
	          (* (expt 2 (- (p) 53))
		     (rp4 j))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (bvecp-rp4 rpn-inv-46
                        (:instance bits-plus-bits (x (rp4 j)) (n 58) (p  (- 53 (p))) (m 0))))))

(local-defthmd rpn-inv-49
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (equal (bits (rn4 j) 58 (- 53 (p)))
	          (* (expt 2 (- (p) 53))
		     (rn4 j))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (bvecp-rn4 rpn-inv-47
                        (:instance bits-plus-bits (x (rn4 j)) (n 58) (p  (- 53 (p))) (m 0))))))

(local-defthmd rpn-inv-50
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (equal (mod (- (bits (rp4 j) 58 (- 53 (p)))
	                  (bits (rn4 j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
	          (mod (* (expt 2 (+ (p) 4)) (r j))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (rpn-inv-4 rpn-inv-48 rpn-inv-49
                        (:instance mod-prod (k (expt 2 (- (p) 53))) (n (expt 2 59)) (m (* (expt 2 57) (r j))))
			(:instance mod-prod (k (expt 2 (- (p) 53))) (n (expt 2 59)) (m (- (rp4 j) (rn4 j))))))))

(local-defthmd rpn-inv-51
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (integerp (- (- (bits (rp4 j) 58 (- 53 (p)))
	                   (bits (rn4 j) 58 (- 53 (p))))
			(* (expt 2 (+ (p) 4)) (r j)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (rpn-inv-50
                        (:instance mod-equal-int (a (- (bits (rp4 j) 58 (- 53 (p))) (bits (rn4 j) 58 (- 53 (p)))))
			                         (b (* (expt 2 (+ (p) 4)) (r j)))
						 (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-52
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
	   (integerp (* (expt 2 (+ (p) 4)) (r j))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (rpn-inv-51))))

(local-defthmd rpn-inv-53
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (lognot (sum* j))
	          (logxor (logxor (rp4 j) (lognot (rn4 j))) (d* j))))
  :hints (("Goal" :in-theory (enable rp4 rn4 rp4* rn4* lognot-logxor sum*))))

(local-defthmd rpn-inv-54
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (lognot (sum* j)) 58 (- 53 (p)))
	          (logxor (logxor (bits (rp4 j) 58 (- 53 (p)))
		                  (bits (lognot (rn4 j)) 58 (- 53 (p))))
		          (bits (d* j) 58 (- 53 (p))))))
  :hints (("Goal" :use (rpn-inv-53)
                  :in-theory (enable bvecp n p f dp sp hp prec bits-logxor sum* rp4 rn4 rn4* rp4* d*))))

(local-defthmd rpn-inv-55
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (bits (car* j) 58 (- 53 (p)))
                  (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                  (bits (lognot (rn4 j)) 58 (- 53 (p))))
                          (logand (logior (bits (rp4 j) 58 (- 53 (p)))
                                          (bits (lognot (rn4 j)) 58 (- 53 (p))))
                                  (bits (d* J) 58 (- 53 (p)))))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec bits-logior bits-logand bits-bits car* rp4 rn4 rn4* rp4* d*))))

(local-defthmd rpn-inv-56
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (+ (* 2 (bits (car* j) 58 (- 53 (p))))
	             (bits (lognot (sum* j)) 58 (- 53 (p))))
		  (+ (logxor (bits (rp4 j) 58 (- 53 (p)))
                             (logxor (bits (lognot (rn4 j)) 58 (- 53 (p)))
                                     (bits (d* J) 58 (- 53 (p)))))
		     (* 2 (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                          (bits (lognot (rn4 j)) 58 (- 53 (p))))
                                  (logand (logior (bits (rp4 j) 58 (- 53 (p)))
                                                  (bits (lognot (rn4 j)) 58 (- 53 (p))))
                                          (bits (d* J) 58 (- 53 (p)))))))))
  :hints (("Goal" :use (rpn-inv-54 rpn-inv-55)
                  :in-theory (enable bvecp n p f dp sp hp prec))))

(local-defthmd rpn-inv-57
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                  (bits (lognot (rn4 j)) 58 (- 53 (p))))
                          (logand (logior (bits (rp4 j) 58 (- 53 (p)))
                                          (bits (lognot (rn4 j)) 58 (- 53 (p))))
                                  (bits (d* J) 58 (- 53 (p)))))
		  (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                  (bits (lognot (rn4 j)) 58 (- 53 (p))))
                          (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                          (bits (d* J) 58 (- 53 (p))))
				  (logand (bits (lognot (rn4 j)) 58 (- 53 (p)))
                                          (bits (d* J) 58 (- 53 (p))))))))
  :hints (("Goal" :use ((:instance logior-logand-2 (y (bits (rp4 j) 58 (- 53 (p))))
		                                   (z (bits (lognot (rn4 j)) 58 (- 53 (p))))
				                   (x (bits (d* J) 58 (- 53 (p))))))
                  :in-theory (enable bvecp n p f dp sp hp prec))))

(local-defthmd rpn-inv-58
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (+ (logxor (bits (rp4 j) 58 (- 53 (p)))
                             (logxor (bits (lognot (rn4 j)) 58 (- 53 (p)))
                                     (bits (d* J) 58 (- 53 (p)))))
		     (* 2 (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                          (bits (lognot (rn4 j)) 58 (- 53 (p))))
                                  (logior (logand (bits (rp4 j) 58 (- 53 (p)))
                                                  (bits (d* J) 58 (- 53 (p))))
				          (logand (bits (lognot (rn4 j)) 58 (- 53 (p)))
                                                  (bits (d* J) 58 (- 53 (p))))))))
		  (+ (bits (rp4 j) 58 (- 53 (p)))
                     (bits (lognot (rn4 j)) 58 (- 53 (p)))
                     (bits (d* J) 58 (- 53 (p))))))
  :hints (("Goal" :use ((:instance add-3 (x (bits (rp4 j) 58 (- 53 (p))))
		                         (y (bits (lognot (rn4 j)) 58 (- 53 (p))))
				         (z (bits (d* J) 58 (- 53 (p))))))
                  :in-theory (enable bvecp n p f dp sp hp prec))))

(local-defthmd rpn-inv-59
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (+ (* 2 (bits (car* j) 58 (- 53 (p))))
	             (bits (lognot (sum* j)) 58 (- 53 (p))))
		  (+ (bits (rp4 j) 58 (- 53 (p)))
                     (bits (lognot (rn4 j)) 58 (- 53 (p)))
                     (bits (d* J) 58 (- 53 (p))))))
  :hints (("Goal" :use (rpn-inv-56 rpn-inv-57 rpn-inv-58))))

(local-defthmd rpn-inv-60
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (* 2 (bits (car* j) 58 (- 53 (p))))
	                  (bits (lognot (sum* j)) 58 (- 53 (p)))
			  1)
		       (expt 2 (+ (p) 6)))
		  (mod (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                  (bits (sum* j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec bits-lognot)
                  :use (fnum-vals
		        (:instance mod-mult (m (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                                          (bits (sum* j) 58 (- 53 (p)))))
				            (a 1)
				            (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-61
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                  (bits (sum* j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (bits (rp4 j) 58 (- 53 (p)))
                          (bits (lognot (rn4 j)) 58 (- 53 (p)))
                          (bits (d* J) 58 (- 53 (p)))
			  1)
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (rpn-inv-59 rpn-inv-60))))

(local-defthmd rpn-inv-62
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                  (bits (sum* j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (bits (rp4 j) 58 (- 53 (p)))
                          (- (bits (rn4 j) 58 (- 53 (p))))
                          (bits (d* J) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec bits-lognot)
                  :use (fnum-vals rpn-inv-61
		        (:instance mod-mult (m (+ (bits (rp4 j) 58 (- 53 (p)))
                                                  (- (bits (rn4 j) 58 (- 53 (p))))
                                                  (bits (d* J) 58 (- 53 (p)))))
				            (a 1)
				            (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-63
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (bits (rp4 j) 58 (- 53 (p)))
                          (- (bits (rn4 j) 58 (- 53 (p))))
                          (bits (d* J) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 4)) (r j))
                          (bits (d* J) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec bits-lognot)
                  :use (fnum-vals rpn-inv-50
		        (:instance mod-sum (a (bits (d* J) 58 (- 53 (p))))
			                   (b (- (bits (rp4 j) 58 (- 53 (p)))
                                                 (bits (rn4 j) 58 (- 53 (p)))))
				           (n (expt 2 (+ (p) 6))))
		        (:instance mod-sum (a (bits (d* J) 58 (- 53 (p))))
			                   (b (* (expt 2 (+ (p) 4)) (r j)))
				           (n (expt 2 (+ (p) 6))))))))

(defthm rat-r
  (rationalp (r j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable r))))

(local-defthmd rpn-inv-64
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 4)) (r j))
                          (bits (d* J) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 4)) (r j))
                          (mod (bits (d* J) 58 (- 53 (p)))
			       (expt 2 (+ (p) 6))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec bits-lognot)
                  :use (fnum-vals
		        (:instance q-vals (j (1+ j)))
		        (:instance mod-sum (b (bits (d* J) 58 (- 53 (p))))
			                   (a (* (expt 2 (+ (p) 4)) (r j)))
				           (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-65
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (+ (* (expt 2 (+ (p) 4)) (r j))
                          (bits (d* J) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 4)) (r j))
                          (mod (- (- (* (expt 2 (+ (p) 2))
		                        (q (1+ j))
		                        (factor j)))
			          (if (> (q (1+ j)) 0) 1 0))
			       (expt 2 (+ (p) 6))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rpn-inv-64 rpn-inv-45))))

(local-defthmd rpn-inv-66
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (+ (* (expt 2 (+ (p) 4)) (r j))
                          (bits (d* J) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (- (- (* (expt 2 (+ (p) 4)) (r j))
                             (* (expt 2 (+ (p) 2))
		                (q (1+ j))
		                (factor j)))
			  (if (> (q (1+ j)) 0) 1 0))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec bits-lognot)
                  :use (fnum-vals rpn-inv-65
		        (:instance q-vals (j (1+ j)))
		        (:instance mod-sum (b (- (- (* (expt 2 (+ (p) 2))
		                                       (q (1+ j))
		                                       (factor j)))
			                         (if (> (q (1+ j)) 0) 1 0)))
			                   (a (* (expt 2 (+ (p) 4)) (r j)))
				           (n (expt 2 (+ (p) 6))))))))

(local-defthmd rpn-inv-67
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                  (bits (sum* j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (- (- (* (expt 2 (+ (p) 4)) (r j))
                             (* (expt 2 (+ (p) 2))
		                (q (1+ j))
		                (factor j)))
			  (if (> (q (1+ j)) 0) 1 0))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rpn-inv-62 rpn-inv-63 rpn-inv-66))))

(local-defthmd rpn-inv-68
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                  (bits (sum* j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (- (* (expt 2 (+ (p) 2)) (r (1+ j)))
			  (if (> (q (1+ j)) 0) 1 0))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable r-recurrence factor bvecp n p f dp sp hp prec bits-lognot)
                  :use (fnum-vals rpn-inv-67))))

(local-defthmd rpn-inv-69
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (rn (+ 1 j))
	          (* (expt 2 (- 53 (p)))
		     (bits (sum* j) 58 (- 53 (p))))))
  :hints (("Goal" :in-theory (enable cat rn* bvecp n p f dp sp hp prec)
                  :use (nextrem-lemma fnum-vals
		        (:instance bits-bounds (x (sum* j)) (i 58) (j (- 53 (p))))))))

(local-defthmd rpn-inv-70
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (rp (+ 1 j))
	          (* (expt 2 (- 53 (p)))
		     (+ (* 2 (bits (car* j) 57 (- 53 (p))))
		        (if (> (q (1+ j)) 0) 1 0)))))
  :hints (("Goal" :in-theory (enable cat rp* bvecp n p f dp sp hp prec)
                  :use (nextrem-lemma fnum-vals
		        (:instance bits-bounds (x (car* j)) (i 57) (j (- 53 (p))))
		        (:instance bits-bounds (x (car* j)) (i 57) (j 0))))))

(local-defthmd rpn-inv-71
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (- (rp (+ 1 j)) (rn (+ 1 j)))
	          (* (expt 2 (- 53 (p)))
		     (+ (* 2 (bits (car* j) 57 (- 53 (p))))
		        (- (bits (sum* j) 58 (- 53 (p))))
		        (if (> (q (1+ j)) 0) 1 0)))))
  :hints (("Goal" :in-theory (enable cat rp* bvecp n p f dp sp hp prec)
                  :use (rpn-inv-69 rpn-inv-70))))

(local-defthmd rpn-inv-72
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (* (expt 2 (- 53 (p)))
		          (+ (* 2 (bits (car* j) 57 (- 53 (p))))
		             (- (bits (sum* j) 58 (- 53 (p))))
		             (if (> (q (1+ j)) 0) 1 0)))
		       (expt 2 59))
	          (mod (* (expt 2 (- 53 (p)))
		          (+ (* 2 (bits (car* j) 58 (- 53 (p))))
		             (- (bits (sum* j) 58 (- 53 (p))))
		             (if (> (q (1+ j)) 0) 1 0)))
		       (expt 2 59))))
  :hints (("Goal" :in-theory (e/d (bvecp n p f dp sp hp prec) (ACL2::|(mod (+ 1 x) y)|))
                  :use (fnum-vals
		        (:instance mod-mult (m (+ (* 2 (bits (car* j) 57 (- 53 (p))))
		                                  (- (bits (sum* j) 58 (- 53 (p))))
		                                  (if (> (q (1+ j)) 0) 1 0)))
				            (n (expt 2 59))
					    (a 1))
		        (:instance bitn-0-1 (x (car* j)) (n 58))
		        (:instance bitn-plus-bits (x (car* j)) (n 58) (m (- 53 (p))))))))

(local-defthmd rpn-inv-73
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (- (rp (+ 1 j)) (rn (+ 1 j)))
	               (expt 2 59))
	          (mod (* (expt 2 (- 53 (p)))
		          (+ (* 2 (bits (car* j) 58 (- 53 (p))))
		             (- (bits (sum* j) 58 (- 53 (p))))
		             (if (> (q (1+ j)) 0) 1 0)))
		       (expt 2 59))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rpn-inv-71 rpn-inv-72))))

(local-defthmd rpn-inv-74
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (* (expt 2 (- 53 (p)))
	                  (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                     (bits (sum* j) 58 (- 53 (p)))))
		       (expt 2 59))
		  (mod (- (* (expt 2 55) (r (1+ j)))
			  (* (expt 2 (- 53 (p))) (if (> (q (1+ j)) 0) 1 0)))
		       (expt 2 59))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-68
		        (:instance mod-prod (k (expt 2 (- 53 (p))))
			                    (n (expt 2 (+ (p) 6)))
					    (m (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                                          (bits (sum* j) 58 (- 53 (p))))))
		        (:instance mod-prod (k (expt 2 (- 53 (p))))
			                    (n (expt 2 (+ (p) 6)))
					    (m (- (* (expt 2 (+ (p) 2)) (r (1+ j)))
			                          (if (> (q (1+ j)) 0) 1 0))))))))

(local-defthmd rpn-inv-75
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (* (expt 2 (- 53 (p)))
	                  (+ (* 2 (bits (car* j) 58 (- 53 (p))))
	                     (- (bits (sum* j) 58 (- 53 (p))))
			     (if (> (q (1+ j)) 0) 1 0)))
		       (expt 2 59))
		  (mod (* (expt 2 55) (r (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-17 rpn-inv-74
		        (:instance mod-plus-mod-iff (a (* (expt 2 (- 53 (p)))
	                                                  (- (* 2 (bits (car* j) 58 (- 53 (p))))
	                                                     (bits (sum* j) 58 (- 53 (p))))))
					            (b (- (* (expt 2 55) (r (1+ j)))
			                                  (* (expt 2 (- 53 (p))) (if (> (q (1+ j)) 0) 1 0))))
					   	    (c (* (expt 2 (- 53 (p))) (if (> (q (1+ j)) 0) 1 0)))
						    (n (expt 2 59)))))))

(local-defthmd rpn-inv-76
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (equal (mod (- (rp (+ 1 j)) (rn (+ 1 j)))
	               (expt 2 59))
	          (mod (* (expt 2 55) (r (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rpn-inv-73 rpn-inv-75))))

(local-defthmd rpn-inv-77
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (and (integerp (* (expt 2 (- (p) 53)) (rp (+ 1 j))))
	        (integerp (* (expt 2 (- (p) 53)) (rn (+ 1 j))))))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-69 rpn-inv-70
		        (:instance bvecp-rp-j (j (1+ j)))
		        (:instance bvecp-rn-j (j (1+ j)))))))

(local-defthmd rpn-inv-78
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (and (equal (rp (+ 1 j))
	               (+ (* (expt 2 (- 53 (p))) (bits (rp (+ 1 j)) 58 (- 53 (p))))
		          (bits (rp (+ 1 j)) (- 52 (p)) 0)))
                (equal (rn (+ 1 j))
	               (+ (* (expt 2 (- 53 (p))) (bits (rn (+ 1 j)) 58 (- 53 (p))))
		          (bits (rn (+ 1 j)) (- 52 (p)) 0)))))	        
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals
		        (:instance bvecp-rp-j (j (1+ j)))
		        (:instance bvecp-rn-j (j (1+ j)))
			(:instance bits-plus-bits (x (rp (1+ j))) (n 58) (p (- 53 (p))) (m 0))
			(:instance bits-plus-bits (x (rn (1+ j))) (n 58) (p (- 53 (p))) (m 0))))))

(local-defthmd hack-2
  (implies (integerp (* (expt 2 (- (p) 53)) 
                        (+ (* (expt 2 (- 53 (p))) (bits (rp (+ 1 j)) 58 (- 53 (p))))
		           (bits (rp (+ 1 j)) (- 52 (p)) 0))))
	   (integerp (* (expt 2 (- (p) 53)) (bits (rp (+ 1 j)) (- 52 (p)) 0)))))

(local-defthmd hack-3
  (implies (integerp (* (expt 2 (- (p) 53)) 
                        (+ (* (expt 2 (- 53 (p))) (bits (rn (+ 1 j)) 58 (- 53 (p))))
		           (bits (rn (+ 1 j)) (- 52 (p)) 0))))
	   (integerp (* (expt 2 (- (p) 53)) (bits (rn (+ 1 j)) (- 52 (p)) 0)))))

(local-defthmd rpn-inv-79
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (and (integerp (* (expt 2 (- (p) 53)) (bits (rp (+ 1 j)) (- 52 (p)) 0)))
	        (integerp (* (expt 2 (- (p) 53)) (bits (rn (+ 1 j)) (- 52 (p)) 0)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rpn-inv-77 rpn-inv-78 hack-2 hack-3))))

(local-defthmd rpn-inv-80
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j)
		(not (= (q (1+ j)) 0)))
           (and (equal (bits (rp (+ 1 j)) (- 52 (p)) 0) 0)
	        (equal (bits (rn (+ 1 j)) (- 52 (p)) 0) 0)))
  :hints (("Goal" :in-theory (enable bvecp n p f dp sp hp prec)
                  :use (fnum-vals rpn-inv-79
			(:instance bits-bounds (x (rp (1+ j))) (i (- 52 (p))) (j 0))
			(:instance bits-bounds (x (rn (1+ j))) (i (- 52 (p))) (j 0))))))

(defthmd rpn-inv-lemma
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (rpn-inv (1+ j)))
  :hints (("Goal" :use (rpn-inv-80 rpn-inv-76 rpn-inv-17 rpn-inv-18)
                  :in-theory (enable n rpn-inv))))

(defthmd hyp-step
  (implies (and (not (specialp))
                (not (zp j))
		(< j (n))
		(hyp j))
           (hyp (1+ j)))
  :hints (("Goal" :use (rpn-inv-lemma approx-inv-lemma r-quot-bnds-inv-lemma root-inv-lemma)
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


