(in-package "RTL")

(include-book "clz")

(local-defund multiplier ()
  (bits (ash (manb) 1) 54 0))

(local-defund pprod ()
  (computeproduct-loop-0 0 (multiplier) (mana) ()))

(local-defund ia ()
  (bits (if1 (log= (expa) 0) 0 (manb)) 51 0))

(local-defund ib ()
  (setbitn (bits (if1 (log= (expb) 0) 0 (mana)) 52 0) 53 52
           (logand1 (lognot1 (log= (expa) 0)) (lognot1 (log= (expb) 0)))))

(local-defund ppa ()
  (mv-nth 0 (mv-list 2 (compress (pprod) (ia) (ib)))))

(local-defund ppb ()
  (mv-nth 1 (mv-list 2 (compress (pprod) (ia) (ib)))))

(local-defund prod* ()
  (bits (+ (ppa) (ppb)) 105 0))

(local-defthmd computeproduct-lemma
  (equal (prod) (prod*))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(multiplier pprod ia ib ppa ppb prod* prod computeproduct))))

(local-defund slc (i) (bits (multiplier) (+ (* 2 i) 2) (* 2 i)))

(local-defund enc (i)
  (- (+ (bitn (slc i) 0) (bitn (slc i) 1))
     (* 2 (bitn (slc i) 2))))

(local-defund mux (i)
  (let ((mux (case (enc i) (0 (bits 0 52 0))
                           ((1 -1) (mana))
                           ((2 -2) (bits (ash (mana) 1) 52 0))
                           (t 0))))
    (if1 (bitn (slc i) 2) (bits (lognot mux) 52 0) mux)))

(local-in-theory (disable (multiplier) (pprod) (ia) (ib) (ppa) (ppb) (prod*) (slc) (enc) (mux)))

(local-defund update-pp (i pp)
  (if1 (log= i 0)
       (let* ((pp (as i (setbits (ag i pp) 57 52 0 (mux i)) pp))
              (pp (as i (setbitn (ag i pp) 57 53 (bitn (slc i) 2)) pp))
              (pp (as i (setbitn (ag i pp) 57 54 (bitn (slc i) 2)) pp))
              (pp (as i (setbitn (ag i pp) 57 55 (lognot1 (bitn (slc i) 2))) pp)))
         (as i (setbitn (ag i pp) 57 56 0) pp))
       (let* ((pp (as i (setbitn (ag i pp) 57 0 (bitn (slc i) 0)) pp))
              (pp (as i (setbitn (ag i pp) 57 1 0) pp))
              (pp (as i (setbits (ag i pp) 57 54 2 (mux i)) pp))
              (pp (as i (setbitn (ag i pp) 57 55 (lognot1 (bitn (slc i) 2))) pp)))
         (as i (setbitn (ag i pp) 57 56 (log< i 26)) pp))))

(local-defund loop-simple (i pp)
  (declare (xargs :measure (nfix (- 27 i))))
  (if (and (integerp i) (integerp 27) (< i 27))
      (loop-simple (+ 1 i) (update-pp i pp))
      pp))

(local-defthmd loop-rewrite
  (equal (computeproduct-loop-0 i (multiplier) (mana) pp)
         (loop-simple i pp))
  :hints (("Goal" :in-theory (enable update-pp computeproduct-loop-0 loop-simple slc enc mux))))

(local-defthm update-noop
  (implies (not (= i j))
           (equal (ag j (update-pp i pp))
	          (ag j pp)))
  :hints (("Goal" :in-theory (enable update-pp))))

(local-defthm ag-update-nil
  (implies (and (natp i) (< i 27) pp)
           (equal (ag i (update-pp i pp))
	          (ag i (update-pp i ()))))
  :hints (("Goal" :in-theory (enable update-pp))))

(local-defthm prod-loop-1
  (implies (and (natp i)
                (natp j)
                (> j i))
           (equal (ag i (loop-simple j pp))
                  (ag i pp)))
  :hints (("goal" :in-theory (enable loop-simple))))

(local-defthm prod-loop-2
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (< i 27)
                (= (ag i pp) 0))
           (equal (ag i (loop-simple j pp))
                  (ag i (update-pp i ()))))
  :hints (("Goal" :in-theory (enable loop-simple))
          ("Subgoal *1/5" :cases ((= i j)))
          ("Subgoal *1/4" :cases ((= i j))
	                  :use (ag-update-nil)
			  :expand ((LOOP-SIMPLE i PP) (LOOP-SIMPLE i ()) (LOOP-SIMPLE J PP)))
          ("Subgoal *1/3" :cases ((= i j))
	                  :use (ag-update-nil)
			  :expand ((LOOP-SIMPLE i PP) (LOOP-SIMPLE i ()) (LOOP-SIMPLE J PP)))))

(local-in-theory (disable (loop-simple)))

(local-defthmd ag-pprod-update
  (implies (and (natp i)
                (< i 27))
           (equal (ag i (pprod))
                  (ag i (update-pp i ()))))
  :hints (("Goal" :in-theory (enable pprod loop-rewrite))))

(defthmd ash-rewrite
  (equal (ash i c)
         (fl (* (ifix i) (expt 2 c))))
  :hints (("goal" :in-theory (enable floor fl ash))))

(defthmd bvecp-mana
  (implies (not (specialp))
           (bvecp (mana) 52))
  :hints (("Goal" :in-theory (enable specialp manf dp)
                  :use (a-fields))))

(defthmd bvecp-manb
  (implies (not (specialp))
           (bvecp (manb) 52))
  :hints (("Goal" :in-theory (enable specialp manf dp)
                  :use (b-fields))))

(defthm integerp-mana
  (implies (not (specialp))
           (integerp (mana)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable specialp manf dp)
                  :use (a-fields))))

(defthm integerp-manb
  (implies (not (specialp))
           (integerp (manb)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable specialp manf dp)
                  :use (b-fields))))

(local-defthm bitn-multiplier
  (implies (and (not (specialp)) (natp j) (<= j 54))
           (equal (bitn (multiplier) j)
	          (bitn (manb) (1- j))))
  :hints (("Goal" :in-theory (enable ash-rewrite bitn-bits multiplier)
                  :use ((:instance bitn-shift-up (x (manb)) (k 1) (n (1- j)))))))

(local-defthm mux-bmux4p
  (implies (and (not (specialp)) (natp i) (< i 27))
           (equal (mux i) (bmux4p i (mana) (manb) 53)))
  :hints (("Goal" :in-theory (enable ash-rewrite bvecp bitn-bits mux enc slc bmux4p mag nbit)
                  :use (bvecp-mana
		        (:instance bitn-plus-bits (x (manb)) (n (1+ (* 2 i))) (m (1- (* 2 i))))
		        (:instance bitn-plus-bits (x (manb)) (n (* 2 i)) (m (1- (* 2 i))))))))

(local-defthmd pp-0-rewrite
  (implies (not (specialp))
           (equal (pp4p 0 (mana) (manb) 53)
	          (ag 0 (pprod))))
  :hints (("Goal" :in-theory (enable cat bitn-bits slc ag-pprod-update update-pp pp4p nbit bvecp)
                  :use (bvecp-mana bvecp-manb
		        (:instance bits-bounds (x (bmux4p 0 (mana) (manb) 53)) (i 52) (j 0))))))

(local-defthmd pp-i-rewrite
  (implies (and (not (specialp)) (not (zp i)) (< i 26))
           (equal (pp4p i (mana) (manb) 53)
	          (* (expt 2 (* 2 (1- i)))
		     (ag i (pprod)))))
  :hints (("Goal" :in-theory (enable cat bvecp bitn-bits slc ag-pprod-update update-pp pp4p nbit bvecp)
                  :use (bvecp-mana bvecp-manb
		        (:instance bvecp-member (x i) (n 5))
		        (:instance bitn-0-1 (x (manb)) (n (1- (* 2 i))))
		        (:instance bitn-0-1 (x (manb)) (n (1+ (* 2 i))))
		        (:instance bitn-0-1 (x (manb)) (n (* 2 i)))
		        (:instance bvecp-bmux4p (x (mana)) (y (manb)) (n 53))
		        (:instance bits-bounds (x (bmux4p i (mana) (manb) 53)) (i 52) (j 0))))))

(local-defthmd pp-26-rewrite
  (implies (not (specialp))
           (equal (pp4p 26 (mana) (manb) 53)
	          (+ (expt 2 106)
		     (* (expt 2 50)
		        (ag 26 (pprod))))))
  :hints (("Goal" :in-theory (enable cat bvecp bitn-bits slc ag-pprod-update update-pp pp4p nbit bvecp)
                  :use (bvecp-mana bvecp-manb
		        (:instance bvecp-member (x 26) (n 5))
		        (:instance bitn-0-1 (x (manb)) (n 51))
		        (:instance bitn-0-1 (x (manb)) (n 52))
		        (:instance bitn-0-1 (x (manb)) (n 53))
		        (:instance bvecp-bmux4p (i 26) (x (mana)) (y (manb)) (n 53))
		        (:instance bits-bounds (x (bmux4p 26 (mana) (manb) 53)) (i 52) (j 0))))))

(local-defun sum-pprod (m)
  (if (zp m)
      0
    (if (= m 1)
        (ag 0 (pprod))
      (+ (* (expt 2 (* 2 (- m 2)))
            (ag (1- m) (pprod)))
         (sum-pprod (1- m))))))

(local-in-theory (disable (sum-pprod)))

(local-defthm integerp-pprod
  (implies (and (natp i) (< i 27))
           (integerp (ag i (pprod))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable cat bvecp bitn-bits slc ag-pprod-update update-pp pp4p nbit bvecp)
                  :use (bvecp-mana bvecp-manb))))

(local-defthm integerp-sum-pprod
  (implies (and (natp i) (<= i 27))
           (integerp (sum-pprod i)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :induct (sum-pprod i))))

(local-defthmd sum-pp-pprod 
  (implies (and (not (specialp)) (natp m) (<= m 27))
           (equal (sum-pp4p (mana) (manb) m 53)
                  (if (= m 27)
                      (+ (expt 2 106) (sum-pprod m))
		    (sum-pprod m))))
  :hints (("Goal" :in-theory (enable pp-0-rewrite pp-i-rewrite pp-26-rewrite ))))

(local-defthmd sum-pp-pprod-27 
  (implies (not (specialp))
           (equal (sum-pp4p (mana) (manb) 27 53)
                  (+ (expt 2 106) (sum-pprod 27))))
  :hints (("Goal" :use ((:instance sum-pp-pprod (m 27))))))

(local-defthmd sum-pprod-rewrite 
  (implies (not (specialp))
           (equal (sum-pprod 27)
	          (+ (expt 2 106) (* (mana) (manb)))))                  
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-mana bvecp-manb sum-pp-pprod-27
                        (:instance booth4-corollary-3 (x (mana)) (y (manb)) (n 53) (m 27))))))

(defund sa ()
  (if (= (expa) 0)
      (mana)
    (+ (expt 2 52) (mana))))

(defund sb ()
  (if (= (expb) 0)
      (manb)
    (+ (expt 2 52) (manb))))

(in-theory (disable (sa) (sb)))

(local-defthmd sum-pprod-ia-ib
  (implies (not (specialp))
           (equal (+ (sum-pprod 27) (* (expt 2 52) (+ (ia) (ib))))
	          (+ (expt 2 106) (* (sa) (sb)))))                  
  :hints (("Goal" :in-theory (enable cat bvecp sum-pprod-rewrite sa sb ia ib)
                  :use (bvecp-mana bvecp-manb))))




(local-defund t2pp0s ()
  (logxor (logxor (ag 0 (pprod)) (ag 1 (pprod)))
          (bits (ash (ag 2 (pprod)) 2) 58 0)))

(local-defund t1pp0c ()
  (logior (logior (logand (ag 0 (pprod)) (ag 1 (pprod)))
                  (logand (ag 0 (pprod)) (bits (ash (ag 2 (pprod)) 2) 58 0)))
          (logand (ag 1 (pprod)) (bits (ash (ag 2 (pprod)) 2) 58 0))))

(local-defund t2pp1s ()
  (logxor (logxor (ag 3 (pprod)) (bits (ash (ag 4 (pprod)) 2) 60 0))
          (bits (ash (ag 5 (pprod)) 4) 60 0)))
	  
(local-defund t1pp1c ()
  (logior (logior (logand (ag 3 (pprod)) (bits (ash (ag 4 (pprod)) 2) 60 0)) 
                  (logand (ag 3 (pprod)) (bits (ash (ag 5 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 4 (pprod)) 2) 60 0) (bits (ash (ag 5 (pprod)) 4) 60 0))))

(local-defund t2pp2s ()
  (logxor (logxor (ag 6 (pprod)) (bits (ash (ag 7 (pprod)) 2) 60 0))
          (bits (ash (ag 8 (pprod)) 4) 60 0)))
	  
(local-defund t1pp2c ()
  (logior (logior (logand (ag 6 (pprod)) (bits (ash (ag 7 (pprod)) 2) 60 0))
                  (logand (ag 6 (pprod)) (bits (ash (ag 8 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 7 (pprod)) 2) 60 0) (bits (ash (ag 8 (pprod)) 4) 60 0))))

(local-defund t2pp3s ()
  (logxor (logxor (ag 9 (pprod)) (bits (ash (ag 10 (pprod)) 2) 60 0))
          (bits (ash (ag 11 (pprod)) 4) 60 0)))
	  
(local-defund t1pp3c ()
  (logior (logior (logand (ag 9 (pprod)) (bits (ash (ag 10 (pprod)) 2) 60 0))
                  (logand (ag 9 (pprod)) (bits (ash (ag 11 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 10 (pprod)) 2) 60 0) (bits (ash (ag 11 (pprod)) 4) 60 0))))

(local-defund t2pp4s ()
  (logxor (logxor (ag 12 (pprod)) (bits (ash (ag 13 (pprod)) 2) 60 0))
          (bits (ash (ag 14 (pprod)) 4) 60 0)))
	  
(local-defund t1pp4c ()
  (logior (logior (logand (ag 12 (pprod)) (bits (ash (ag 13 (pprod)) 2) 60 0))
                  (logand (ag 12 (pprod)) (bits (ash (ag 14 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 13 (pprod)) 2) 60 0) (bits (ash (ag 14 (pprod)) 4) 60 0))))

(local-defund t2pp5s ()
  (logxor (logxor (ag 15 (pprod)) (bits (ash (ag 16 (pprod)) 2) 60 0))
          (bits (ash (ag 17 (pprod)) 4) 60 0)))
	  
(local-defund t1pp5c ()
  (logior (logior (logand (ag 15 (pprod)) (bits (ash (ag 16 (pprod)) 2) 60 0))
                  (logand (ag 15 (pprod)) (bits (ash (ag 17 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 16 (pprod)) 2) 60 0) (bits (ash (ag 17 (pprod)) 4) 60 0))))

(local-defund t2pp6s ()
  (logxor (logxor (ag 18 (pprod)) (bits (ash (ag 19 (pprod)) 2) 60 0))
          (bits (ash (ag 20 (pprod)) 4) 60 0)))
	  
(local-defund t1pp6c ()
  (logior (logior (logand (ag 18 (pprod)) (bits (ash (ag 19 (pprod)) 2) 60 0))
                  (logand (ag 18 (pprod)) (bits (ash (ag 20 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 19 (pprod)) 2) 60 0)  (bits (ash (ag 20 (pprod)) 4) 60 0))))

(local-defund t2pp7s ()
  (logxor (logxor (ag 21 (pprod)) (bits (ash (ag 22 (pprod)) 2) 60 0))
          (bits (ash (ag 23 (pprod)) 4) 60 0)))

(local-defund t1pp7c ()
  (logior (logior (logand (ag 21 (pprod)) (bits (ash (ag 22 (pprod)) 2) 60 0))
                  (logand (ag 21 (pprod)) (bits (ash (ag 23 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 22 (pprod)) 2) 60 0) (bits (ash (ag 23 (pprod)) 4) 60 0))))

(local-defund t2pp8s ()
  (logxor (logxor (ag 24 (pprod)) (bits (ash (ag 25 (pprod)) 2) 60 0))
          (bits (ash (ag 26 (pprod)) 4) 60 0)))

(local-defund t1pp8c ()
  (logior (logior (logand (ag 24 (pprod)) (bits (ash (ag 25 (pprod)) 2) 60 0))
                  (logand (ag 24 (pprod)) (bits (ash (ag 26 (pprod)) 4) 60 0)))
          (logand (bits (ash (ag 25 (pprod)) 2) 60 0) (bits (ash (ag 26 (pprod)) 4) 60 0))))

(local-defund t3pp0s ()
  (logxor (logxor (t1pp0c) (bits (ash (t1pp1c) 4) 70 0))
          (bits (ash (t1pp2c) 10) 70 0)))

(local-defund t2pp0c ()
  (logior (logior (logand (t1pp0c) (bits (ash (t1pp1c) 4) 70 0))
                  (logand (t1pp0c) (bits (ash (t1pp2c) 10) 70 0)))
          (logand (bits (ash (t1pp1c) 4) 70 0) (bits (ash (t1pp2c) 10) 70 0))))

(local-defund t3pp1s ()
  (logxor (logxor (t1pp3c) (bits (ash (t1pp4c) 6) 72 0))
          (bits (ash (t1pp5c) 12) 72 0)))

(local-defund t2pp1c ()
  (logior (logior (logand (t1pp3c) (bits (ash (t1pp4c) 6) 72 0))
                  (logand (t1pp3c) (bits (ash (t1pp5c) 12) 72 0)))
          (logand (bits (ash (t1pp4c) 6) 72 0) (bits (ash (t1pp5c) 12) 72 0))))

(local-defund t3pp2s ()
  (logxor (logxor (t1pp6c) (bits (ash (t1pp7c) 6) 72 0))
          (bits (ash (t1pp8c) 12) 72 0)))

(local-defund t2pp2c ()
  (logior (logior (logand (t1pp6c) (bits (ash (t1pp7c) 6) 72 0))
                  (logand (t1pp6c) (bits (ash (t1pp8c) 12) 72 0)))
          (logand (bits (ash (t1pp7c) 6) 72 0) (bits (ash (t1pp8c) 12) 72 0))))

(local-defund t4pp0s ()
  (logxor (logxor (t2pp0s) (bits (ash (t2pp1s) 4) 70 0))
          (bits (ash (t2pp2s) 10) 70 0)))

(local-defund t3pp0c ()
  (logior (logior (logand (t2pp0s) (bits (ash (t2pp1s) 4) 70 0))
                  (logand (t2pp0s) (bits (ash (t2pp2s) 10) 70 0)))
          (logand (bits (ash (t2pp1s) 4) 70 0) (bits (ash (t2pp2s) 10) 70 0))))

(local-defund t4pp1s ()
  (logxor (logxor (t2pp3s) (bits (ash (t2pp4s) 6) 72 0))
          (bits (ash (t2pp5s) 12) 72 0)))

(local-defund t3pp1c ()
  (logior (logior (logand (t2pp3s) (bits (ash (t2pp4s) 6) 72 0))
                  (logand (t2pp3s) (bits (ash (t2pp5s) 12) 72 0)))
          (logand (bits (ash (t2pp4s) 6) 72 0) (bits (ash (t2pp5s) 12) 72 0))))

(local-defund t4pp2s ()
  (logxor (logxor (t2pp6s) (bits (ash (t2pp7s) 6) 72 0))
          (bits (ash (t2pp8s) 12) 72 0)))

(local-defund t3pp2c ()
  (logior (logior (logand (t2pp6s) (bits (ash (t2pp7s) 6) 72 0))
                  (logand (t2pp6s) (bits (ash (t2pp8s) 12) 72 0)))
          (logand (bits (ash (t2pp7s) 6) 72 0) (bits (ash (t2pp8s) 12) 72 0))))

(local-defund t4pp3s ()
  (logxor (logxor (t2pp0c) (bits (ash (t2pp1c) 16) 106 0))
          (bits (ash (t2pp2c) 34) 106 0)))

(local-defund t3pp3c ()
  (logior (logior (logand (t2pp0c) (bits (ash (t2pp1c) 16) 106 0))
                  (logand (t2pp0c) (bits (ash (t2pp2c) 34) 106 0)))
          (logand (bits (ash (t2pp1c) 16) 106 0) (bits (ash (t2pp2c) 34) 106 0))))

(local-defund t5pp0s ()
  (logxor (logxor (t3pp0s) (bits (ash (t3pp1s) 16) 106 0))
          (bits (ash (t3pp2s) 34) 106 0)))

(local-defund t4pp0c ()
  (logior (logior (logand (t3pp0s) (bits (ash (t3pp1s) 16) 106 0))
                  (logand (t3pp0s) (bits (ash (t3pp2s) 34) 106 0)))
          (logand (bits (ash (t3pp1s) 16) 106 0) (bits (ash (t3pp2s) 34) 106 0))))

(local-defund t5pp1s ()
  (logxor (logxor (t3pp0c) (bits (ash (t3pp1c) 16) 106 0))
          (bits (ash (t3pp2c) 34) 106 0)))

(local-defund t4pp1c ()
  (logior (logior (logand (t3pp0c) (bits (ash (t3pp1c) 16) 106 0))
                  (logand (t3pp0c) (bits (ash (t3pp2c) 34) 106 0)))
          (logand (bits (ash (t3pp1c) 16) 106 0) (bits (ash (t3pp2c) 34) 106 0))))

(local-defund t4pp4s ()
  (logxor (logxor (bits (ash (ia) 49) 106 0) (bits (ash (ib) 49) 106 0))
          (t3pp3c)))

(local-defund t4pp2c ()
  (logior (logior (logand (bits (ash (ia) 49) 106 0) (bits (ash (ib) 49) 106 0))
                  (logand (bits (ash (ia) 49) 106 0) (t3pp3c)))
          (logand (bits (ash (ib) 49) 106 0) (t3pp3c))))

(local-defund t6pp0s ()
  (logxor (logxor (bits (ash (t4pp2c) 2) 108 0) (t4pp1c))
          (t4pp0c)))

(local-defund t5pp0c ()
  (logior (logior (logand (bits (ash (t4pp2c) 2) 108 0) (t4pp1c))
                  (logand (bits (ash (t4pp2c) 2) 108 0) (t4pp0c)))
          (logand (t4pp1c) (t4pp0c))))

(local-defund t6pp1s ()
  (logxor (logxor (bits (ash (t4pp4s) 3) 109 0) (t4pp0s))
          (bits (ash (t4pp1s) 16) 109 0)))

(local-defund t5pp1c ()
  (logior (logior (logand (bits (ash (t4pp4s) 3) 109 0) (t4pp0s))
                  (logand (bits (ash (t4pp4s) 3) 109 0) (bits (ash (t4pp1s) 16) 109 0)))
          (logand (t4pp0s) (bits (ash (t4pp1s) 16) 109 0))))

(local-defund t7pp0s ()
  (logxor (logxor (t5pp0s) (t5pp1s))
          (bits (ash (t5pp0c) 2) 110 0)))

(local-defund t6pp0c ()
  (logior (logior (logand (t5pp0s) (t5pp1s))
                  (logand (t5pp0s) (bits (ash (t5pp0c) 2) 110 0)))
          (logand (t5pp1s) (bits (ash (t5pp0c) 2) 110 0))))

(local-defund t6pp2s ()
  (logxor (logxor (bits (ash (t4pp2s) 33) 109 0) (bits (ash (t4pp3s) 1) 109 0))
          (t5pp1c)))

(local-defund t6pp1c ()
  (logior (logior (logand (bits (ash (t4pp2s) 33) 109 0) (bits (ash (t4pp3s) 1) 109 0))
                  (logand (bits (ash (t4pp2s) 33) 109 0) (t5pp1c)))
          (logand (bits (ash (t4pp3s) 1) 109 0) (t5pp1c))))

(local-defund t8pp0s ()
  (logxor (logxor (bits (ash (t6pp0s) 2) 110 0) (t6pp1s))
          (bits (ash (t6pp2s) 1) 110 0)))

(local-defund t7pp0c ()
  (logior (logior (logand (bits (ash (t6pp0s) 2) 110 0) (t6pp1s))
                  (logand (bits (ash (t6pp0s) 2) 110 0) (bits (ash (t6pp2s) 1) 110 0)))
          (logand (t6pp1s) (bits (ash (t6pp2s) 1) 110 0))))

(local-defund t9pp0s ()
  (logxor (logxor (t7pp0s) (t7pp0c))
          (bits (ash (t6pp0c) 1) 111 0)))

(local-defund t7pp1c ()
  (logior (logior (logand (t7pp0s) (t7pp0c))
                  (logand (t7pp0s) (bits (ash (t6pp0c) 1) 111 0)))
          (logand (t7pp0c) (bits (ash (t6pp0c) 1) 111 0))))

(local-defund t9pp1s ()
  (logxor (logxor (bits (ash (t7pp1c) 2) 113 0) (bits (ash (t6pp1c) 2) 113 0))
          (t8pp0s)))

(local-defund t9pp0c ()
  (logior (logior (logand (bits (ash (t7pp1c) 2) 113 0) (bits (ash (t6pp1c) 2) 113 0)) 
                  (logand (bits (ash (t7pp1c) 2) 113 0) (t8pp0s)))
          (logand (bits (ash (t6pp1c) 2) 113 0) (t8pp0s))))

(local-defund ppa* ()
  (bits (logxor (logxor (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                (bits (ash (t9pp0c) 1) 114 0))
        105 0))

(local-defund ppb* ()
  (bits (bits (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                   (logand (bits (ash (t9pp0s) 1) 114 0) (bits (ash (t9pp0c) 1) 114 0)))
                           (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                   1)
              115 0)
	105 0))

(local-defthmd compress-lemma
  (and (equal (ppa) (ppa*))
       (equal (ppb) (ppb*)))
  :hints (("goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(t2pp0s t1pp0c t2pp1s t1pp1c t2pp2s t1pp2c t2pp3s t1pp3c t2pp4s t1pp4c t2pp5s t1pp5c t2pp6s t1pp6c
	                t2pp7s t1pp7c t2pp8s t1pp8c t3pp0s t2pp0c t3pp1s t2pp1c t3pp2s t2pp2c t4pp0s t3pp0c t4pp1s t3pp1c t4pp2s
			t3pp2c t4pp3s t3pp3c t5pp0s t4pp0c t5pp1s t4pp1c t4pp4s t4pp2c t6pp0s t5pp0c t6pp1s t5pp1c t7pp0s t6pp0c
			t6pp2s t6pp1c t8pp0s t7pp0c t9pp0s t7pp1c t9pp1s t9pp0c ppa* ppb* compress ppa ppb))))

(local-in-theory (disable (t2pp0s) (t1pp0c) (t2pp1s) (t1pp1c) (t2pp2s) (t1pp2c) (t2pp3s) (t1pp3c) (t2pp4s) (t1pp4c) (t2pp5s) (t1pp5c)
                    (t2pp6s) (t1pp6c) (t2pp7s) (t1pp7c) (t2pp8s) (t1pp8c) (t3pp0s) (t2pp0c) (t3pp1s) (t2pp1c) (t3pp2s) (t2pp2c)
		    (t4pp0s) (t3pp0c) (t4pp1s) (t3pp1c) (t4pp2s) (t3pp2c) (t4pp3s) (t3pp3c) (t5pp0s) (t4pp0c) (t5pp1s) (t4pp1c)
		    (t4pp4s) (t4pp2c) (t6pp0s) (t5pp0c) (t6pp1s) (t5pp1c) (t7pp0s) (t6pp0c) (t6pp2s) (t6pp1c) (t8pp0s) (t7pp0c)
		    (t9pp0s) (t7pp1c) (t9pp1s) (t9pp0c) (ppa*) (ppb*)))

(local-defthmd comp-1
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (ag 0 (pprod))
		     (ag 1 (pprod))
		     (* (expt 4 1) (ag 2 (pprod)))
		     (* (expt 4 2) (ag 3 (pprod)))
		     (* (expt 4 3) (ag 4 (pprod)))
		     (* (expt 4 4) (ag 5 (pprod)))
		     (* (expt 4 5) (ag 6 (pprod)))
		     (* (expt 4 6) (ag 7 (pprod)))
		     (* (expt 4 7) (ag 8 (pprod)))
		     (* (expt 4 8) (ag 9 (pprod)))
		     (* (expt 4 9) (ag 10 (pprod)))
		     (* (expt 4 10) (ag 11 (pprod)))
		     (* (expt 4 11) (ag 12 (pprod)))
		     (* (expt 4 12) (ag 13 (pprod)))
		     (* (expt 4 13) (ag 14 (pprod)))
		     (* (expt 4 14) (ag 15 (pprod)))
		     (* (expt 4 15) (ag 16 (pprod)))
		     (* (expt 4 16) (ag 17 (pprod)))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (sum-pprod-ia-ib) :expand ((:free (m) (sum-pprod m))))))

(local-defthmd bvecp-pprod
  (implies (and (natp i) (< i 27))
           (bvecp (ag i (pprod)) 57))
  :hints (("Goal" :in-theory (enable ag-pprod-update update-pp))))

(local-defthmd bvecp-pprod-26
  (bvecp (ag 26 (pprod)) 56)
  :hints (("Goal" :in-theory (enable cat-0 ag-pprod-update update-pp))))

(defthm integerp-sa
  (implies (not (specialp))
           (integerp (sa)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable sa) :use (bvecp-mana))))

(defthm integerp-sb
  (implies (not (specialp))
           (integerp (sb)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable sb) :use (bvecp-manb))))

(local-defthmd comp-2
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 4 2) (ag 3 (pprod)))
		     (* (expt 4 3) (ag 4 (pprod)))
		     (* (expt 4 4) (ag 5 (pprod)))
		     (* (expt 4 5) (ag 6 (pprod)))
		     (* (expt 4 6) (ag 7 (pprod)))
		     (* (expt 4 7) (ag 8 (pprod)))
		     (* (expt 4 8) (ag 9 (pprod)))
		     (* (expt 4 9) (ag 10 (pprod)))
		     (* (expt 4 10) (ag 11 (pprod)))
		     (* (expt 4 11) (ag 12 (pprod)))
		     (* (expt 4 12) (ag 13 (pprod)))
		     (* (expt 4 13) (ag 14 (pprod)))
		     (* (expt 4 14) (ag 15 (pprod)))
		     (* (expt 4 15) (ag 16 (pprod)))
		     (* (expt 4 16) (ag 17 (pprod)))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-1
                        (:instance bvecp-pprod (i 0))
                        (:instance bvecp-pprod (i 1))
                        (:instance bvecp-pprod (i 2))
                        (:instance add-3 (x (ag 0 (pprod)))
			                 (y (ag 1 (pprod)))
					 (z (* 4 (ag 2 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp0s t1pp0c))))

(local-defthmd comp-3
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* 16 (t2pp1s))
		     (* 32 (t1pp1c))
		     (* (expt 4 5) (ag 6 (pprod)))
		     (* (expt 4 6) (ag 7 (pprod)))
		     (* (expt 4 7) (ag 8 (pprod)))
		     (* (expt 4 8) (ag 9 (pprod)))
		     (* (expt 4 9) (ag 10 (pprod)))
		     (* (expt 4 10) (ag 11 (pprod)))
		     (* (expt 4 11) (ag 12 (pprod)))
		     (* (expt 4 12) (ag 13 (pprod)))
		     (* (expt 4 13) (ag 14 (pprod)))
		     (* (expt 4 14) (ag 15 (pprod)))
		     (* (expt 4 15) (ag 16 (pprod)))
		     (* (expt 4 16) (ag 17 (pprod)))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-2
                        (:instance bvecp-pprod (i 3))
                        (:instance bvecp-pprod (i 4))
                        (:instance bvecp-pprod (i 5))
                        (:instance add-3 (x (ag 3 (pprod)))
			                 (y (* 4 (ag 4 (pprod))))
					 (z (* 16 (ag 5 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp1s t1pp1c))))

(local-defthmd comp-4
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* 16 (t2pp1s))
		     (* 32 (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 4 8) (ag 9 (pprod)))
		     (* (expt 4 9) (ag 10 (pprod)))
		     (* (expt 4 10) (ag 11 (pprod)))
		     (* (expt 4 11) (ag 12 (pprod)))
		     (* (expt 4 12) (ag 13 (pprod)))
		     (* (expt 4 13) (ag 14 (pprod)))
		     (* (expt 4 14) (ag 15 (pprod)))
		     (* (expt 4 15) (ag 16 (pprod)))
		     (* (expt 4 16) (ag 17 (pprod)))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-3
                        (:instance bvecp-pprod (i 6))
                        (:instance bvecp-pprod (i 7))
                        (:instance bvecp-pprod (i 8))
                        (:instance add-3 (x (ag 6 (pprod)))
			                 (y (* 4 (ag 7 (pprod))))
					 (z (* 16 (ag 8 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp2s t1pp2c))))

(local-defthmd comp-5
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 5) (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 4 11) (ag 12 (pprod)))
		     (* (expt 4 12) (ag 13 (pprod)))
		     (* (expt 4 13) (ag 14 (pprod)))
		     (* (expt 4 14) (ag 15 (pprod)))
		     (* (expt 4 15) (ag 16 (pprod)))
		     (* (expt 4 16) (ag 17 (pprod)))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-4
                        (:instance bvecp-pprod (i 9))
                        (:instance bvecp-pprod (i 10))
                        (:instance bvecp-pprod (i 11))
                        (:instance add-3 (x (ag 9 (pprod)))
			                 (y (* 4 (ag 10 (pprod))))
					 (z (* 16 (ag 11 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp3s t1pp3c))))

(local-defthmd comp-6
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 5) (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 23) (t1pp4c))
		     (* (expt 4 14) (ag 15 (pprod)))
		     (* (expt 4 15) (ag 16 (pprod)))
		     (* (expt 4 16) (ag 17 (pprod)))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-5
                        (:instance bvecp-pprod (i 12))
                        (:instance bvecp-pprod (i 13))
                        (:instance bvecp-pprod (i 14))
                        (:instance add-3 (x (ag 12 (pprod)))
			                 (y (* 4 (ag 13 (pprod))))
					 (z (* 16 (ag 14 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp4s t1pp4c))))

(local-defthmd comp-7
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 5) (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 23) (t1pp4c))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 29) (t1pp5c))
		     (* (expt 4 17) (ag 18 (pprod)))
		     (* (expt 4 18) (ag 19 (pprod)))
		     (* (expt 4 19) (ag 20 (pprod)))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-6
                        (:instance bvecp-pprod (i 15))
                        (:instance bvecp-pprod (i 16))
                        (:instance bvecp-pprod (i 17))
                        (:instance add-3 (x (ag 15 (pprod)))
			                 (y (* 4 (ag 16 (pprod))))
					 (z (* 16 (ag 17 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp5s t1pp5c))))

(local-defthmd comp-8
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 5) (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 23) (t1pp4c))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 29) (t1pp5c))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 35) (t1pp6c))
		     (* (expt 4 20) (ag 21 (pprod)))
		     (* (expt 4 21) (ag 22 (pprod)))
		     (* (expt 4 22) (ag 23 (pprod)))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-7
                        (:instance bvecp-pprod (i 18))
                        (:instance bvecp-pprod (i 19))
                        (:instance bvecp-pprod (i 20))
                        (:instance add-3 (x (ag 18 (pprod)))
			                 (y (* 4 (ag 19 (pprod))))
					 (z (* 16 (ag 20 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp6s t1pp6c))))

(local-defthmd comp-9
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 5) (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 23) (t1pp4c))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 29) (t1pp5c))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 35) (t1pp6c))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 41) (t1pp7c))
		     (* (expt 4 23) (ag 24 (pprod)))
		     (* (expt 4 24) (ag 25 (pprod)))
		     (* (expt 4 25) (ag 26 (pprod)))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-8
                        (:instance bvecp-pprod (i 21))
                        (:instance bvecp-pprod (i 22))
                        (:instance bvecp-pprod (i 23))
                        (:instance add-3 (x (ag 21 (pprod)))
			                 (y (* 4 (ag 22 (pprod))))
					 (z (* 16 (ag 23 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp7s t1pp7c))))

(local-defthmd comp-10
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (t2pp0s)
		     (* 2 (t1pp0c))
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 5) (t1pp1c))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 11) (t1pp2c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 23) (t1pp4c))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 29) (t1pp5c))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 35) (t1pp6c))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 41) (t1pp7c))
		     (* (expt 2 46) (t2pp8s))
		     (* (expt 2 47) (t1pp8c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-9
                        (:instance bvecp-pprod (i 24))
                        (:instance bvecp-pprod (i 25))
                        (:instance bvecp-pprod (i 26))
                        (:instance add-3 (x (ag 24 (pprod)))
			                 (y (* 4 (ag 25 (pprod))))
					 (z (* 16 (ag 26 (pprod))))))
		  :in-theory (enable bvecp ash-rewrite t2pp8s t1pp8c))))

(local-defthmd bvecp-t2pp0s
  (bvecp (t2pp0s) 59)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 0))
                        (:instance bvecp-pprod (i 1))
                        (:instance bvecp-pprod (i 2)))
		  :in-theory (enable t2pp0s bvecp))))

(local-defthmd bvecp-t1pp0c
  (bvecp (t1pp0c) 59)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 0))
                        (:instance bvecp-pprod (i 1))
                        (:instance bvecp-pprod (i 2)))
		  :in-theory (enable t1pp0c bvecp))))

(local-defthmd bvecp-t2pp1s
  (bvecp (t2pp1s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 3))
                        (:instance bvecp-pprod (i 4))
                        (:instance bvecp-pprod (i 5)))
		  :in-theory (enable t2pp1s bvecp))))

(local-defthmd bvecp-t1pp1c
  (bvecp (t1pp1c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 3))
                        (:instance bvecp-pprod (i 4))
                        (:instance bvecp-pprod (i 5)))
		  :in-theory (enable t1pp1c bvecp))))

(local-defthmd bvecp-t2pp2s
  (bvecp (t2pp2s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 6))
                        (:instance bvecp-pprod (i 7))
                        (:instance bvecp-pprod (i 8)))
		  :in-theory (enable t2pp2s bvecp))))

(local-defthmd bvecp-t1pp2c
  (bvecp (t1pp2c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 6))
                        (:instance bvecp-pprod (i 7))
                        (:instance bvecp-pprod (i 8)))
		  :in-theory (enable t1pp2c bvecp))))

(local-defthmd bvecp-t2pp3s
  (bvecp (t2pp3s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 9))
                        (:instance bvecp-pprod (i 10))
                        (:instance bvecp-pprod (i 11)))
		  :in-theory (enable t2pp3s bvecp))))

(local-defthmd bvecp-t1pp3c
  (bvecp (t1pp3c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 9))
                        (:instance bvecp-pprod (i 10))
                        (:instance bvecp-pprod (i 11)))
		  :in-theory (enable t1pp3c bvecp))))

(local-defthmd bvecp-t2pp4s
  (bvecp (t2pp4s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 12))
                        (:instance bvecp-pprod (i 13))
                        (:instance bvecp-pprod (i 14)))
		  :in-theory (enable t2pp4s bvecp))))

(local-defthmd bvecp-t1pp4c
  (bvecp (t1pp4c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 12))
                        (:instance bvecp-pprod (i 13))
                        (:instance bvecp-pprod (i 14)))
		  :in-theory (enable t1pp4c bvecp))))

(local-defthmd bvecp-t2pp5s
  (bvecp (t2pp5s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 15))
                        (:instance bvecp-pprod (i 16))
                        (:instance bvecp-pprod (i 17)))
		  :in-theory (enable t2pp5s bvecp))))

(local-defthmd bvecp-t1pp5c
  (bvecp (t1pp5c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 15))
                        (:instance bvecp-pprod (i 16))
                        (:instance bvecp-pprod (i 17)))
		  :in-theory (enable t1pp5c bvecp))))

(local-defthmd bvecp-t2pp6s
  (bvecp (t2pp6s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 18))
                        (:instance bvecp-pprod (i 19))
                        (:instance bvecp-pprod (i 20)))
		  :in-theory (enable t2pp6s bvecp))))

(local-defthmd bvecp-t1pp6c
  (bvecp (t1pp6c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 18))
                        (:instance bvecp-pprod (i 19))
                        (:instance bvecp-pprod (i 20)))
		  :in-theory (enable t1pp6c bvecp))))

(local-defthmd bvecp-t2pp7s
  (bvecp (t2pp7s) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 21))
                        (:instance bvecp-pprod (i 22))
                        (:instance bvecp-pprod (i 23)))
		  :in-theory (enable t2pp7s bvecp))))

(local-defthmd bvecp-t1pp7c
  (bvecp (t1pp7c) 61)
  :hints (("Goal" :use ((:instance bvecp-pprod (i 21))
                        (:instance bvecp-pprod (i 22))
                        (:instance bvecp-pprod (i 23)))
		  :in-theory (enable t1pp7c bvecp))))

(local-defthmd bvecp-t2pp8s
  (bvecp (t2pp8s) 60)
  :hints (("Goal" :use (bvecp-pprod-26
                        (:instance bvecp-pprod (i 24))
                        (:instance bvecp-pprod (i 25)))
		  :in-theory (enable ash-rewrite t2pp8s bvecp))))

(local-defthmd bvecp-t1pp8c
  (bvecp (t1pp8c) 60)
  :hints (("Goal" :use (bvecp-pprod-26
                        (:instance bvecp-pprod (i 24))
                        (:instance bvecp-pprod (i 25)))
		  :in-theory (enable t1pp8c ash-rewrite bvecp))))

(local-defthmd comp-11
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 2) (t2pp0c))
                     (t2pp0s)
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 17) (t1pp3c))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 23) (t1pp4c))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 29) (t1pp5c))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 35) (t1pp6c))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 41) (t1pp7c))
		     (* (expt 2 46) (t2pp8s))
		     (* (expt 2 47) (t1pp8c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-10 bvecp-t1pp0c bvecp-t1pp1c bvecp-t1pp2c
                        (:instance add-3 (x (t1pp0c))
			                 (y (* (expt 2 4) (t1pp1c)))
					 (z (* (expt 2 10) (t1pp2c)))))
		  :in-theory (enable bvecp ash-rewrite t3pp0s t2pp0c))))

(local-defthmd comp-12
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 2) (t2pp0c))
		     (* (expt 2 17) (t3pp1s))
		     (* (expt 2 18) (t2pp1c))
                     (t2pp0s)
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 35) (t1pp6c))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 41) (t1pp7c))
		     (* (expt 2 46) (t2pp8s))
		     (* (expt 2 47) (t1pp8c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-11 bvecp-t1pp4c bvecp-t1pp5c bvecp-t1pp3c
                        (:instance add-3 (x (t1pp3c))
			                 (y (* (expt 2 6) (t1pp4c)))
					 (z (* (expt 2 12) (t1pp5c)))))
		  :in-theory (enable bvecp ash-rewrite t3pp1s t2pp1c))))

(local-defthmd comp-13
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 2) (t2pp0c))
		     (* (expt 2 17) (t3pp1s))
		     (* (expt 2 18) (t2pp1c))
		     (* (expt 2 35) (t3pp2s))
		     (* (expt 2 36) (t2pp2c))
                     (t2pp0s)
		     (* (expt 2 4) (t2pp1s))
		     (* (expt 2 10) (t2pp2s))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 46) (t2pp8s))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-12 bvecp-t1pp6c bvecp-t1pp7c bvecp-t1pp8c
                        (:instance add-3 (x (t1pp6c))
			                 (y (* (expt 2 6) (t1pp7c)))
					 (z (* (expt 2 12) (t1pp8c)))))
		  :in-theory (enable bvecp ash-rewrite t3pp2s t2pp2c))))

(local-defthmd bvecp-t3pp0s
  (bvecp (t3pp0s) 71)
  :hints (("Goal" :use (bvecp-t1pp0c bvecp-t1pp1c bvecp-t1pp2c)
		  :in-theory (enable t3pp0s bvecp))))

(local-defthmd bvecp-t2pp0c
  (bvecp (t2pp0c) 71)
  :hints (("Goal" :use (bvecp-t1pp0c bvecp-t1pp1c bvecp-t1pp2c)
		  :in-theory (enable t2pp0c bvecp))))

(local-defthmd bvecp-t3pp1s
  (bvecp (t3pp1s) 73)
  :hints (("Goal" :use (bvecp-t1pp3c bvecp-t1pp4c bvecp-t1pp5c)
		  :in-theory (enable t3pp1s bvecp))))

(local-defthmd bvecp-t2pp1c
  (bvecp (t2pp1c) 73)
  :hints (("Goal" :use (bvecp-t1pp3c bvecp-t1pp4c bvecp-t1pp5c)
		  :in-theory (enable t2pp1c bvecp))))

(local-defthmd bvecp-t3pp2s
  (bvecp (t3pp2s) 73)
  :hints (("Goal" :use (bvecp-t1pp6c bvecp-t1pp7c bvecp-t1pp8c)
		  :in-theory (enable t3pp2s bvecp))))

(local-defthmd bvecp-t2pp2c
  (bvecp (t2pp2c) 72)
  :hints (("Goal" :use (bvecp-t1pp6c bvecp-t1pp7c bvecp-t1pp8c)
		  :in-theory (enable t2pp2c ash-rewrite bvecp))))

(local-defthmd comp-14
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 2) (t2pp0c))
		     (* (expt 2 17) (t3pp1s))
		     (* (expt 2 18) (t2pp1c))
		     (* (expt 2 35) (t3pp2s))
		     (* (expt 2 36) (t2pp2c))
		     (t4pp0s)
		     (* 2 (t3pp0c))
		     (* (expt 2 16) (t2pp3s))
		     (* (expt 2 22) (t2pp4s))
		     (* (expt 2 28) (t2pp5s))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 46) (t2pp8s))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-13 bvecp-t2pp0s bvecp-t2pp1s bvecp-t2pp2s
                        (:instance add-3 (x (t2pp0s))
			                 (y (* (expt 2 4) (t2pp1s)))
					 (z (* (expt 2 10) (t2pp2s)))))
		  :in-theory (enable bvecp ash-rewrite t4pp0s t3pp0c))))

(local-defthmd comp-15
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 2) (t2pp0c))
		     (* (expt 2 17) (t3pp1s))
		     (* (expt 2 18) (t2pp1c))
		     (* (expt 2 35) (t3pp2s))
		     (* (expt 2 36) (t2pp2c))
		     (t4pp0s)
		     (* 2 (t3pp0c))
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 17) (t3pp1c))
		     (* (expt 2 34) (t2pp6s))
		     (* (expt 2 40) (t2pp7s))
		     (* (expt 2 46) (t2pp8s))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-14 bvecp-t2pp3s bvecp-t2pp4s bvecp-t2pp5s
                        (:instance add-3 (x (t2pp3s))
			                 (y (* (expt 2 6) (t2pp4s)))
					 (z (* (expt 2 12) (t2pp5s)))))
		  :in-theory (enable bvecp ash-rewrite t4pp1s t3pp1c))))

(local-defthmd comp-16
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 2) (t2pp0c))
		     (* (expt 2 17) (t3pp1s))
		     (* (expt 2 18) (t2pp1c))
		     (* (expt 2 35) (t3pp2s))
		     (* (expt 2 36) (t2pp2c))
		     (t4pp0s)
		     (* 2 (t3pp0c))
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 17) (t3pp1c))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 35) (t3pp2c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-15 bvecp-t2pp6s bvecp-t2pp7s bvecp-t2pp8s
                        (:instance add-3 (x (t2pp6s))
			                 (y (* (expt 2 6) (t2pp7s)))
					 (z (* (expt 2 12) (t2pp8s)))))
		  :in-theory (enable bvecp ash-rewrite t4pp2s t3pp2c))))

(local-defthmd comp-17
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t3pp0s))
		     (* (expt 2 17) (t3pp1s))
		     (* (expt 2 35) (t3pp2s))
		     (t4pp0s)
		     (* 2 (t3pp0c))
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 17) (t3pp1c))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 35) (t3pp2c))
		     (* (expt 2 2) (t4pp3s))
		     (* (expt 2 3) (t3pp3c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-16 bvecp-t2pp0c bvecp-t2pp1c bvecp-t2pp2c
                        (:instance add-3 (x (t2pp0c))
			                 (y (* (expt 2 16) (t2pp1c)))
					 (z (* (expt 2 34) (t2pp2c)))))
		  :in-theory (enable bvecp ash-rewrite t4pp3s t3pp3c))))

(local-defthmd bvecp-t4pp0s
  (bvecp (t4pp0s) 73)
  :hints (("Goal" :use (bvecp-t2pp0s bvecp-t2pp1s bvecp-t2pp2s)
		  :in-theory (enable t4pp0s ash-rewrite bvecp))))

(local-defthmd bvecp-t3pp0c
  (bvecp (t3pp0c) 73)
  :hints (("Goal" :use (bvecp-t2pp0s bvecp-t2pp1s bvecp-t2pp2s)
                  :in-theory (enable t3pp0c ash-rewrite bvecp))))

(local-defthmd bvecp-t4pp1s
  (bvecp (t4pp1s) 73)
  :hints (("Goal" :use (bvecp-t2pp3s bvecp-t2pp4s bvecp-t2pp5s)
		  :in-theory (enable t4pp1s ash-rewrite bvecp))))

(local-defthmd bvecp-t3pp1c
  (bvecp (t3pp1c) 73)
  :hints (("Goal" :use (bvecp-t2pp3s bvecp-t2pp4s bvecp-t2pp5s)
                  :in-theory (enable t3pp1c ash-rewrite bvecp))))

(local-defthmd bvecp-t4pp2s
  (bvecp (t4pp2s) 73)
  :hints (("Goal" :use (bvecp-t2pp6s bvecp-t2pp7s bvecp-t2pp8s)
		  :in-theory (enable t4pp2s ash-rewrite bvecp))))

(local-defthmd bvecp-t3pp2c
  (bvecp (t3pp2c) 73)
  :hints (("Goal" :use (bvecp-t2pp6s bvecp-t2pp7s bvecp-t2pp8s)
		  :in-theory (enable t3pp2c ash-rewrite bvecp))))

(local-defthmd bvecp-t4pp3s
  (bvecp (t4pp3s) 107)
  :hints (("Goal" :use (bvecp-t2pp0c bvecp-t2pp1c bvecp-t2pp2c)
		  :in-theory (enable t4pp3s ash-rewrite bvecp))))

(local-defthmd bvecp-t3pp3c
  (bvecp (t3pp3c) 107)
  :hints (("Goal" :use (bvecp-t2pp0c bvecp-t2pp1c bvecp-t2pp2c)
		  :in-theory (enable t3pp3c ash-rewrite bvecp))))

(local-defthmd comp-18
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t5pp0s))
		     (* (expt 2 2) (t4pp0c))
		     (t4pp0s)
		     (* 2 (t3pp0c))
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 17) (t3pp1c))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 35) (t3pp2c))
		     (* (expt 2 2) (t4pp3s))
		     (* (expt 2 3) (t3pp3c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-17 bvecp-t3pp0s bvecp-t3pp1s bvecp-t3pp2s
                        (:instance add-3 (x (t3pp0s))
			                 (y (* (expt 2 16) (t3pp1s)))
					 (z (* (expt 2 34) (t3pp2s)))))
                  :in-theory (enable bvecp ash-rewrite t5pp0s t4pp0c))))

(local-defthmd bvecp-t5pp0s
  (bvecp (t5pp0s) 107)
  :hints (("Goal" :use (bvecp-t3pp0s bvecp-t3pp1s bvecp-t3pp2s)
                  :in-theory (enable t5pp0s ash-rewrite bvecp))))

(local-defthmd bvecp-t4pp0c
  (bvecp (t4pp0c) 107)
  :hints (("Goal" :use (bvecp-t3pp0s bvecp-t3pp1s bvecp-t3pp2s)
		  :in-theory (enable t4pp0c ash-rewrite bvecp))))

(local-defthmd comp-19
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t5pp0s))
		     (* (expt 2 2) (t4pp0c))
		     (* (expt 2 1) (t5pp1s))
		     (* (expt 2 2) (t4pp1c))
		     (t4pp0s)
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 2) (t4pp3s))
		     (* (expt 2 3) (t3pp3c))
		     (* (expt 2 52) (+ (ia) (ib))))))	          
  :hints (("Goal" :use (comp-18 bvecp-t3pp0c bvecp-t3pp1c bvecp-t3pp2c
                        (:instance add-3 (x (t3pp0c))
			                 (y (* (expt 2 16) (t3pp1c)))
					 (z (* (expt 2 34) (t3pp2c)))))
                  :in-theory (enable bvecp ash-rewrite t5pp1s t4pp1c))))

(local-defthmd bvecp-t5pp1s
  (bvecp (t5pp1s) 107)
  :hints (("Goal" :use (bvecp-t3pp0c bvecp-t3pp1c bvecp-t3pp2c)
                  :in-theory (enable t5pp1s ash-rewrite bvecp))))

(local-defthmd bvecp-t4pp1c
  (bvecp (t4pp1c) 107)
  :hints (("Goal" :use (bvecp-t3pp0c bvecp-t3pp1c bvecp-t3pp2c)
                  :in-theory (enable t4pp1c ash-rewrite bvecp))))

(local-defthmd bvecp-ia
  (bvecp (ia) 52)
  :hints (("Goal" :in-theory (enable ia))))

(local-defthmd bvecp-ib
  (bvecp (ib) 53)
  :hints (("Goal" :in-theory (enable ib))))

(local-defthmd comp-20
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t5pp0s))
		     (* (expt 2 2) (t4pp0c))
		     (* (expt 2 1) (t5pp1s))
		     (* (expt 2 2) (t4pp1c))
		     (t4pp0s)
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 2) (t4pp3s))
		     (* (expt 2 3) (t4pp4s))
		     (* (expt 2 4) (t4pp2c)))))
  :hints (("Goal" :use (comp-19 bvecp-ia bvecp-ib bvecp-t3pp3c
                        (:instance add-3 (x (* (expt 2 49) (ia)))
			                 (y (* (expt 2 49) (ib)))
					 (z (t3pp3c))))
                  :in-theory (enable bvecp ash-rewrite t4pp4s t4pp2c))))

(local-defthmd bvecp-t4pp4s
  (bvecp (t4pp4s) 107)
  :hints (("Goal" :use (bvecp-ia bvecp-ib bvecp-t3pp3c)
                  :in-theory (enable t4pp4s ash-rewrite bvecp))))

(local-defthmd bvecp-t4pp2c
  (bvecp (t4pp2c) 107)
  :hints (("Goal" :use (bvecp-ia bvecp-ib bvecp-t3pp3c)
                  :in-theory (enable t4pp2c ash-rewrite bvecp))))

(local-defthmd comp-21
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t5pp0s))
		     (* (expt 2 2) (t6pp0s))
		     (* (expt 2 3) (t5pp0c))
		     (* (expt 2 1) (t5pp1s))
		     (t4pp0s)
		     (* (expt 2 16) (t4pp1s))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 2) (t4pp3s))
		     (* (expt 2 3) (t4pp4s)))))
  :hints (("Goal" :use (comp-20 bvecp-t4pp2c bvecp-t4pp1c bvecp-t4pp0c
                        (:instance add-3 (x (* (expt 2 2) (t4pp2c)))
			                 (y (t4pp1c))
					 (z (t4pp0c))))
                  :in-theory (enable bvecp ash-rewrite t6pp0s t5pp0c))))

(local-defthmd bvecp-t6pp0s
  (bvecp (t6pp0s) 109)
  :hints (("Goal" :use (bvecp-t4pp2c bvecp-t4pp1c bvecp-t4pp0c)
                  :in-theory (enable t6pp0s ash-rewrite bvecp))))

(local-defthmd bvecp-t5pp0c
  (bvecp (t5pp0c) 109)
  :hints (("Goal" :use (bvecp-t4pp2c bvecp-t4pp1c bvecp-t4pp0c)
                  :in-theory (enable t5pp0c ash-rewrite bvecp))))

(local-defthmd comp-22
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t5pp0s))
		     (* (expt 2 2) (t6pp0s))
		     (* (expt 2 3) (t5pp0c))
		     (* (expt 2 1) (t5pp1s))
		     (t6pp1s)
		     (* (expt 2 1) (t5pp1c))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 2) (t4pp3s)))))
  :hints (("Goal" :use (comp-21 bvecp-t4pp0s bvecp-t4pp1s bvecp-t4pp4s
                        (:instance add-3 (x (* (expt 2 3) (t4pp4s)))
			                 (y (t4pp0s))
					 (z (* (expt 2 16) (t4pp1s)))))
                  :in-theory (enable bvecp ash-rewrite t6pp1s t5pp1c))))

(local-defthmd bvecp-t6pp1s
  (bvecp (t6pp1s) 110)
  :hints (("Goal" :use (bvecp-t4pp0s bvecp-t4pp1s bvecp-t4pp4s)
                  :in-theory (enable t6pp1s ash-rewrite bvecp))))

(local-defthmd bvecp-t5pp1c
  (bvecp (t5pp1c) 110)
  :hints (("Goal" :use (bvecp-t4pp0s bvecp-t4pp1s bvecp-t4pp4s)
                  :in-theory (enable t5pp1c ash-rewrite bvecp))))

(local-defthmd comp-23
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t7pp0s))
		     (* (expt 2 2) (t6pp0c))
		     (* (expt 2 2) (t6pp0s))
		     (t6pp1s)
		     (* (expt 2 1) (t5pp1c))
		     (* (expt 2 34) (t4pp2s))
		     (* (expt 2 2) (t4pp3s)))))
  :hints (("Goal" :use (comp-22 bvecp-t5pp0s bvecp-t5pp1s bvecp-t5pp0c
                        (:instance add-3 (x (t5pp0s))
			                 (y (t5pp1s))
					 (z (* (expt 2 2) (t5pp0c)))))
                  :in-theory (enable bvecp ash-rewrite t7pp0s t6pp0c))))

(local-defthmd bvecp-t7pp0s
  (bvecp (t7pp0s) 111)
  :hints (("Goal" :use (bvecp-t5pp0s bvecp-t5pp1s bvecp-t5pp0c)
                  :in-theory (enable t7pp0s ash-rewrite bvecp))))

(local-defthmd bvecp-t6pp0c
  (bvecp (t6pp0c) 111)
  :hints (("Goal" :use (bvecp-t5pp0s bvecp-t5pp1s bvecp-t5pp0c)
                  :in-theory (enable t6pp0c ash-rewrite bvecp))))

(local-defthmd comp-24
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t7pp0s))
		     (* (expt 2 2) (t6pp0c))
		     (* (expt 2 2) (t6pp0s))
		     (t6pp1s)
		     (* (expt 2 1) (t6pp2s))
		     (* (expt 2 2) (t6pp1c)))))
  :hints (("Goal" :use (comp-23 bvecp-t5pp1c bvecp-t4pp2s bvecp-t4pp3s
                        (:instance add-3 (x (* (expt 2 33) (t4pp2s)))
			                 (y (* (expt 2 1) (t4pp3s)))
					 (z (t5pp1c))))
                  :in-theory (enable bvecp ash-rewrite t6pp2s t6pp1c))))

(local-defthmd bvecp-t6pp2s
  (bvecp (t6pp2s) 110)
  :hints (("Goal" :use (bvecp-t5pp1c bvecp-t4pp2s bvecp-t4pp3s)
                  :in-theory (enable t6pp2s ash-rewrite bvecp))))

(local-defthmd bvecp-t6pp1c
  (bvecp (t6pp1c) 110)
  :hints (("Goal" :use (bvecp-t5pp1c bvecp-t4pp2s bvecp-t4pp3s)
                  :in-theory (enable t6pp1c ash-rewrite bvecp))))

(local-defthmd comp-25
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
	          (+ (* (expt 2 1) (t7pp0s))
		     (* (expt 2 2) (t6pp0c))
		     (t8pp0s)
		     (* (expt 2 1) (t7pp0c))
		     (* (expt 2 2) (t6pp1c)))))
  :hints (("Goal" :use (comp-24 bvecp-t6pp0s bvecp-t6pp1s bvecp-t6pp2s
                        (:instance add-3 (x (* (expt 2 2) (t6pp0s)))
			                 (y (t6pp1s))
					 (z (* (expt 2 1) (t6pp2s)))))
                  :in-theory (enable bvecp ash-rewrite t8pp0s t7pp0c))))

(local-defthmd bvecp-t8pp0s
  (bvecp (t8pp0s) 111)
  :hints (("Goal" :use (bvecp-t6pp0s bvecp-t6pp1s bvecp-t6pp2s)
                  :in-theory (enable t8pp0s ash-rewrite bvecp))))

(local-defthmd bvecp-t7pp0c
  (bvecp (t7pp0c) 111)
  :hints (("Goal" :use (bvecp-t6pp0s bvecp-t6pp1s bvecp-t6pp2s)
                  :in-theory (enable t7pp0c ash-rewrite bvecp))))

(local-defthmd comp-26
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
		  (+ (t8pp0s)
		     (* (expt 2 1) (t9pp0s))
		     (* (expt 2 2) (t7pp1c))
		     (* (expt 2 2) (t6pp1c)))))
  :hints (("Goal" :use (comp-25 bvecp-t6pp0c bvecp-t7pp0c bvecp-t7pp0s
                        (:instance add-3 (x (t7pp0s))
			                 (y (t7pp0c))
					 (z (* (expt 2 1) (t6pp0c)))))
                  :in-theory (enable bvecp ash-rewrite t9pp0s t7pp1c))))

(local-defthmd bvecp-t9pp0s
  (bvecp (t9pp0s) 112)
  :hints (("Goal" :use (bvecp-t6pp0c bvecp-t7pp0c bvecp-t7pp0s)
                  :in-theory (enable t9pp0s ash-rewrite bvecp))))

(local-defthmd bvecp-t7pp1c
  (bvecp (t7pp1c) 112)
  :hints (("Goal" :use (bvecp-t6pp0c bvecp-t7pp0c bvecp-t7pp0s)
                  :in-theory (enable t7pp1c ash-rewrite bvecp))))

(local-defthmd comp-27
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
		  (+ (t9pp1s)
		     (* (expt 2 1) (t9pp0c))
		     (* (expt 2 1) (t9pp0s)))))
  :hints (("Goal" :use (comp-26 bvecp-t6pp1c bvecp-t7pp1c bvecp-t8pp0s
                        (:instance add-3 (x (* (expt 2 2) (t7pp1c)))
			                 (y (* (expt 2 2) (t6pp1c)))
					 (z (t8pp0s))))
                  :in-theory (enable bvecp ash-rewrite t9pp1s t9pp0c))))

(local-defthmd bvecp-t9pp1s
  (bvecp (t9pp1s) 114)
  :hints (("Goal" :use (bvecp-t6pp1c bvecp-t7pp1c bvecp-t8pp0s)
                  :in-theory (enable t9pp1s ash-rewrite bvecp))))

(local-defthmd bvecp-t9pp0c
  (bvecp (t9pp0c) 114)
  :hints (("Goal" :use (bvecp-t6pp1c bvecp-t7pp1c bvecp-t8pp0s)
                  :in-theory (enable t9pp0c ash-rewrite bvecp))))

(local-defthmd comp-28
  (implies (not (specialp))
           (equal (+ (expt 2 106) (* (sa) (sb)))
		  (+ (logxor (logxor (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                             (bits (ash (t9pp0c) 1) 114 0))
	             (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                          (logand (bits (ash (t9pp0s) 1) 114 0) (bits (ash (t9pp0c) 1) 114 0)))
                                  (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                          1))))
  :hints (("Goal" :use (comp-27 bvecp-t9pp0c bvecp-t9pp1s bvecp-t9pp0s
                        (:instance add-3 (x (* (expt 2 1) (t9pp0s)))
			                 (y (t9pp1s))
					 (z (* (expt 2 1) (t9pp0c)))))
                  :in-theory (enable bvecp ash-rewrite))))

(local-defthmd comp-29
  (implies (not (specialp))
           (equal (* (sa) (sb))
		  (mod (+ (logxor (logxor (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                  (bits (ash (t9pp0c) 1) 114 0))
	                  (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                               (logand (bits (ash (t9pp0s) 1) 114 0) (bits (ash (t9pp0c) 1) 114 0)))
                                       (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                               1))
		       (expt 2 106))))
  :hints (("Goal" :use (comp-28 bvecp-t9pp0c bvecp-t9pp1s bvecp-t9pp0s bvecp-mana bvecp-manb)
                  :nonlinearp t
                  :in-theory (enable bvecp ash-rewrite sa sb))))

(local-defthmd comp-30
  (implies (not (specialp))
           (equal (* (sa) (sb))
		  (mod (+ (ppa*)
	                  (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                               (logand (bits (ash (t9pp0s) 1) 114 0) (bits (ash (t9pp0c) 1) 114 0)))
                                       (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                               1))
		       (expt 2 106))))
  :hints (("Goal" :use (bvecp-t9pp0c bvecp-t9pp1s bvecp-t9pp0s
                        (:instance mod-sum (a (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                                                   (logand (bits (ash (t9pp0s) 1) 114 0)
								           (bits (ash (t9pp0c) 1) 114 0)))
                                                           (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                                                   1))
					   (b (logxor (logxor (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                                     (bits (ash (t9pp0c) 1) 114 0)))
					   (n (expt 2 106))))
                  :in-theory (enable comp-29 bits-mod ppa*))))

(local-defthmd ppb*-rewrite
  (equal (ppb*)
         (bits (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                    (logand (bits (ash (t9pp0s) 1) 114 0) (bits (ash (t9pp0c) 1) 114 0)))
                            (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                    1)
               105 0))
  :hints (("Goal" :in-theory (enable ppb* bits-bits))))
	

(local-defthmd comp-31
  (implies (not (specialp))
           (equal (* (sa) (sb))
		  (mod (+ (ppa*) (ppb*)) (expt 2 106))))
  :hints (("Goal" :use (bvecp-t9pp0c bvecp-t9pp1s bvecp-t9pp0s
                        (:instance mod-sum (b (ash (logior (logior (logand (bits (ash (t9pp0s) 1) 114 0) (t9pp1s))
                                                                   (logand (bits (ash (t9pp0s) 1) 114 0)
								           (bits (ash (t9pp0c) 1) 114 0)))
                                                           (logand (t9pp1s) (bits (ash (t9pp0c) 1) 114 0)))
                                                   1))
					   (a (ppa*))
					   (n (expt 2 106))))
                  :in-theory (enable comp-30 bits-mod ppb*-rewrite))))

(defthmd prod-rewrite
  (implies (not (specialp))
           (equal (prod) (* (sa) (sb))))
  :hints (("Goal" :in-theory (enable comp-31 computeproduct-lemma prod* bits-mod compress-lemma))))


