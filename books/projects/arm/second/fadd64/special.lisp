(in-package "RTL")

(include-book "prelim")

(defthmd opazero-rewrite
  (equal (opazero)
         (if (= (a) 0)
             1 0))
  :hints (("Goal" :in-theory (enable opazero a val absval expa frac fraca manf sigf expnt siga opaz opax checkdenorm
                              fzp cat)
		  :use ((:instance bits-shift-up-1 (k 53) (x (bits (opa) 63 0)) (i 115) (j 105))
		        (:instance bits-shift-up-1 (k 53) (x (bits (opa) 63 0)) (i 116) (j 105))
		        (:instance bitn-shift-up (k 53) (x (bits (opa) 63 0)) (n 63))
			(:instance bits-shift-up-2 (k 53) (x (bits (opa) 63 0)) (i 51))
			(:instance bits-shift-up-2 (k 1) (x (BITS (* 9007199254740992 (BITS (OPA) 63 0)) 104 0)) (i 104))
			(:instance bits-shift-up-2 (k 1) (x (BITS (* 40564819207303340847894502572032 (BITS (OPA) 63 52)) 104 0))
			                           (i 104))))))

(local-defthmd b-0-1
           (iff (equal (b) 0)
                (and (= (expb) 0)
                     (= (fracb) 0)
	             (= (mulstk) 0)
	             (= (mulovfl) 0)))
  :hints (("Goal" :use (comp-constraints-lemma
                        (:instance bits-plus-bits (x (opb)) (n 104) (p 52) (m 0))
                        (:instance bits-shift-up-2 (x (opb)) (k 1) (i 51)))
		  :expand ((BITS (OPB) 104 52))
                  :in-theory (enable fzp checkdenorm comp-constraints bits-mod expb opbz chop expnt mulstk mulovfl opblong
		              fracb frac val absval))))

(defthmd opbzero-rewrite
  (equal (opbzero)
         (if (= (b) 0)
             1 0))
  :hints (("Goal" :in-theory (enable opbzero)
		  :use (b-0-1))))

(defthm piz-1-rewrite
  (equal (piz-1) 0)
  :hints (("Goal" :in-theory (enable piz-1 comp-constraints)
                  :use (comp-constraints-lemma))))

(defthm opanan-rewrite
  (equal (opanan) 0)
  :hints (("Goal" :in-theory (enable expnt opax checkdenorm fzp opaz expf dp opanan expa piz-1 comp-constraints)
                  :use (comp-constraints-lemma))))

(defthm opainf-rewrite
  (equal (opainf) 0)
  :hints (("Goal" :in-theory (enable expnt opax checkdenorm fzp opaz expf dp opainf expa piz-1 comp-constraints)
                  :use (comp-constraints-lemma))))

(defthm opbnan-rewrite
  (equal (opbnan) 0)
  :hints (("Goal" :in-theory (enable opblong expnt checkdenorm fzp opbz expf dp opbnan expb piz-1 comp-constraints
                                     val absval)
                  :use (comp-constraints-lemma))))

(defthm opbinf-rewrite
  (equal (opbinf) 0)
  :hints (("Goal" :in-theory (enable opblong expnt checkdenorm fzp opbz expf dp opbinf expb piz-1 comp-constraints
                                     val absval)
                  :use (comp-constraints-lemma))))

(local-defthmd sum-0-1
  (implies (= (mulovfl) 1)
           (>= (abs (b)) (expt 2 1025)))	   
  :hints (("Goal" :in-theory (enable mulovfl opblong comp-constraints)
                  :use (comp-constraints-lemma))))

(local-defthmd sum-0-2
  (<=  (expa) 2046)
  :hints (("Goal" :in-theory (enable expnt opax checkdenorm fzp opaz expf dp expa comp-constraints)
                  :use (comp-constraints-lemma))))

(local-defthmd sum-0-3
  (<  (siga) (expt 2 107))
  :hints (("Goal" :in-theory (enable bvecp siga cat)
                  :use ((:instance bits-bounds (x (fraca)) (i 104) (j 0))))))

(local-defthmd sum-0-4
  (<  (abs (a)) (expt 2 1025))
  :hints (("Goal" :in-theory (enable a val absval)
                  :nonlinearp t
                  :use (sum-0-2 sum-0-3))))

(local-defthmd sum-0-5
  (implies (= (+ (a) (b)) 0)
           (equal (mulovfl) 0))
  :hints (("Goal" :in-theory (enable mulovfl)
                  :use (sum-0-1 sum-0-4))))

(local-defthmd sum-0-6
  (implies (= (mulstk) 1)
           (and (< (absval 0 (chop (sigb) -53)) (abs (b)))
	        (> (absval 0 (+ (expt 2 53) (chop (sigb) -53))) (abs (b)))))
  :hints (("Goal" :in-theory (enable cat frac fracb opblong opbz checkdenorm sigb expb expnt mulstk comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-shift-up-2 (k 1) (i 104) (x (bits (opb) 104 0)))))))

(local-defthmd sum-0-7
  (implies (= (mulstk) 1)
           (not (integerp (* (expt 2 (+ 52 1023)) (b)))))
  :hints (("Goal" :in-theory (enable absval chop)
                  :use (sum-0-6))))

(local-defthmd sum-0-8
  (integerp (* (expt 2 (+ 52 1023)) (- (a))))
  :hints (("Goal" :in-theory (enable a-rewrite dp expf decode ddecode ndecode))))

(local-defthmd sum-0-9
  (implies (= (b) (- (a)))
           (= (mulstk) 0))
  :hints (("Goal" :use (sum-0-7 sum-0-8))))

(local-defthmd sum-0-10
  (implies (= (+ (a) (b)) 0)
           (equal (mulstk) 0))
  :hints (("Goal" :use (sum-0-9))))

(local-defthmd sum-0-11
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(> (expb) 0))
	   (equal (b) (val (signb) (expb) (+ (expt 2 106) (* 2 (fracb))))))
  :hints (("Goal" :in-theory (enable signb sign cat frac fracb opblong opbz checkdenorm sigb expb expnt mulstk
                                     mulovfl comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-shift-up-1 (k 105) (i 115) (j 105) (x (bits (opb) 116 105)))))))

(local-defthmd sum-0-12
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (and (< (absval 0 (chop (sigb) -53)) (abs (b)))
	        (> (absval 0 (+ (expt 2 53) (chop (sigb) -53))) (abs (b)))))
  :hints (("Goal" :in-theory (enable signb sign cat frac fracb opblong opbz checkdenorm sigb expb expnt mulstk
                                     fzp mulovfl comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-shift-up-2 (k 1) (i 104) (x (bits (opb) 104 0)))
		        (:instance bits-shift-up-2 (k 105) (i -1) (x (bits (opb) 116 105)))
		        (:instance bits-shift-up-1 (k 105) (i 115) (j 105) (x (bits (opb) 116 105)))))))

(local-defthmd sum-0-12
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (and (< (absval 0 (chop (sigb) -53)) (abs (b)))
	        (> (absval 0 (+ (expt 2 53) (chop (sigb) -53))) (abs (b)))))
  :hints (("Goal" :in-theory (enable signb sign cat frac fracb opblong opbz checkdenorm sigb expb expnt mulstk
                                     fzp mulovfl comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-shift-up-2 (k 1) (i 104) (x (bits (opb) 104 0)))
		        (:instance bits-shift-up-2 (k 105) (i -1) (x (bits (opb) 116 105)))
		        (:instance bits-shift-up-1 (k 105) (i 115) (j 105) (x (bits (opb) 116 105)))))))

(local-defthmd sum-0-13
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (not (integerp (* (expt 2 (+ 52 1023)) (b)))))
  :hints (("Goal" :in-theory (enable absval chop)
                  :use (sum-0-12))))

(local-defthmd sum-0-14
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (not (= (b) (- (a)))))
  :hints (("Goal" :in-theory (enable absval chop)
                  :use (sum-0-13 sum-0-8))))

(local-defthmd sum-0-15
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (not (= (+ (a) (b)) 0)))
  :hints (("Goal" :use (sum-0-14))))

(local-defthmd sum-0-16
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (not (= (bits (fracb) 51 0) 0)))
  :hints (("Goal" :in-theory (enable sigb))))

(local-defthmd sum-0-17
  (equal (bits (fraca) 51 0)
          0)
  :hints (("Goal" :in-theory (enable fraca frac opax opaz checkdenorm))))

(local-defthmd sum-0-18
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (= (bits (sigb) 52 0) 0)))
           (and (not (= (+ (a) (b)) 0))
	        (not (= (fraca) (fracb)))))
  :hints (("Goal" :use (sum-0-15 sum-0-16 sum-0-17))))

(local-defthmd sum-0-19
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(= (bits (sigb) 52 0) 0))
	   (equal (absval 0 (chop (sigb) -53)) (abs (b))))
  :hints (("Goal" :in-theory (enable signb sign cat frac fracb opblong opbz checkdenorm sigb expb expnt mulstk
                                     absval fzp mulovfl comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-shift-up-2 (k 1) (i 104) (x (bits (opb) 104 0)))
		        (:instance bits-shift-up-2 (k 105) (i -1) (x (bits (opb) 116 105)))
		        (:instance bits-shift-up-1 (k 105) (i 115) (j 105) (x (bits (opb) 116 105)))))))

(local-defthmd sum-0-20
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(= (bits (sigb) 52 0) 0))
	   (integerp (/ (sigb) (expt 2 53))))
  :hints (("Goal" :use ((:instance exact-bits-3 (k 53) (x (sigb)))))))

(local-defthmd sum-0-21
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expb) 0)
		(= (bits (sigb) 52 0) 0))
	   (equal (absval 0 (sigb)) (abs (b))))
  :hints (("Goal" :in-theory (enable chop)
                  :use (sum-0-19 sum-0-20))))

(local-defthmd sum-0-22
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expa) (expb))
		(> (expa) 0)
		(= (fraca) (fracb))
		(not (= (signa) (signb))))
	   (equal (+ (a) (b)) 0))
  :hints (("Goal" :in-theory (enable sign fraca fracb frac bvecp cat absval val sum-0-11 a siga sigb signa signb)  
                  :use ((:instance bits-shift-up-2 (k 1) (i 104) (x (bits (opaz) 104 0)))))))

(local-defthmd sum-0-23
  (implies (not (= (b) 0))
           (equal (signb)
                  (if (< (b) 0) 1 0)))
  :hints (("Goal" :in-theory (enable bitn-bits opbz checkdenorm sign signb comp-constraints)
                  :use (comp-constraints-lemma))))

(local-defthmd sum-0-24
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expa) (expb))
		(= (expa) 0)
		(= (fraca) (fracb))
		(= (bits (sigb) 52 0) 0)
		(not (= (signa) (signb))))
	   (equal (+ (a) (b)) 0))
  :hints (("Goal" :in-theory (enable sum-0-23 sign fraca fracb frac bvecp cat absval val a siga sigb signa)
                  :use (sum-0-21
		        (:instance bits-shift-up-2 (k 1) (i 104) (x (bits (opaz) 104 0)))))))

(local-defthmd sum-0-25
  (implies (and (= (mulstk) 0)
                (= (mulovfl) 0)
		(= (expa) (expb))
		(= (fraca) (fracb))
		(not (= (signa) (signb))))
	   (equal (+ (a) (b)) 0))
  :hints (("Goal" :use (sum-0-22 sum-0-24 sum-0-18))))

(defthm isspecial-0
  (equal (isspecial) 0)
  :hints (("Goal" :use (sum-0-25 a+b<>0)
                  :in-theory (enable checkspecial-lemma isspecial* opazero-rewrite opbzero-rewrite opanan-rewrite
		                     opbnan-rewrite opaqnan opasnan opbqnan opbsnan opainf-rewrite opbinf-rewrite
				     piz-1-rewrite))))





