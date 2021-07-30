(in-package "RTL")

(include-book "induct")

(local-defund hyp-pos (j)
  (and (bvecp (quot j) (1- (* 3 j)))
       (bvecp (quotm j) (1- (* 3 j)))
       (= (quot j) (* (expt 8 (1- j)) (quotient j)))
       (= (quotm j) (1- (quot j)))))

(local-in-theory (disable (hyp-pos)))

(local-defthmd nextquot-pos-1
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-pos j))
	   (and (bvecp (quot j) (1- (* 3 j)))
	        (bvecp (quotm j) (1- (* 3 j)))))
  :hints (("Goal" :in-theory (enable hyp-pos))))

(local-defthmd nextquot-pos-2
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-pos j))
	   (= (quot j) (* (expt 8 (1- j)) (quotient j))))
  :hints (("Goal" :in-theory (enable hyp-pos))))

(local-defthmd nextquot-pos-3
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-pos j))
           (= (quotm j) (1- (quot j))))
  :hints (("Goal" :in-theory (enable hyp-pos))))

(local-defthmd nextquot-pos-4
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-pos j)
		(< j (n)))
	   (<= j 21))
  :hints (("Goal" :use (n-bounds))))

(local-defthmd nextquot-pos-5
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n))
		(>= (q (1+ j)) 0))
	   (equal (quot (+ 1 j)) (+ (* 8 (quot j)) (q (1+ j)))))
  :hints (("Goal" :in-theory (enable si quot-1 bvecp nextquot quot cat ash)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4
		        (:instance bits-shift-up-1 (x (quot j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-6
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n))
		(< (q (1+ j)) 0))
	   (equal (quot (+ 1 j)) (+ (* 8 (quotm j)) (+ 8 (q (1+ j))))))
  :hints (("Goal" :in-theory (enable si quot-1 bvecp nextquot quot cat ash)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4 nextquot-pos-3
		        (:instance bits-shift-up-1 (x (quotm j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-7
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n))
		(< (q (1+ j)) 0))
	   (equal (quot (+ 1 j)) (+ (* 8 (quot j)) (q (1+ j)))))
  :hints (("Goal" :in-theory (enable si quot-1 bvecp nextquot quot cat ash)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4 nextquot-pos-3
		        (:instance bits-shift-up-1 (x (quotm j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-8
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n)))
	   (equal (quot (+ 1 j)) (+ (* 8 (quot j)) (q (1+ j)))))
  :hints (("Goal" :use (nextquot-pos-5 nextquot-pos-7))))

(local-defthmd nextquot-pos-9
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n)))
	   (equal (quot (+ 1 j)) (* (expt 8 j) (quotient (1+ j)))))
  :hints (("Goal" :use (nextquot-pos-2 nextquot-pos-8)
                  :in-theory (enable quotient))))

(local-defthmd nextquot-pos-10
  (implies (and (natp q)
                (natp j)
		(< q (expt 2 j)))
	   (<= (* 8 q) (- (expt 2 (+ 3 j)) 8)))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd nextquot-pos-11
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n)))
	   (bvecp (quot (1+ j)) (1- (* 3 (1+ j)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4 nextquot-pos-5 nextquot-pos-6
		        (:instance nextquot-pos-10 (q (quot j)) (j (1- (* 3 j))))
		        (:instance nextquot-pos-10 (q (quotm j)) (j (1- (* 3 j))))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-12
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n))
		(> (q (1+ j)) 0))
	   (equal (quotm (+ 1 j)) (+ (* 8 (quot j)) (q (1+ j)) -1)))
  :hints (("Goal" :in-theory (enable si quot-1 quotm-1 bvecp nextquot quotm cat ash)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4
		        (:instance bits-shift-up-1 (x (quot j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-13
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n))
		(<= (q (1+ j)) 0))
	   (equal (quotm (+ 1 j)) (+ (* 8 (quotm j)) (+ 7 (q (1+ j))))))
  :hints (("Goal" :in-theory (enable si quot-1 quotm-1 bvecp nextquot quotm cat ash)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4 nextquot-pos-3
		        (:instance bits-shift-up-1 (x (quotm j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-14
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n)))
	   (equal (quotm (+ 1 j)) (1- (quot (+ 1 j)))))
  :hints (("Goal" :use (nextquot-pos-1 nextquot-pos-3 nextquot-pos-12 nextquot-pos-13 nextquot-pos-5 nextquot-pos-6
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-15
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 0)
		(hyp-pos j)
		(< j (n)))
	   (bvecp (quotm (1+ j)) (1- (* 3 (1+ j)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (nextquot-pos-1 nextquot-pos-4 nextquot-pos-12 nextquot-pos-13
		        (:instance nextquot-pos-10 (q (quot j)) (j (1- (* 3 j))))
		        (:instance nextquot-pos-10 (q (quotm j)) (j (1- (* 3 j))))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-pos-16
  (implies (and (not (earlyp))
		(= (sgnq) 0)
                (not (zp j))
		(< j (n))
		(hyp-pos j))
	   (hyp-pos (1+ j)))
  :hints (("Goal" :expand ((hyp-pos (+ 1 j)))
                  :use (p-vals nextquot-pos-9 nextquot-pos-11 nextquot-pos-14 nextquot-pos-15))))

(local-defthmd nextquot-pos-17
  (implies (and (not (earlyp))
		(= (sgnq) 0))
	   (hyp-pos 1))
  :hints (("Goal" :in-theory (enable hyp-pos q-1 q quot quotm quot-1 quotm-1 quotient))))

(local-defthmd nextquot-pos-18
  (implies (and (not (earlyp))
		(= (sgnq) 0)
                (not (zp j))
		(<= j (n)))
	   (hyp-pos j))	   
  :hints (("Goal" :induct (nats j))  
          ("Subgoal *1/2" :use (nextquot-pos-17))
	  ("Subgoal *1/1" :use (nextquot-pos-17 (:instance nextquot-pos-16 (j (1- j)))))))

(local-defthmd nextquot-pos
  (implies (and (not (earlyp))
		(= (sgnq) 0)
                (not (zp j))
		(<= j (n)))
          (and (bvecp (quot j) (1- (* 3 j)))
               (bvecp (quotm j) (1- (* 3 j)))
               (= (quot j) (* (expt 8 (1- j)) (quotient j)))
               (= (quotm j) (1- (quot j)))))
  :hints (("Goal" :in-theory (enable hyp-pos)
		  :use (n-bounds nextquot-pos-18))))

(defthmd quotf-pos
  (implies (and (not (earlyp))
		(= (sgnq) 0))
	   (and (bvecp (quotf) 65)
	        (bvecp (quotmf) 65)
                (equal (quotf) (* (expt 8 (1- (n))) (qf)))
		(equal (quotmf) (1- (quotf)))))
  :hints (("Goal" :in-theory (enable qf quotf-rewrite quotmf-rewrite bvecp)
                  :nonlinearp t
                  :use (n-bounds
		        (:instance nextquot-pos (j (n)))))))

;;***************************************************************************************

(local-defund hyp-neg (j)
  (and (integerp (quot j))
       (< (- (expt 2 65) (expt 2 (1- (* 3 j)))) (quot j))
       (< (quot j) (expt 2 65))
       (integerp (quotm j))
       (< (- (expt 2 65) (expt 2 (1- (* 3 j)))) (quotm j))
       (< (quotm j) (expt 2 65))
       (= (quot j) (- (expt 2 65) (* (expt 8 (1- j)) (quotient j))))
       (= (quotm j) (1- (quot j)))))

(local-in-theory (disable (hyp-neg)))

(local-defthmd nextquot-neg-1
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-neg j))
	   (and (integerp (quot j))
                (< (- (expt 2 65) (expt 2 (1- (* 3 j)))) (quot j))
                (< (quot j) (expt 2 65))
                (integerp (quotm j))
                (< (- (expt 2 65) (expt 2 (1- (* 3 j)))) (quotm j))
                (< (quotm j) (expt 2 65))))
  :hints (("Goal" :in-theory (enable hyp-neg))))

(local-defthmd nextquot-neg-2
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-neg j))
	   (= (quot j) (- (expt 2 65) (* (expt 8 (1- j)) (quotient j)))))
  :hints (("Goal" :in-theory (enable hyp-neg))))

(local-defthmd nextquot-neg-3
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-neg j))
           (= (quotm j) (1- (quot j))))
  :hints (("Goal" :in-theory (enable hyp-neg))))

(local-defthmd nextquot-neg-4
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp-neg j)
		(< j (n)))
	   (<= j 21))
  :hints (("Goal" :use (n-bounds))))

(local-defthmd nextquot-neg-5
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n))
		(<= (q (1+ j)) 0))
	   (equal (quot (+ 1 j)) (+ (* 8 (quot j)) (- (q (1+ j))) (- (* 7 (expt 2 65))))))
  :hints (("Goal" :in-theory (enable si bits-top-ones neg-bits-1 quot-1 bvecp nextquot quot cat ash)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4
		        (:instance bits-plus-bits (x (quot j)) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (- (quot j) (expt 2 65))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-6
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n))
		(> (q (1+ j)) 0))
	   (equal (quot (+ 1 j)) (+ (* 8 (quotm j)) (- 8 (q (1+ j))) (- (* 7 (expt 2 65))))))
  :hints (("Goal" :in-theory (enable si bits-top-ones quot-1 bvecp nextquot quot cat ash)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4 nextquot-neg-3
		        (:instance bits-plus-bits (x (quotm j)) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (- (quotm j) (expt 2 65))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-7
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n))
		(> (q (1+ j)) 0))
	   (equal (quot (+ 1 j)) (+ (* 8 (quot j)) (- (q (1+ j))) (- (* 7 (expt 2 65))))))
  :hints (("Goal" :in-theory (enable si bits-top-ones quot-1 bvecp nextquot quot cat ash)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4 nextquot-neg-3
		        (:instance bits-plus-bits (x (quotm j)) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (- (quotm j) (expt 2 65))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-8
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n)))
	   (equal (quot (+ 1 j)) (+ (* 8 (quot j)) (- (q (1+ j))) (- (* 7 (expt 2 65))))))
  :hints (("Goal" :use (nextquot-neg-5 nextquot-neg-7))))

(local-defthmd nextquot-neg-9
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n)))
	   (equal (quot (+ 1 j)) (- (expt 2 65) (* (expt 8 j) (quotient (1+ j))))))
  :hints (("Goal" :use (nextquot-neg-2 nextquot-neg-8)
                  :in-theory (enable quotient))))

(local-defthmd nextquot-neg-11
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n)))
           (and (integerp (quot (1+ j)))
                (< (- (expt 2 65) (expt 2 (1- (* 3 (1+ j))))) (quot (1+ j)))
                (< (quot (1+ j)) (expt 2 65))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4 nextquot-neg-5 nextquot-neg-6
		        ;(:instance nextquot-neg-10 (q (quot j)) (j (1- (* 3 j))))
		        ;(:instance nextquot-neg-10 (q (quotm j)) (j (1- (* 3 j))))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-12
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n))
		(< (q (1+ j)) 0))
	   (equal (quotm (+ 1 j)) (+ (* 8 (quot j)) (- (q (1+ j))) -1 (- (* 7 (expt 2 65))))))
  :hints (("Goal" :in-theory (enable si bits-top-ones quot-1 quotm-1 bvecp nextquot quotm cat ash)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4
		        (:instance bits-plus-bits (x (quot j)) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (- (quot j) (expt 2 65))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-13
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n))
		(>= (q (1+ j)) 0))
	   (equal (quotm (+ 1 j)) (+ (* 8 (quotm j)) (- 7 (q (1+ j))) (- (* 7 (expt 2 65))))))
  :hints (("Goal" :in-theory (enable si bits-top-ones quot-1 quotm-1 bvecp nextquot quotm cat ash)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4 nextquot-neg-3
		        (:instance bits-plus-bits (x (quotm j)) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (- (quotm j) (expt 2 65))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm j)) (k 3) (i 64) (j 3))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-14
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n)))
	   (equal (quotm (+ 1 j)) (1- (quot (+ 1 j)))))
  :hints (("Goal" :use (nextquot-neg-1 nextquot-neg-3 nextquot-neg-12 nextquot-neg-13 nextquot-neg-5 nextquot-neg-6
                        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-15
  (implies (and (not (earlyp))
                (not (zp j))
		(= (sgnq) 1)
		(hyp-neg j)
		(< j (n)))
           (and (integerp (quotm (1+ j)))
                (< (- (expt 2 65) (expt 2 (1- (* 3 (1+ j))))) (quotm (1+ j)))
                (< (quotm (1+ j)) (expt 2 65))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (nextquot-neg-1 nextquot-neg-4 nextquot-neg-12 nextquot-neg-13
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-neg-16
  (implies (and (not (earlyp))
		(= (sgnq) 1)
                (not (zp j))
		(< j (n))
		(hyp-neg j))
	   (hyp-neg (1+ j)))
  :hints (("Goal" :expand ((hyp-neg (+ 1 j)))
                  :use (p-vals nextquot-neg-9 nextquot-neg-11 nextquot-neg-14 nextquot-neg-15))))

(local-defthmd nextquot-neg-17
  (implies (and (not (earlyp))
		(= (sgnq) 1))
	   (hyp-neg 1))
  :hints (("Goal" :in-theory (enable hyp-neg q-1 q quot quotm quot-1 quotm-1 quotient))))

(local-defthmd nextquot-neg-18
  (implies (and (not (earlyp))
		(= (sgnq) 1)
                (not (zp j))
		(<= j (n)))
	   (hyp-neg j))	   
  :hints (("Goal" :induct (nats j))  
          ("Subgoal *1/2" :use (nextquot-neg-17))
	  ("Subgoal *1/1" :use (nextquot-neg-17 (:instance nextquot-neg-16 (j (1- j)))))))

(local-defthmd nextquot-neg
  (implies (and (not (earlyp))
		(= (sgnq) 1)
                (not (zp j))
		(<= j (n)))
           (and (integerp (quot j))
                (< (- (expt 2 65) (expt 2 (1- (* 3 j)))) (quot j))
                (< (quot j) (expt 2 65))
                (integerp (quotm j))
                (< (- (expt 2 65) (expt 2 (1- (* 3 j)))) (quotm j))
                (< (quotm j) (expt 2 65))
                (= (quot j) (- (expt 2 65) (* (expt 8 (1- j)) (quotient j))))
                (= (quotm j) (1- (quot j)))))
  :hints (("Goal" :in-theory (enable hyp-neg)
		  :use (n-bounds nextquot-neg-18))))

(defthmd quotf-neg
  (implies (and (not (earlyp))
		(= (sgnq) 1))
	   (and (bvecp (quotf) 65)
	        (bvecp (quotmf) 65)
                (equal (quotf) (- (expt 2 65) (* (expt 8 (1- (n))) (qf))))
		(equal (quotmf) (1- (quotf)))))
  :hints (("Goal" :in-theory (enable qf quotf-rewrite quotmf-rewrite bvecp)
                  :nonlinearp t
                  :use (n-bounds
		        (:instance nextquot-neg (j (n)))))))

;;***************************************************************************************

(defthmd sgnq-0-1
  (member (sgnq) '(0 1))
  :hints (("Goal" :in-theory (enable sgnq sgna-a sgnb-b))))
                
(defthmd quotpf-n=2
  (implies (and (not (earlyp))
                (= (n) 2)
		(not (and (= (sgnq) 1) (= (del) 1) (= (qf) 1/2))))
	   (equal (quotpf)
	          (+ (quotf) (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotpf-rewrite quotf-rewrite qf quotient quotp it1 bvecp k n)
                  :use (q1-max-1 sgnq-0-1 del-bounds
		        (:instance bvecp-member (x (del)) (n 6))
		        (:instance q-vals (j 2))
			(:instance nextquot-pos (j 2))
			(:instance nextquot-neg (j 2))))))

(defthmd quotpf-n=2-pos
  (implies (and (not (earlyp))
                (= (n) 2)
		(= (sgnq) 0))
	   (equal (quotpf)
	          (+ (* (expt 8 (1- (n))) (qf))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotpf-n=2 quotf-pos))))

(defthmd quotpf-n=2-neg
  (implies (and (not (earlyp))
                (= (n) 2)
		(= (sgnq) 1)
		(not (= (qf) 1/2)))
	   (equal (quotpf)
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (qf)))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotpf-n=2 quotf-neg))))

(local-defthmd quotp-incquot
  (implies (and (not (earlyp))
                (> (n) 2))
	   (equal (quotp (n))
	          (incquot (sgnq) (q (n)) (quot (1- (n))) (quotm (1- (n))) (q (1- (n))) (quot (- (n) 2)) (quotm (- (n) 2)) (k))))
  :hints (("Goal" :in-theory (enable quotp it1 qlast quotlast quotmlast))))

(local-defthmd quotp-n-2-sgnq=0
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0))
	   (and (bvecp (quot (- (n) 2)) (1- (* 3 (- (n) 2))))
                (bvecp (quotm (- (n) 2)) (1- (* 3 (- (n) 2))))
                (= (quot (- (n) 2)) (* (expt 8 (1- (- (n) 2))) (quotient (- (n) 2))))
                (= (quotm (- (n) 2)) (1- (quot (- (n) 2))))))
  :hints (("Goal" :use ((:instance nextquot-pos (j (- (n) 2)))))))

(local-defthmd quotp-sgnq=0-k=2-qn=4
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0)
		(= (k) 2)
		(= (q (n)) 4))
	   (equal (quotp (n))
	          (+ (* (expt 8 (1- (n))) (quotient (n)))
		     (expt 2 (k)))))
  :hints (("Goal" :cases ((< (q (1- (n))) -1))
                  :in-theory (enable quotp-incquot incquot cat bvecp quotient)
                  :nonlinearp t
                  :use (quotp-n-2-sgnq=0 n-bounds
		        (:instance bits-shift-up-1 (x (quot (- (n) 2))) (k 6) (i 64) (j 6))
		        (:instance bits-shift-up-1 (x (quot (- (n) 2))) (k 6) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (- (n) 2))) (k 6) (i 64) (j 6))
		        (:instance bits-shift-up-1 (x (quotm (- (n) 2))) (k 6) (i 2) (j 0))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd quotp-n-2-sgnq=1
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1))
           (and (integerp (quot (- (n) 2)))
                (< (- (expt 2 65) (expt 2 (1- (* 3 (- (n) 2))))) (quot (- (n) 2)))
                (< (quot (- (n) 2)) (expt 2 65))
                (integerp (quotm (- (n) 2)))
                (< (- (expt 2 65) (expt 2 (1- (* 3 (- (n) 2))))) (quotm (- (n) 2)))
                (< (quotm (- (n) 2)) (expt 2 65))
                (= (quot (- (n) 2)) (- (expt 2 65) (* (expt 8 (1- (- (n) 2))) (quotient (- (n) 2)))))
                (= (quotm (- (n) 2)) (1- (quot (- (n) 2))))))
  :hints (("Goal" :use ((:instance nextquot-neg (j (- (n) 2)))))))

(local-defthmd quotp-sgnq=1-k=2-qn=4
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1)
		(= (k) 2)
		(= (q (n)) -4))
	   (equal (quotp (n))
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (quotient (n))))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp bits-top-ones)
                  :nonlinearp t
		  :expand ((quotient (+ -1 (n)))
		           (quotient (n)))
                  :use (quotp-n-2-sgnq=1 n-bounds
		        (:instance bits-plus-bits (x (quot (- (n) 2))) (n 64) (p 59) (m 0))
		        (:instance bits-plus-bits (x (quotm (- (n) 2))) (n 64) (p 59) (m 0))
		        (:instance bits-shift-up-1 (x (quot (- (n) 2))) (k 6) (i 64) (j 6))
		        (:instance bits-shift-up-1 (x (quotm (- (n) 2))) (k 6) (i 64) (j 6))
		        (:instance bits-shift-up-1 (x (quot (- (n) 2))) (k 6) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (- (n) 2))) (k 6) (i 2) (j 0))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd quotp-n-1-sgnq=0
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0))
	   (and (bvecp (quot (1- (n))) (1- (* 3 (1- (n)))))
                (bvecp (quotm (1- (n))) (1- (* 3 (1- (n)))))
                (= (quot (1- (n))) (* (expt 8 (1- (1- (n)))) (quotient (1- (n)))))
                (= (quotm (1- (n))) (1- (quot (1- (n)))))))
  :hints (("Goal" :use ((:instance nextquot-pos (j (1- (n))))))))

(local-defthmd quotp-n-1-sgnq=1
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1))
           (and (integerp (quot (1- (n))))
                (< (- (expt 2 65) (expt 2 (1- (* 3 (1- (n)))))) (quot (1- (n))))
                (< (quot (1- (n))) (expt 2 65))
                (integerp (quotm (1- (n))))
                (< (- (expt 2 65) (expt 2 (1- (* 3 (1- (n)))))) (quotm (1- (n))))
                (< (quotm (1- (n))) (expt 2 65))
                (= (quot (1- (n))) (- (expt 2 65) (* (expt 8 (1- (1- (n)))) (quotient (1- (n))))))
                (= (quotm (1- (n))) (1- (quot (1- (n)))))))
  :hints (("Goal" :use ((:instance nextquot-neg (j (1- (n))))))))


(local-defthmd quotp-sgnq=0-k=2-qn<4
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0)
		(= (k) 2)
		(< (q (n)) 4))
	   (equal (quotp (n))
	          (+ (* (expt 8 (1- (n))) (quotient (n)))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp quotient)
                  :nonlinearp t
                  :use (quotp-n-1-sgnq=0 q-vals n-bounds
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 2) (j 0))
		        (:instance q-vals (j (n)))))))

(local-defthmd quotp-sgnq=1-k=2-qn>-4
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1)
		(= (k) 2)
		(> (q (n)) -4))
	   (equal (quotp (n))
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (quotient (n))))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp bits-top-ones)
                  :nonlinearp t
		  :expand ((quotient (n)))
                  :use (quotp-n-1-sgnq=1 n-bounds
		        (:instance bits-plus-bits (x (quot (1- (n)))) (n 64) (p 62) (m 0))
		        (:instance bits-plus-bits (x (quotm (1- (n)))) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 6) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 6) (i 2) (j 0))
		        (:instance q-vals (j (n)))))))

(local-defthmd quotp-sgnq=0-k=1
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0)
		(= (k) 1))
	   (equal (quotp (n))
	          (+ (* (expt 8 (1- (n))) (quotient (n)))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp quotient)
                  :nonlinearp t
                  :use (quotp-n-1-sgnq=0 q-vals n-bounds
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 2) (j 0))
		        (:instance q-vals (j (n)))))))

(local-defthmd quotp-sgnq=1-k=1
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1)
		(= (k) 1))
	   (equal (quotp (n))
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (quotient (n))))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp bits-top-ones)
                  :nonlinearp t
		  :expand ((quotient (n)))
                  :use (quotp-n-1-sgnq=1 n-bounds
		        (:instance bits-plus-bits (x (quot (1- (n)))) (n 64) (p 62) (m 0))
		        (:instance bits-plus-bits (x (quotm (1- (n)))) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 6) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 6) (i 2) (j 0))
		        (:instance q-vals (j (n)))))))

(local-defthmd quotp-sgnq=0-k=0
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0)
		(= (k) 0))
	   (equal (quotp (n))
	          (+ (* (expt 8 (1- (n))) (quotient (n)))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp quotient)
                  :nonlinearp t
                  :use (quotp-n-1-sgnq=0 q-vals n-bounds
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 2) (j 0))
		        (:instance q-vals (j (n)))))))

(local-defthmd quotp-sgnq=1-k=0
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1)
		(= (k) 0))
	   (equal (quotp (n))
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (quotient (n))))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable quotp-incquot incquot cat bvecp bits-top-ones)
                  :nonlinearp t
		  :expand ((quotient (n)))
                  :use (quotp-n-1-sgnq=1 n-bounds
		        (:instance bits-plus-bits (x (quot (1- (n)))) (n 64) (p 62) (m 0))
		        (:instance bits-plus-bits (x (quotm (1- (n)))) (n 64) (p 62) (m 0))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 3) (i 64) (j 3))
		        (:instance bits-shift-up-1 (x (quot (1- (n)))) (k 6) (i 2) (j 0))
		        (:instance bits-shift-up-1 (x (quotm (1- (n)))) (k 6) (i 2) (j 0))
		        (:instance q-vals (j (n)))))))

(defthmd quotpf-sgnq=0
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0))
	   (equal (quotpf)
	          (+ (* (expt 8 (1- (n))) (qf))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable k quotpf-rewrite qf)
                  :use (quotp-sgnq=0-k=0 quotp-sgnq=0-k=1 quotp-sgnq=0-k=2-qn=4 quotp-sgnq=0-k=2-qn<4
		        (:instance q-vals (j (n)))))))

(defthmd quotpf-sgnq=1
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1))
	   (equal (quotpf)
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (qf)))
		     (expt 2 (k)))))
  :hints (("Goal" :in-theory (enable k quotpf-rewrite qf)
                  :use (quotp-sgnq=1-k=0 quotp-sgnq=1-k=1 quotp-sgnq=1-k=2-qn=4 quotp-sgnq=1-k=2-qn>-4
		        (:instance q-vals (j (n)))))))
