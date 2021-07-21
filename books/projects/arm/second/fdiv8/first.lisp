(in-package "RTL")

(include-book "algorithm")

(local-defthm sigaltsigb-rewrite
  (implies (not (specialp))
           (equal (sigaltsigb)
	          (if (< (siga) (sigb)) 1 0)))
  :hints (("Goal" :in-theory (enable bitn-bits lognot sigaltsigb bvecp sigcmp)
           :use (siga-bounds sigb-bounds
                 (:instance bitn-0-1 (x (+ (1- (expt 2 53)) (- (sigb) (siga)))) (n 53))
		 (:instance bitn-plus-bits (x (+ (1- (expt 2 53)) (- (sigb) (siga)))) (n 53) (m 0))			
		 (:instance bits-bounds (x (+ (1- (expt 2 53)) (- (sigb) (siga)))) (i 52) (j 0))))))

(defthm ash-rewrite
  (equal (ash i c)
         (fl (* (ifix i) (expt 2 c))))
  :hints (("Goal" :in-theory (enable floor fl ash))))

(defthmd rp1-rewrite
  (implies (not (specialp))
           (equal (rp-1)
	          (* (expt 2 67) (x))))
  :hints (("Goal" :use (siga-bounds siga-rewrite sigb-rewrite)
                  :in-theory (enable bvecp sigaltsigb-rewrite rp-1 x))))

(defthm integerp-expdiff
  (implies (not (specialp))
           (integerp (expdiff)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable bias expdiff-rewrite))))

(defthmd expq-expdiff
  (implies (not (specialp))
           (equal (si (expq) 13)
	          (if (< (siga) (sigb))
                      (1- (si (expdiff) 13))
		    (si (expdiff) 13))))
  :hints (("Goal" :in-theory (enable si sigaltsigb-rewrite expq)
                  :use (si-expdiff-bounds (:instance si-bits (n 13) (x (1- (si (expdiff) 13))))))))

(defthm integerp-expq
  (implies (not (specialp))
           (integerp (expq)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable expq))))

(defthmd quotient-expq
  (implies (not (specialp))
           (equal (abs (/ (a) (b)))
	          (* (expt 2 (- (si (expq) 13) (bias (f))))
		     (/ (x) (d)))))
  :hints (("Goal" :use (fnum-vals quotient-formula)
                  :in-theory (enable f dp sp hp expw si bias siga-rewrite sigb-rewrite expq-expdiff x d))))

(defthmd m-monotone
  (implies (and (not (specialp))
		(member k '(-3 -2 -1 0 1 2 3 4))
		(member l '(-3 -2 -1 0 1 2 3 4))
		(< k l))
	   (< (m k (bits (div) 65 60)) (m l (bits (div) 65 60))))
  :hints (("Goal" :in-theory (enable m si computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(defthm p-vals
  (member (p) '(53 24 11))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p prec dp sp hp f)
                  :use (fnum-vals))))

(defthmd q-vals
  (member (q j) '(-4 -3 -2 -1 0 1 2 3 4))
  :hints (("Goal" :in-theory (enable q-1 nextdigit)
                  :expand ((q j) (q 1)))))

(defthm integerp-q
  (integerp (q j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (q-vals))))

(local-in-theory (enable quotient))

(defthm rat-quot
  (implies (natp j)
           (rationalp (quotient j)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd int-4*n
  (implies (integerp n)
           (integerp (* 4 n))))

(local-defthmd int-quot-1
  (implies (and (natp j) (natp n))
           (= (* (QUOTIENT (+ -2 J)) (EXPT n (+ -1 J)))
              (* n (* (QUOTIENT (+ -2 J)) (EXPT n (+ -2 J)))))))

(local-defthm int-quot-2
  (implies (and (natp j)
                (INTEGERP (* (QUOTIENT (+ -2 J)) (EXPT 8 (+ -2 J)))))
           (INTEGERP (* (QUOTIENT (+ -2 J)) (EXPT 8 (+ -1 J)))))
  :hints (("Goal" :use ((:instance int-quot-1 (n 8))
                        (:instance int-4*n (n (* (QUOTIENT (+ -2 J)) (EXPT 8 (+ -2 J)))))))))

(defthmd int-quot
  (implies (natp j)
           (integerp (* (expt 8 (1- j)) (quotient j))))
  :hints (("Goal" :induct (quotient j))))

(local-defthm int-r-1
  (implies (and (not (specialp))
                (not (zp j)))
           (and (integerp (* (expt 2 (p)) (d)))
                (integerp (* (expt 8 (1- j)) (quotient j)))))
  :hints (("Goal" :use (int-quot p-vals exactp-b)
                  :in-theory (enable d))))

(local-defthm int-r-2
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (* (* (expt 2 (p)) (d))
                     (* (expt 8 (1- j)) (quotient j)))
                  (* (D) (QUOTIENT J) (EXPT 2 (+ -3 (P) (* 3 J))))))
  :hints (("Goal" :use (int-quot p-vals))))

(local-defthmd int-r-3
  (implies (and (integerp m) (integerp n))
           (integerp (* m n))))

(local-defthmd int-r-4
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (D) (QUOTIENT J) (EXPT 2 (+ -3 (P) (* 3 J))))))
  :hints (("Goal" :use (int-r-1 int-r-2 (:instance int-r-3 (m (* (expt 2 (p)) (d))) (n (* (expt 8 (1- j)) (quotient j)))))
                  :in-theory (theory 'minimal-theory))))

(local-defthmd int-r-5
  (implies (and (not (specialp))
                (not (zp j)))
           (and (integerp (expt 8 (1- j)))
	        (integerp (* (expt 2 (p)) (x)))))
  :hints (("Goal" :in-theory (enable x)
                  :use (p-vals exactp-a))))

(local-defthmd int-r-6
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (* (expt 8 (1- j)) (* (expt 2 (p)) (x)))
	          (* (X) (EXPT 2 (+ -3 (P) (* 3 J))))))
  :hints (("Goal" :use p-vals)))

(local-defthmd int-r-7
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (X) (EXPT 2 (+ -3 (P) (* 3 J))))))
  :hints (("Goal" :use (int-r-5 int-r-6 (:instance int-r-3 (m (expt 8 (1- j))) (n (* (expt 2 (p)) (x)))))
                  :in-theory (theory 'minimal-theory))))

(defthmd int-r
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (expt 2 (p)) (r j))))
  :hints (("Goal" :expand ((:free (j) (r j)))  
                  :use (p-vals int-r-4 int-r-7))))

(defthmd q1-max-1
  (implies (not (specialp))
           (member (q 1) '(1 2)))
  :hints (("Goal" :in-theory (enable q q-1))))

(defthmd q1-max-2
  (implies (not (specialp))
           (and (< (rp-1) (expt 2 71))
	        (>= (rp-1) (expt 2 66))))
  :hints (("Goal" :in-theory (enable rp1-rewrite x)
                  :use (siga-bounds siga-rewrite))))

(local-defthmd q1-max-3
  (implies (not (specialp))
           (>= (rs10-0) (expt 2 5)))
  :hints (("Goal" :in-theory (enable bvecp rs10-0)
                  :use (q1-max-2
		        (:instance bits-plus-bits (x (rp-1)) (n 70) (m 0) (p 61))
			(:instance bits-bounds (x (rp-1)) (i 60) (j 0))))))

(local-defthmd q1-max-4
  (implies (not (specialp))
           (and (>= (ag 4 (cmpconst)) 992)
	        (< (ag 4 (cmpconst)) 1024)))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(local-defthmd q1-max-5
  (implies (not (specialp))
           (equal (bitn (ag 4 (cmpconst)) 9) 1))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(defthm int-cmpconst
  (implies (member k '(0 1 2 3 4 5 6 7 8))
           (integerp (ag k (computecmpconst (bits (div) 65 60)))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable computecmpconst si))))

(defthmd q1-max-6
  (implies (not (specialp))
           (<= (m 1 (bits (div) 65 60))
	       (/ (rs10-0) 64)))
  :hints (("Goal" :in-theory (enable cmpconst m si)
                  :use (q1-max-3 q1-max-4 q1-max-5))))

(local-defthmd q1-max-7
  (implies (not (specialp))
           (< (rp-1) (* 2 (div))))
  :hints (("Goal" :in-theory (enable rp1-rewrite div-rewrite)
                  :use (x-bounds))))

(local-defthmd q1-max-8
  (implies (not (specialp))
           (<= (rs10-0) (bits (div) 69 60)))
  :hints (("Goal" :in-theory (enable rs10-0 bvecp)
                  :use (q1-max-2 q1-max-7 div-bounds
		        (:instance bits-plus-bits (x (rp-1)) (n 70) (p 61) (m 0))
			(:instance bits-plus-bits (x (div)) (n 69) (p 60) (m 0))
		        (:instance bits-bounds (x (rp-1)) (i 60) (j 0))
		        (:instance bits-bounds (x (div)) (i 59) (j 0))))))

(local-defthmd q1-max-9
  (implies (not (specialp))
           (equal (bits (div) 69 66) 1))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (div-bounds
			(:instance bits-plus-bits (x (div)) (n 69) (p 66) (m 0))
		        (:instance bits-bounds (x (div)) (i 65) (j 0))))))

(local-defthmd q1-max-10
  (implies (not (specialp))
           (<= (rs10-0) (+ 64 (bits (div) 65 60))))
  :hints (("Goal" :in-theory (enable rs10-0 bvecp)
                  :use (q1-max-8 q1-max-9
			(:instance bits-plus-bits (x (div)) (n 69) (p 66) (m 60))))))

(defthmd rs10-0-9
  (implies (not (specialp))
           (equal (bitn (rs10-0) 9) 0))
  :hints (("Goal" :use (q1-max-10
                        (:instance bits-bounds (x (div)) (i 65) (j 60)))
		  :in-theory (enable bvecp rs10-0))))

(local-defthmd q1-max-11
  (implies (not (specialp))
           (and (> (ag 6 (cmpconst)) 512)
	        (< (ag 6 (cmpconst)) 1024)))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(local-defthmd q1-max-12
  (implies (not (specialp))
           (equal (bitn (ag 6 (cmpconst)) 9) 1))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(local-defthmd q1-max-13
  (implies (not (specialp))
           (> (- 1024 (ag 6 (cmpconst)))
	      (+ 64 (bits (div) 65 60))))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(defthmd q1-max-14
  (implies (not (specialp))
           (> (m 3 (bits (div) 65 60))
	      (/ (rs10-0) 64)))
  :hints (("Goal" :in-theory (enable cmpconst m si)
                  :use (q1-max-10 q1-max-12 q1-max-13))))

(local-defthmd q1-max-15
  (implies (not (specialp))
           (and (> (ag 5 (cmpconst)) 512)
	        (< (ag 5 (cmpconst)) 1024)))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(local-defthmd q1-max-16
  (implies (not (specialp))
           (equal (bitn (ag 5 (cmpconst)) 9) 1))
  :hints (("Goal" :in-theory (enable cmpconst computecmpconst)
                  :use ((:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(local-defthmd q1-max-17
  (implies (not (specialp))
           (equal (q 1)
	          (if (>= (+ (rs10-0) (ag 5 (cmpconst))) 1024)
		      2 1)))
  :hints (("Goal" :in-theory (enable cmpconst q q-1 rs10-0 gep2 bvecp)
                  :use (q1-max-15
                        (:instance bits-bounds (x (rp-1)) (i 70) (j 61))
			(:instance bits-bounds (x (gep2)) (i 9) (j 0))
			(:instance bitn-plus-bits (x (gep2)) (n 10) (m 0))
			(:instance bitn-0-1 (x (gep2)) (n 10))))))

(local-defthmd q1-max-18
  (implies (not (specialp))
           (equal (q 1)
	          (if (<= (m 2 (bits (div) 65 60))
		          (/ (rs10-0) 64))
		      2 1)))
  :hints (("Goal" :in-theory (enable si m q1-max-17 cmpconst rs10-0)
                  :use (q1-max-16))))

(defthmd q1-max
  (implies (not (specialp))
           (equal (q 1)
	          (maxk (/ (rs10-0) 64))))
  :hints (("Goal" :in-theory (enable q1-max-18 maxk)
                  :use (q1-max-6 q1-max-14
		        (:instance m-monotone (k 2) (l 3))
		        (:instance m-monotone (k 3) (l 4))))))

(local-defthmd a0-error-1
  (implies (not (specialp))
           (equal (rp-1)
	          (+ (* (expt 2 61) (rs10-0))
		     (bits (rp-1) 60 0))))
  :hints (("Goal" :in-theory (enable rp-1 rs10-0)
                  :use (q1-max-2 
		        (:instance bits-plus-bits (x (rp-1)) (n 70) (p 61) (m 0))))))

(local-defthmd a0-error-2
  (implies (not (specialp))
           (equal (* (expt 2 67) (x))
	          (+ (* (expt 2 61) (rs10-0))
		     (bits (rp-1) 60 0))))
  :hints (("Goal" :use (a0-error-1 rp1-rewrite))))

(defthmd a0-error
  (implies (not (specialp))
           (< (abs (- (/ (rs10-0) 64)
	              (* 8 (r 0))))
	      1/64))
  :hints (("Goal" :use (a0-error-2 (:instance bits-bounds (x (rp-1)) (i 60) (j 0)))
                  :in-theory (enable r0-rewrite))))

(defthmd r1-bound
  (implies (not (specialp))
           (<= (abs (r 1)) (* 4/7 (d))))
  :hints (("Goal" :use (a0-error q1-max r0-bound (:instance r-bound-inv (j 0) (approx (/ (rs10-0) 64)))))))

(defthmd rn1-rewrite
  (implies (not (specialp))
           (equal (rn-1)
	          (* (expt 2 67) (q 1) (d))))
  :hints (("Goal" :in-theory (enable q rn-1 q-1 div-rewrite div2-rewrite))))

(defthmd r1-rp1-rn1
  (implies (not (specialp))
           (equal (* (expt 2 67) (r 1))
	          (- (rp 1) (rn 1))))
  :hints (("Goal" :in-theory (enable rp1-rewrite rn1-rewrite rp rn r quotient)
                  :expand ((quotient 1)))))

(local-defthmd bits-rp1-0-1
  (implies (not (specialp))
           (integerp (* (expt 2 (- (p) 67)) (rp-1))))
  :hints (("Goal" :in-theory (enable rp1-rewrite x)
                  :use (p-vals exactp-a))))

(defthmd bits-rp1-0
  (implies (not (specialp))
           (equal (bits (rp 1) (- 66 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable rp)
                  :use (p-vals bits-rp1-0-1 (:instance exact-bits-3 (x (rp-1)) (k (- 67 (p))))))))

(local-defthmd bits-rn1-0-1
  (implies (not (specialp))
           (integerp (* (expt 2 (- (p) 67)) (rn-1))))
  :hints (("Goal" :in-theory (enable q q-1 rn1-rewrite d)
                  :use (p-vals exactp-b))))

(defthmd bits-rn1-0
  (implies (not (specialp))
           (equal (bits (rn 1) (- 66 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable rn)
                  :use (p-vals bits-rn1-0-1 (:instance exact-bits-3 (x (rn-1)) (k (- 67 (p))))))))
