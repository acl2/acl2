(in-package "RTL")

(include-book "quot")

(local-defthmd q-error-1
  (implies (and (not (earlyp))
                (natp j))
           (equal (- (/ (x) (d)) (quotient j))
	          (/ (* (expt 8 (- 1 j)) (r j))
		     (d))))
  :hints (("Goal" :in-theory (enable r) :use (d-bounds))))

(local-defthmd q-error-2
  (implies (not (earlyp))
           (equal (- (/ (x) (d)) (qf))
	          (/ (* (expt 8 (- (1- (n)))) (rf))
		     (d))))
  :hints (("Goal" :in-theory (enable rf qf) :use ((:instance q-error-1 (j (n)))))))

(local-defthmd q-error-3
  (implies (not (earlyp))
           (<= (abs (/ (* (expt 8 (- (1- (n)))) (rf)) (d)))
	       (* 4/7 (expt 8 (- (1- (n)))))))
  :hints (("Goal" :use (d-bounds rf-bound) :nonlinearp t)))

(defthmd q-error
  (implies (not (earlyp))
           (<= (abs (- (/ (x) (d)) (qf)))
	       (* 4/7 (expt 8 (- (1- (n)))))))
  :hints (("Goal" :use (d-bounds q-error-2 q-error-3))))

(defthmd int-rf
  (implies (not (earlyp))
	   (integerp (* (expt 2 67) (rf))))
  :hints (("Goal" :in-theory (enable rf p)
	          :use ((:instance int-r (j (n)))))))

(local-defthmd rdiff-rewrite
  (implies (not (earlyp))
           (equal (rdiff) (bits (* (expt 2 67) (rf)) 70 0)))
  :hints (("Goal" :in-theory (enable bvecp rdiff lognot bits-mod)
                  :use (int-rf bvecp-rpf-rnf rf-rpf-rnf))))

(local-defthmd bitn-rdiff-rewrite
  (implies (not (earlyp))
           (equal (bitn (rdiff) 70)
	          (if (< (rf) 0) 1 0)))
  :hints (("Goal" :in-theory (enable bvecp rdiff-rewrite bitn-bits)
                  :use (int-rf rf-bound d-bounds))))

(defund quotsgn () (if1 (sgnq) (- (qf)) (qf)))

(in-theory (disable (quotsgn)))

(local-defthmd qf-bound-1
  (implies (not (earlyp))
           (<= (* (expt 8 (1- (n))) (qf))
	       (+ (* (expt 8 (1- (n))) (/ (x) (d)))
	          4/7)))
  :hints (("Goal" :use (q-error)
                  :nonlinearp t)))

(local-defthmd qf-bound-2
  (implies (and (not (earlyp))
                (<= (n) 21))
           (< (+ 4 (* (expt 8 (1- (n))) (qf)))
	      (expt 2 64)))
  :hints (("Goal" :use (qf-bound-1 x-bounds d-bounds)
                  :nonlinearp t)))

(local-defthmd qf-bound-3
  (implies (and (not (earlyp))
                (= (n) 22))
           (member (del) '(61 62)))
  :hints (("Goal" :in-theory (enable n del-bounds bvecp)
                  :use ((:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd qf-bound-4
  (implies (and (not (earlyp))
                (= (del) 62))
           (and (equal (expo (a0)) 63)
	        (equal (expo (b0)) 1)))
  :hints (("Goal" :in-theory (enable del clza-rewrite clzb-rewrite)
                  :use (a0-rewrite b0-rewrite clza>=0 b0<=a0 b0<>0 clzb<=62))))

(local-defthmd qf-bound-5
  (implies (and (not (earlyp))
                (= (del) 61))
           (or (and (equal (expo (a0)) 62)
	            (equal (expo (b0)) 1))
	       (and (equal (expo (a0)) 63)
	            (equal (expo (b0)) 2))))
  :hints (("Goal" :in-theory (enable del clza-rewrite clzb-rewrite)
                  :use (a0-rewrite b0-rewrite clza>=0 b0<=a0 b0<>0 clzb<=62))))

(local-defthmd qf-bound-6
  (implies (and (not (earlyp))
                (= (del) 62))
           (< (abs (a0)) (expt 2 64)))
  :hints (("Goal" :use (qf-bound-4
                        (:instance expo-upper-bound (x (a0)))))))

(local-defthmd qf-bound-7
  (implies (not (earlyp))
	   (not (member (b0) '(1 -1 2 -2 4 -4))))
  :hints (("Goal" :in-theory (enable ispow2 earlyp mskb-rewrite sgnb-b0))))

(local-defthmd qf-bound-8
  (implies (and (not (earlyp))
                (= (del) 62))
           (>= (abs (b0)) 3))
  :hints (("Goal" :use (qf-bound-4 qf-bound-7
                        (:instance expo-lower-bound (x (b0)))))))

(local-defthmd qf-bound-9
  (implies (and (not (earlyp))
                (= (del) 62))
           (< (abs (/ (x) (d))) 4/3))
  :hints (("Goal" :use (qf-bound-6 qf-bound-8 quotient-x-d)
                  :nonlinearp t)))

(local-defthmd qf-bound-10
  (implies (and (not (earlyp))
                (= (del) 61)
                (equal (expo (a0)) 62)
	        (equal (expo (b0)) 1))
           (< (abs (a0)) (expt 2 63)))
  :hints (("Goal" :use (qf-bound-4
                        (:instance expo-upper-bound (x (a0)))))))

(local-defthmd qf-bound-11
  (implies (and (not (earlyp))
                (= (del) 61)
                (equal (expo (a0)) 62)
	        (equal (expo (b0)) 1))
           (>= (abs (b0)) 3))
  :hints (("Goal" :use (qf-bound-4 qf-bound-7
                        (:instance expo-lower-bound (x (b0)))))))

(local-defthmd qf-bound-12
  (implies (and (not (earlyp))
                (= (del) 61)
                (equal (expo (a0)) 62)
	        (equal (expo (b0)) 1))
           (< (abs (/ (x) (d))) 4/3))
  :hints (("Goal" :use (qf-bound-10 qf-bound-11 quotient-x-d)
                  :nonlinearp t)))

(local-defthmd qf-bound-13
  (implies (and (not (earlyp))
                (= (del) 61)
                (equal (expo (a0)) 63)
	        (equal (expo (b0)) 2))
           (< (abs (a0)) (expt 2 64)))
  :hints (("Goal" :use (qf-bound-4
                        (:instance expo-upper-bound (x (a0)))))))

(local-defthmd qf-bound-14
  (implies (and (not (earlyp))
                (= (del) 61)
                (equal (expo (a0)) 63)
	        (equal (expo (b0)) 2))
           (>= (abs (b0)) 5))
  :hints (("Goal" :use (qf-bound-4 qf-bound-7
                        (:instance expo-lower-bound (x (b0)))))))

(local-defthmd qf-bound-15
  (implies (and (not (earlyp))
                (= (del) 61)
                (equal (expo (a0)) 63)
	        (equal (expo (b0)) 2))
           (< (abs (/ (x) (d))) 8/5))
  :hints (("Goal" :use (qf-bound-13 qf-bound-14 quotient-x-d)
                  :nonlinearp t)))

(local-defthmd qf-bound-16
  (implies (and (not (earlyp))
                (= (n) 22))
           (< (abs (/ (x) (d))) 8/5))
  :hints (("Goal" :use (qf-bound-3 qf-bound-4 qf-bound-5 qf-bound-9 qf-bound-12 qf-bound-15 quotient-x-d))))

(local-defthmd qf-bound-18
  (implies (and (not (earlyp))
                (= (n) 22))
           (< (+ 4 (* (expt 8 (1- (n))) (qf)))
	      (expt 2 64)))
  :hints (("Goal" :use (qf-bound-1 qf-bound-16)
                  :nonlinearp t)))

(local-defthmd qf-bound
  (implies (not (earlyp))
           (< (+ 4 (* (expt 8 (1- (n))) (qf)))
	      (expt 2 64)))
  :hints (("Goal" :use (qf-bound-2 qf-bound-18 n-bounds))))

(local-defthmd int-qf
  (implies (not (earlyp))
	   (and (integerp (* (expt 8 (1- (n))) (qf)))
	        (integerp (quotf))
		(integerp (quotmf))
		(> (* (expt 8 (1- (n))) (qf)) 0)))
  :hints (("Goal" :in-theory (enable bvecp)
	          :use (sgnq-0-1 quotf-pos quotf-neg))))

(defthmd si-quotf-rewrite
  (implies (not (earlyp))
           (equal (si (quotf) 65)
	          (* (expt 8 (1- (n))) (quotsgn))))
  :hints (("Goal" :in-theory (enable bvecp bvecp-bitn-1 quotsgn si quotf-pos quotf-neg)
                  :use (int-qf sgnq-0-1 qf-bound))))

(defthmd si-quotmf-rewrite
  (implies (not (earlyp))
           (equal (si (quotmf) 65)
	          (1- (si (quotf) 65))))
  :hints (("Goal" :in-theory (enable bvecp bvecp-bitn-1 quotsgn si quotf-pos quotf-neg)
                  :use (int-qf sgnq-0-1 qf-bound))))

(local-defthmd bvecp-quotpf
  (implies (not (earlyp))
           (bvecp (quotpf) 65))
  :hints (("Goal" :in-theory (enable quotpf-rewrite incquot)
                  :expand ((quotp (n))))))

(defthmd si-quotpf-rewrite
  (implies (and (not (earlyp))
                (not (= (qf) 1/2)))
           (equal (si (quotpf) 65)
	          (+ (expt 2 (k)) (si (quotf) 65))))
  :hints (("Goal" :in-theory (enable si-quotf-rewrite k bvecp bvecp-bitn-1 quotsgn si quotpf-n=2-pos
                                     quotpf-n=2-neg quotpf-sgnq=0 quotpf-sgnq=1)
                  :cases ((= (n) 2))
                  :use (bvecp-quotpf int-qf sgnq-0-1 qf-bound n-bounds))))

;;*************************************************************************************************************

(local-defthmd a-b-q-1
  (implies (not (earlyp))
           (integerp (* (expt 2 (k))
	                (expt 2 (del))
			(quotsgn))))
  :hints (("Goal" :in-theory (enable k n bvecp quotsgn)
                  :use (int-qf del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd a-b-q-2
  (implies (not (earlyp))
           (equal (abs (- (/ (a0) (b0)) (* (expt 2 (del)) (quotsgn))))
	          (* (expt 2 (del)) (abs (- (/ (x) (d)) (qf))))))
  :hints (("Goal" :in-theory (enable quotsgn sgnq sgna-a0 sgnb-b0 bvecp)
                  :use (quotient-x-d)
		  :nonlinearp t)))

(local-defthmd a-b-q-3
  (implies (not (earlyp))
           (< (* (expt 2 (del)) (abs (- (/ (x) (d)) (qf))))
	      (* (expt 2 (del)) (expt 8 (- 1 (n))))))
  :hints (("Goal" :use (q-error)
                  :nonlinearp t)))

(local-defthmd a-b-q-4
  (implies (not (earlyp))
           (< (* (expt 2 (del)) (abs (- (/ (x) (d)) (qf))))
	      (expt 2 (- (k)))))
  :hints (("Goal" :in-theory (enable k n bvecp)
                  :use (a-b-q-3 del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd a-b-q-5
  (implies (not (earlyp))
           (< (abs (- (/ (a0) (b0)) (* (expt 2 (del)) (quotsgn))))
	      (expt 2 (- (k)))))
  :hints (("Goal" :use (a-b-q-2 a-b-q-4))))

(local-defthmd a-b-q-6
  (implies (not (earlyp))
           (< (- (* (expt 2 (del)) (quotsgn))
	         (fl (* (expt 2 (del)) (quotsgn))))
	      1)))

(local-defthmd a-b-q-7
  (implies (not (earlyp))
           (< (- (* (expt 2 (k)) (expt 2 (del)) (quotsgn))
	         (* (expt 2 (k)) (fl (* (expt 2 (del)) (quotsgn)))))
	      (expt 2 (k))))
  :hints (("Goal" :use (a-b-q-6))))

(local-defthmd a-b-q-8
  (implies (not (earlyp))
           (<= (- (* (expt 2 (k)) (expt 2 (del)) (quotsgn))
	          (* (expt 2 (k)) (fl (* (expt 2 (del)) (quotsgn)))))
	       (1- (expt 2 (k)))))
  :hints (("Goal" :use (a-b-q-7 a-b-q-1 del-bounds (:instance bvecp-member (x (del)) (n 6)))
                  :in-theory (enable k bvecp))))

(local-defthmd a-b-q-9
  (implies (not (earlyp))
           (<= (- (* (expt 2 (del)) (quotsgn))
	          (fl (* (expt 2 (del)) (quotsgn))))
	       (- 1 (expt 2 (- (k))))))
  :hints (("Goal" :use (a-b-q-8)
                  :nonlinearp t)))

(local-defthmd a-b-q-10
  (implies (not (earlyp))
           (< (abs (- (/ (a0) (b0)) (fl (* (expt 2 (del)) (quotsgn)))))
	      1))
  :hints (("Goal" :use (a-b-q-5 a-b-q-9))))

(local-defthmd a-b-q-pos-1
  (implies (and (not (earlyp))
                (= (sgnq) 0))
           (equal (i) (fl (/ (a0) (b0)))))
  :hints (("Goal" :in-theory (enable i-rewrite iquot sgnq sgna-a0 sgnb-b0))))

(local-defthmd r-sign
  (implies (not (earlyp))
           (iff (< (rf) 0)
	        (< (/ (x) (d)) (qf))))
  :hints (("Goal" :in-theory (enable rf r qf)
                  :use (d-bounds)
                  :nonlinearp t)))

(local-defthmd a-b-q-pos-3
  (implies (and (not (earlyp))
                (= (sgnq) 0))
           (iff (< (rf) 0)
	        (< (/ (a0) (b0)) (* (expt 2 (del)) (qf)))))
  :hints (("Goal" :in-theory (enable sgnq sgna-a0 sgnb-b0)
                  :use (quotient-x-d r-sign)
		  :nonlinearp t)))

(local-defthmd a-b-q-pos-4
  (implies (and (not (earlyp))
                (= (sgnq) 0)
		(integerp (* (expt 2 (del)) (qf))))
           (iff (< (rf) 0)
	        (< (/ (a0) (b0)) (fl (* (expt 2 (del)) (qf))))))
  :hints (("Goal" :use (a-b-q-pos-3))))

(local-defthmd a-b-q-pos-5
  (implies (and (not (earlyp))
                (= (sgnq) 0)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (< (* (expt 2 (k)) (fl (* (expt 2 (del)) (qf))))
	      (* (expt 2 (k)) (expt 2 (del)) (qf)))))

(local-defthmd a-b-q-pos-6
  (implies (and (not (earlyp))
                (= (sgnq) 0)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (<= (* (expt 2 (k)) (fl (* (expt 2 (del)) (qf))))
	       (1- (* (expt 2 (k)) (expt 2 (del)) (qf)))))
  :hints (("Goal" :use (a-b-q-pos-5 a-b-q-1 del-bounds
                        (:instance bvecp-member (x (del)) (n 6)))
                  :in-theory (enable quotsgn k bvecp)
		  :nonlinearp t)))

(local-defthmd a-b-q-pos-7
  (implies (and (not (earlyp))
                (= (sgnq) 0)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (<= (fl (* (expt 2 (del)) (qf)))
	       (- (* (expt 2 (del)) (qf))
	          (expt 2 (- (k))))))
  :hints (("Goal" :use (a-b-q-pos-6 del-bounds
                        (:instance bvecp-member (x (del)) (n 6)))
                  :in-theory (enable k bvecp)
		  :nonlinearp t)))

(local-defthmd a-b-q-pos-8
  (implies (and (not (earlyp))
                (= (sgnq) 0)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (< (fl (* (expt 2 (del)) (qf)))
	       (/ (a0) (b0))))
  :hints (("Goal" :use (a-b-q-pos-7 a-b-q-5)
                  :in-theory (enable quotsgn))))

(local-defthmd a-b-q-pos-9
  (implies (and (not (earlyp))
                (= (sgnq) 0))
           (iff (> (fl (* (expt 2 (del)) (qf)))
	           (/ (a0) (b0)))
		(and (integerp (* (expt 2 (del)) (qf)))
		     (< (rf) 0))))
  :hints (("Goal" :use (a-b-q-pos-4 a-b-q-pos-8))))

(defthmd a-b-q-pos
  (implies (and (not (earlyp))
                (= (sgnq) 0))
	   (equal (i)
	          (if (and (integerp (* (expt 2 (del)) (qf)))
		           (< (rf) 0))
		      (1- (fl (* (expt 2 (del)) (quotsgn))))
		    (fl (* (expt 2 (del)) (quotsgn))))))
  :hints (("Goal" :in-theory (enable a-b-q-pos-1 quotsgn)
                  :use (a-b-q-10 a-b-q-pos-9))))

(local-defthmd a-b-q-neg-1
  (implies (and (not (earlyp))
                (= (sgnq) 1))
           (equal (i) (cg (/ (a0) (b0)))))
  :hints (("Goal" :in-theory (enable i-rewrite iquot sgnq sgna-a0 sgnb-b0))))

(local-defthmd a-b-q-neg-3
  (implies (and (not (earlyp))
                (= (sgnq) 1))
           (iff (< (rf) 0)
	        (> (/ (a0) (b0)) (- (* (expt 2 (del)) (qf))))))
  :hints (("Goal" :in-theory (enable sgnq sgna-a0 sgnb-b0)
                  :use (quotient-x-d r-sign)
		  :nonlinearp t)))

(local-defthmd a-b-q-neg-4
  (implies (and (not (earlyp))
                (= (sgnq) 1)
		(integerp (* (expt 2 (del)) (qf))))
           (iff (< (rf) 0)
	        (> (/ (a0) (b0)) (fl (- (* (expt 2 (del)) (qf)))))))
  :hints (("Goal" :use (a-b-q-neg-3))))

(local-defthmd a-b-q-neg-5
  (implies (and (not (earlyp))
                (= (sgnq) 1)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (< (* (expt 2 (k)) (fl (- (* (expt 2 (del)) (qf)))))
	      (* (expt 2 (k)) (- (* (expt 2 (del)) (qf)))))))

(local-defthmd a-b-q-neg-6
  (implies (and (not (earlyp))
                (= (sgnq) 1)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (<= (* (expt 2 (k)) (fl (- (* (expt 2 (del)) (qf)))))
	       (1- (* (expt 2 (k)) (- (* (expt 2 (del)) (qf)))))))
  :hints (("Goal" :use (a-b-q-neg-5 a-b-q-1 del-bounds
                        (:instance bvecp-member (x (del)) (n 6)))
                  :in-theory (enable quotsgn k bvecp)
		  :nonlinearp t)))

(local-defthmd a-b-q-neg-7
  (implies (and (not (earlyp))
                (= (sgnq) 1)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (<= (fl (- (* (expt 2 (del)) (qf))))
	       (- (- (* (expt 2 (del)) (qf)))
	          (expt 2 (- (k))))))
  :hints (("Goal" :use (a-b-q-neg-6 del-bounds
                        (:instance bvecp-member (x (del)) (n 6)))
                  :in-theory (enable k bvecp)
		  :nonlinearp t)))

(local-defthmd a-b-q-neg-8
  (implies (and (not (earlyp))
                (= (sgnq) 1)
		(not (integerp (* (expt 2 (del)) (qf)))))
           (< (fl (- (* (expt 2 (del)) (qf))))
	       (/ (a0) (b0))))
  :hints (("Goal" :use (a-b-q-neg-7 a-b-q-5)
                  :in-theory (enable quotsgn))))

(local-defthmd a-b-q-neg-9
  (implies (and (not (earlyp))
                (= (sgnq) 1))
           (iff (>= (fl (- (* (expt 2 (del)) (qf))))
	            (/ (a0) (b0)))
		(and (integerp (* (expt 2 (del)) (qf)))
		     (>= (rf) 0))))
  :hints (("Goal" :use (a-b-q-neg-4 a-b-q-neg-8))))

(defthmd a-b-q-neg
  (implies (and (not (earlyp))
                (= (sgnq) 1))
	   (equal (i)
	          (if (and (integerp (* (expt 2 (del)) (qf)))
		           (>= (rf) 0))
		      (fl (* (expt 2 (del)) (quotsgn)))
		    (1+ (fl (* (expt 2 (del)) (quotsgn)))))))
  :hints (("Goal" :in-theory (enable a-b-q-neg-1 quotsgn)
                  :use (a-b-q-10 a-b-q-neg-9))))

;;*************************************************************************************************************

(local-defthmd d-i-1
  (implies (not (earlyp))
           (equal (* (expt 2 (- (k))) (si (quotf) 65))
	          (* (expt 2 (del)) (quotsgn))))
  :hints (("Goal" :in-theory (enable si-quotf-rewrite k n bvecp)
                  :use (del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd d-i-2
  (implies (not (earlyp))
           (equal (islost)
	          (if (= (mod (si (quotf) 65) (expt 2 (k))) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable bits-mod k n bvecp si islost)
                  :use (del-bounds int-qf
		        (:instance logand-bits (x (si (quotf) 65)) (n (k)) (k 0))
		        (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd d-i-3
  (implies (not (earlyp))
           (equal (islost)
	          (if (integerp (* (expt 2 (- (k))) (si (quotf) 65)))
		      0 1)))
  :hints (("Goal" :in-theory (enable k n bvecp si d-i-2)
                  :use (del-bounds int-qf
		        (:instance mod-equal-int (a (si (quotf) 65)) (b 0) (n (expt 2 (k))))
		        (:instance mod-equal-int-reverse (a (si (quotf) 65)) (b 0) (n (expt 2 (k))))
		        (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd d-i-4
  (implies (not (earlyp))
           (equal (islost)
	          (if (integerp (* (expt 2 (del)) (quotsgn)))
		      0 1)))
  :hints (("Goal" :use (d-i-1 d-i-3))))

(local-defthmd d-i-5
  (implies (not (earlyp))
           (integerp (si (quotf) 65)))
  :hints (("Goal" :in-theory (enable si)
                  :use (int-qf))))

(local-defthmd d-i-6
  (implies (not (earlyp))
           (equal (quot0)
	          (bits (fl (* (expt 2 (del)) (quotsgn))) 63 0)))
  :hints (("Goal" :in-theory (enable k quot0 si-quotf-rewrite n k bvecp)
                  :use (del-bounds d-i-5 (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd d-i-7
  (implies (not (earlyp))
           (equal (quotm0)
	          (bits (fl (- (* (expt 2 (del)) (quotsgn)) (expt 2 (- (k))))) 63 0)))
  :hints (("Goal" :in-theory (enable k quotm0 si-quotf-rewrite si-quotmf-rewrite n k bvecp)
                  :use (del-bounds d-i-5 (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd d-i-8
  (implies (and (not (earlyp))
                (not (= (qf) 1/2)))
           (equal (quotp0)
	          (bits (fl (1+ (* (expt 2 (del)) (quotsgn)))) 63 0)))
  :hints (("Goal" :in-theory (enable k quotp0 si-quotf-rewrite si-quotpf-rewrite n k bvecp)
                  :use (del-bounds d-i-5 (:instance bvecp-member (x (del)) (n 6))))))

(local-defthmd d-i-9
  (implies (not (earlyp))
           (equal (data)
                  (if1 (logand1 (sgnq) (logior1 (islost) (bitn (rdiff) 70)))
                       (quotp0)
                     (if1 (logand1 (logand1 (lognot1 (sgnq)) (lognot1 (islost))) (bitn (rdiff) 70))
                          (quotm0)
                        (quot0)))))
  :hints (("Goal" :in-theory (enable earlyp data))))

(local-defthmd d-i-10
  (implies (not (earlyp))
           (equal (i)
                  (if1 (logand1 (sgnq) (logior1 (islost) (bitn (rdiff) 70)))
                       (fl (1+ (* (expt 2 (del)) (quotsgn))))
                     (if1 (logand1 (logand1 (lognot1 (sgnq)) (lognot1 (islost))) (bitn (rdiff) 70))
                          (1- (* (expt 2 (del)) (quotsgn)))
                        (fl (* (expt 2 (del)) (quotsgn)))))))
  :hints (("Goal" :in-theory (enable a-b-q-neg a-b-q-pos d-i-4 quotsgn bitn-rdiff-rewrite)
                  :use (sgnq-0-1))))

(local-defthmd d-i-11
  (implies (and (not (earlyp))
                (equal (islost) 0))
	   (equal (fl (- (* (expt 2 (del)) (quotsgn)) (expt 2 (- (k)))))
	          (1- (* (expt 2 (del)) (quotsgn)))))
  :hints (("Goal" :in-theory (enable k d-i-4))))

(local-defthmd d-i-12
  (implies (and (not (earlyp))
                (= (qf) 1/2))
	   (equal (islost) 0))
  :hints (("Goal" :in-theory (enable d-i-4 quotsgn) :use (del-bounds))))

(local-defthmd d-i-13
  (implies (and (not (earlyp))
                (= (qf) 1/2))
	   (equal (bitn (rdiff) 70) 0))
  :hints (("Goal" :in-theory (enable bitn-rdiff-rewrite)
                  :nonlinearp t
                  :use (x-bounds d-bounds r-sign))))

(local-defthmd d-i-14
  (implies (not (earlyp))
	   (equal (data) (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable k d-i-6 d-i-7 d-i-8 d-i-9 d-i-10 d-i-12 d-i-13)
                  :cases ((= (qf) 1/2))
                  :use (d-i-11))))

(local-defthmd data-i
   (equal (data)
	  (if (= (b) 0)
              0
	    (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable b0-rewrite) :use (b0<>0 early-case d-i-14))))

(defthmd idiv8-main
  (equal (data) (idiv-spec (opa) (opb) (int32) (sgnd)))
  :hints (("Goal" :in-theory (enable data-i idiv-spec i a b))))

(defthmd lemma-to-be-functionally-instantiated
  (equal (idiv8 (opa) (opb) (int32) (sgnd))
         (idiv-spec (opa) (opb) (int32) (sgnd)))
  :hints (("Goal" :in-theory (enable idiv8-main)
                  :use (idiv8-lemma))))

(local (defmacro ic ()
  '(input-constraints opa opb int32 sgnd)))

(defthmd idiv8-correct
  (implies (input-constraints opa opb int32 sgnd)
           (equal (idiv8 opa opb int32 sgnd)
                  (idiv-spec opa opb int32 sgnd)))
  :hints  (("Goal" :use ((:functional-instance lemma-to-be-functionally-instantiated
                          (opa (lambda () (if (ic) opa (opa))))
                          (opb (lambda () (if (ic) opb (opb))))
                          (int32 (lambda () (if (ic) int32 (int32))))
                          (sgnd (lambda () (if (ic) sgnd (sgnd)))))))
          ("Subgoal 1" :use (input-constraints-lemma))))







