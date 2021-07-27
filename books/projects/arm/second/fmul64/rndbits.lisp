(in-package "RTL")

(include-book "unrounded")

(local-defthmd rstk-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 55))
	   (equal (rstkmask) (1- (expt 2 (+ 52 (rshift))))))
  :hints (("Goal" :in-theory (enable cat bvecp rstkmask case-1-9)
           :nonlinearp t)))

(local-defthmd bvecp-rstkmask
  (bvecp (rstkmask) 107)
  :hints (("Goal" :in-theory (enable rstkmask))))

(local-defthmd rstk-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 55))
	   (equal (bits (rstkmask) 106 1)
	          (1- (expt 2 (+ 51 (rshift))))))
  :hints (("Goal" :in-theory (enable rstk-1 bvecp bits)
           :nonlinearp t)))

(local-defthmd rstk-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 55))
	   (equal (rstk)
	          (if (= (bits (prod) (+ 50 (rshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable rstk-2 bvecp rstk)
                  :use ((:instance logand-bits (x (prod)) (k 0) (n (+ 51 (rshift))))))))

(local-defthmd rstk-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (rshift) 55))
	   (equal (rstkmask) (1- (expt 2 107))))
  :hints (("Goal" :in-theory (enable cat bvecp rstkmask case-1-9)
                  :nonlinearp t
                  :use (rshift-bounds (:instance bvecp-member (x (rshift)) (n 6))))))

(local-defthmd rstk-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (rshift) 55))
	   (equal (rstk) 1))
  :hints (("Goal" :in-theory (enable rstk rstk-4 bvecp)
                  :use (bvecp-prod))))

(local-defthmd rstk-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (rshift) 55))
	   (not (equal (bits (prod) (+ 50 (rshift)) 0) 0)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
		  :use (rshift-bounds bvecp-prod))))

(local-defthmd rstk-7
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rstk)
	          (if (= (bits (prod) (+ 50 (rshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :use (rstk-3 rstk-5 rstk-6))))

(local-defthmd rstk-8
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rstk)
	          (if (= (bits (prod0) (+ 51 (rshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable cat bvecp prod0 ash-rewrite rstk-7)
                  :use (bvecp-prod rshift-bounds
		        (:instance bits-shift-up-2 (x (prod)) (k 1) (i (+ 50 (rshift))))))))

(local-defthmd rstk-9
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rstk)
	          (if (and (= (bits (prod0) (+ 51 (rshift)) (rshift)) 0)
		           (= (bits (prod0) (1- (rshift)) 0) 0))
		      0 1)))
  :hints (("Goal" :in-theory (enable bvecp rstk-8)
                  :use (bvecp-prod rshift-bounds
		        (:instance bits-plus-bits (x (prod0)) (n (+ 51 (rshift))) (p (rshift)) (m 0))))))

(local-defthmd rstk-10
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (bits (prod0) (+ 51 (rshift)) (rshift))
	          (bits (frac105) 51 0)))
  :hints (("Goal" :in-theory (enable bvecp-bits-0 bvecp case-1-15 bits-bits)
                  :use (bvecp-prod0 rshift-bounds
		        (:instance bits-plus-bits (x (prod0)) (n (+ 51 (RSHIFT))) (p 107) (m (rshift)))))))

(local-defthmd rstk-11
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (stkshft)
	          (if (= (bits (prod0) (1- (rshift)) 0) 0)
		      0 1))) 
  :hints (("Goal" :in-theory (enable bvecp prod0 cat ash-rewrite)
                  :use (bvecp-prod case-1-11 rshift-bounds		  
		        (:instance bits-shift-up-2 (x (prod)) (k 1) (i (- (rshift) 2)))))))

(local-defthmd rstk-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rstk)
	          (if (and (= (bits (frac105) 51 0) 0)
		           (= (stkshft) 0))
		      0 1)))
  :hints (("Goal" :use (rstk-9 rstk-10 rstk-11))))

(local-defthmd rgrd-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rgrdmask)
	          (logand (lognot (bits (rstkmask) 106 52))
                          (bits (rstkmask) 105 51))))
  :hints (("Goal" :in-theory (enable bvecp rgrdmask))))

(local-defthmd rgrd-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(natp k)
		(<= k 54))
	   (iff (= (bitn (rgrdmask) k) 1)
	         (and (= (bitn (rstkmask) (+ k 52)) 0)
                      (= (bitn (rstkmask) (+ k 51)) 1))))
  :hints (("Goal" :in-theory (enable bitn-bits bitn-logand rgrd-1)  
                  :use ((:instance bitn-lognot (x (bits (rstkmask) 106 52)) (n k))
		        (:instance bitn-0-1 (x (rstkmask)) (n (+ 52 k)))
		        (:instance bitn-0-1 (x (rstkmask)) (n (+ 51 k)))))))

(local-defthmd rgrd-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(natp k)
		(>= k 55))
	   (equal (bitn (rgrdmask) k) 0))
  :hints (("Goal" :in-theory (enable bitn-bits bitn-logand rgrd-1)  
                  :use ((:instance bitn-lognot (x (bits (rstkmask) 106 52)) (n k))
		        (:instance bitn-0-1 (x (rstkmask)) (n (+ 52 k)))
		        (:instance bitn-0-1 (x (rstkmask)) (n (+ 51 k)))))))

(local-defthmd hack-1
  (implies (and (integerp a) (integerp b) (>= a b))
           (>= (expt 2 a) (expt 2 b))))

(local-defthmd rgrd-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 55)
		(natp j))
	   (equal (bitn (rstkmask) j)
	          (if (<= j (+ 51 (rshift)))
		      1 0)))
  :hints (("Goal" :in-theory (enable rstk-1 bvecp)
                  :nonlinearp t
                  :use (rshift-bounds))
          ("Subgoal 2" :in-theory (enable bvecp)
	               :use ((:instance bvecp-monotone (n (+ 52 (rshift))) (m j) (x (1- (EXPT 2 (+ 52 (RSHIFT))))))))
	  ("Subgoal 1" :in-theory (enable bvecp)
	               :use ((:instance bvecp-bitn-2 (x (1- (expt 2 (+ 52 (rshift))))) (n (+ 52 (rshift))) (k j)))
		       :nonlinearp t)))

(local-defthmd rgrd-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 55)
		(natp k))
	   (iff (= (bitn (rgrdmask) k) 1)
	        (and (<= (rshift) 54)
		     (= k (rshift)))))
  :hints (("Goal" :use (rgrd-2 rgrd-3
                        (:instance rgrd-4 (j (+ 51 k)))
                        (:instance rgrd-4 (j (+ 52 k)))))))

(local-defthmd rgrd-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (rshift) 55)
		(natp j))
	   (equal (bitn (rstkmask) j)
	          (if (<= j 106)
		      1 0)))
  :hints (("Goal" :in-theory (enable rstk-4 bvecp)
                  :nonlinearp t
                  :use (rshift-bounds))
          ("Subgoal 1" :use ((:instance bvecp-member (x j) (n 7))))))

(local-defthmd rgrd-7
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (rshift) 55)
		(natp k))
	   (not (= (bitn (rgrdmask) k) 1)))
  :hints (("Goal" :use (rgrd-2 rgrd-3
                        (:instance rgrd-6 (j (+ 51 k)))
                        (:instance rgrd-6 (j (+ 52 k)))))))

(local-defthmd rgrd-8
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(natp k))
	   (iff (= (bitn (rgrdmask) k) 1)
	        (and (<= (rshift) 54)
		     (= k (rshift)))))
  :hints (("Goal" :use (rgrd-5 rgrd-7))))

(local-defthmd bvecp-rgrdmask
  (bvecp (rgrdmask) 55)
  :hints (("Goal" :in-theory (enable rgrdmask))))

(local-defthmd rgrd-9
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (rshift) 54))
	   (equal (rgrdmask) 0))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-rgrdmask
		        (:instance bvecp-bitn-1 (x (rgrdmask)) (n (expo (rgrdmask))))
                        (:instance expo-upper-bound (x (rgrdmask)))
                        (:instance expo-lower-bound (x (rgrdmask)))
			(:instance rgrd-8 (k (expo (rgrdmask))))
			(:instance expo>= (x (rgrdmask)) (n 0))))))

(local-defthmd rgrd-10
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 54)
		(natp k)
		(>= k (rshift)))
	   (equal (bitn (bits (rgrdmask) (1- (rshift)) 0) k)
	          0))
  :hints (("Goal" :in-theory (enable bvecp)
                  :nonlinearp t
                  :use (bvecp-rgrdmask rshift-bounds
			(:instance bits-bounds (x (rgrdmask)) (i (1- (rshift))) (j 0))))))

(local-defthmd rgrd-11
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 54))
	   (equal (bits (rgrdmask) (1- (rshift)) 0)
	          0))
  :hints (("Goal" :in-theory (enable bvecp bitn-bits)
                  :use (bvecp-rgrdmask rshift-bounds
		        (:instance rgrd-10 (k (bit-diff (bits (rgrdmask) (1- (rshift)) 0) 0)))
                        (:instance bit-diff-diff (x (bits (rgrdmask) (1- (rshift)) 0)) (y 0))
                        (:instance rgrd-8 (k (bit-diff (bits (rgrdmask) (1- (rshift)) 0) 0)))
			(:instance bits-bounds (x (rgrdmask)) (i (1- (rshift))) (j 0))))))

(local-defthmd rgrd-12
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 54))
	   (< (rgrdmask) (expt 2 (1+ (rshift)))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-rgrdmask rshift-bounds
		        (:instance expo>= (x (rgrdmask)) (n (1+ (rshift))))
		        (:instance bvecp-bitn-1 (x (rgrdmask)) (n (expo (rgrdmask))))
                        (:instance expo-upper-bound (x (rgrdmask)))
                        (:instance expo-lower-bound (x (rgrdmask)))
                        (:instance rgrd-8 (k (expo (rgrdmask))))))))

(local-defthmd rgrd-13
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
		(<= (rshift) 54))
	   (equal (rgrdmask) (expt 2 (rshift))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-rgrdmask rshift-bounds rgrd-11 rgrd-12
		        (:instance rgrd-8 (k (rshift)))
		        (:instance bitn-plus-bits (x (rgrdmask)) (n (rshift)) (m 0))))))

(local-defthmd rgrd-14
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rgrd)
	          (if (and (<= (rshift) 54)
		           (= (bitn (prod) (+ 51 (rshift))) 1))
		      1 0)))
  :hints (("Goal" :in-theory (enable rgrd rgrd-13 rgrd-9 bitn-bits)
                  :cases ((<= (rshift) 54))
                  :use ((:instance logand-bit (n (rshift)) (x (bits (prod) 105 51)))))))

(local-defthmd rgrd-15
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rgrd)
	          (if (= (bitn (prod) (+ 51 (rshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp rgrd-14)
                  :nonlinearp t
                  :use (bvecp-prod))))

(local-defthmd rgrd-16
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rgrd)
	          (if (= (bitn (prod0) (+ 52 (rshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp rgrd-15 prod0 ash-rewrite cat)
                  :use (bvecp-prod rshift-bounds (:instance bitn-shift-up (x (prod)) (k 1) (n (+ 51 (rshift))))))))

(local-defthmd rgrd-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rgrd)
	          (if (= (bitn (frac105) 52) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp rgrd-16 case-1-15 bitn-bits)
                  :nonlinearp t
                  :cases ((<= (rshift) 54))
                  :use (bvecp-prod0 rshift-bounds))))

(local-defthmd rlsb-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rlsb)
	          (if (and (<= (rshift) 53)
		           (= (bitn (prod) (+ 52 (rshift))) 1))
		      1 0)))
  :hints (("Goal" :in-theory (enable rlsb rgrd-13 rgrd-9 bitn-bits)
                  :cases ((<= (rshift) 53) (= (rshift) 54))
                  :use ((:instance logand-bit (n (rshift)) (x (bits (prod) 105 52)))))))

(local-defthmd rlsb-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rlsb)
	          (if (= (bitn (prod) (+ 52 (rshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp rlsb-1)
                  :nonlinearp t
                  :use (bvecp-prod))))

(local-defthmd rlsb-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rlsb)
	          (if (= (bitn (prod0) (+ 53 (rshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp rlsb-2 prod0 ash-rewrite cat)
                  :use (bvecp-prod rshift-bounds (:instance bitn-shift-up (x (prod)) (k 1) (n (+ 52 (rshift))))))))

(local-defthmd rlsb-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (rlsb)
	          (if (= (bitn (frac105) 53) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp rlsb-3 case-1-15 bitn-bits)
                  :nonlinearp t
                  :cases ((<= (rshift) 53))
                  :use (bvecp-prod0 rshift-bounds))))

(local-defthmd lstk-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (and (natp (lshift))
	        (<= (lshift) 52)))
  :hints (("Goal" :in-theory (enable expdiff-rewrite bvecp lshift)
                  :use (clz-bounds lshift-bound))))

(local-defthmd lstk-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (lstkmask)
	          (1- (expt 2 (- 52 (lshift))))))
  :hints (("Goal" :in-theory (enable bvecp ash-rewrite lstkmask)
                  :use (lstk-1(:instance bvecp-member (x (lshift)) (n 6))))))

(local-defthmd lstk-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (lstk)
	          (if (= (bits (prod) (- 51 (lshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable lstk-2 bvecp lstk)
                  :use (lstk-1
		        (:instance logand-bits (x (prod)) (k 0) (n (- 52 (lshift))))))))

(local-defthmd lstk-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (lstk)
	          (if (= (bits (lprodshft) 51 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable ash-rewrite lstk-3 lprodshft bvecp lstk)
                  :use (lstk-1 (:instance bits-shift-up-2 (x (prod)) (k (lshift)) (i (+ 51 (- (LSHIFT)))))))))

(local-defthmd lstk-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (lstk)
	          (if (= (bits (frac105) 51 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable lstk-4 bvecp lfrac105))))

(local-defthmd lstk-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (lstk)
	          (if (= (bits (prod) (- 50 (lshift)) 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable lstk-2 bvecp ash-rewrite lstk)
                  :cases ((= (lshift) 52))
                  :use (lstk-1
		        (:instance logand-bits (x (prod)) (k 0) (n (- 51 (lshift))))))))

(local-defthmd lstk-7
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (lstk)
	          (if (= (bits (lprodshft) 50 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable ash-rewrite lstk-6 lprodshft bvecp)
                  :use (lstk-1 (:instance bits-shift-up-2 (x (prod)) (k (lshift)) (i (+ 50 (- (LSHIFT)))))))))

(local-defthmd lstk-8
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (lstk)
	          (if (= (bits (frac105) 51 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable lstk-7 ash-rewrite bvecp lfrac105)
                  :use ((:instance bits-shift-up-2 (x (BITS (LPRODSHFT) 104 0)) (k 1) (i 50))))))

(local-defthmd lstk-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (lstk)
	          (if (= (bits (frac105) 51 0) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable mulovf)
                  :use (lstk-8 lstk-5))))

(local-defthmd lgrdmask-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (lgrdmask)
	          (expt 2 (- 52 (lshift)))))
  :hints (("Goal" :in-theory (enable bvecp ash-rewrite lgrdmask ovfmask bits)
                  :nonlinearp t
                  :use (lstk-1))))

(local-defthmd lgrd-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (lgrd)
	          (if (= (bitn (prod) (- 52 (lshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable lgrd lgrdmask-rewrite bitn-bits)  
                  :use ((:instance logand-bit (n (- 52 (lshift))) (x (prod)))))))

(local-defthmd lgrd-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (lgrd)
	          (if (= (bitn (lprodshft) 52) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable lgrd-1 lprodshft bitn-bits ash-rewrite)
                  :use (lstk-1 (:instance bitn-shift-up (x (prod)) (k (lshift)) (n (- 52 (lshift))))))))

(local-defthmd lgrd-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (lgrd)
	          (if (= (bitn (frac105) 52) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable lgrd-2 lfrac105 bitn-bits))))

(local-defthmd lgrd-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (lgrd)
	          (if (= (bitn (prod) (- 51 (lshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable lgrd lgrdmask-rewrite ash-rewrite bitn-bits)
                  :cases ((= (lshift) 52))
                  :use (lstk-1 (:instance logand-bit (n (- 51 (lshift))) (x (prod)))))))

(local-defthmd lgrd-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (lgrd)
	          (if (= (bitn (lprodshft) 51) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable lgrd-4 lprodshft bitn-bits ash-rewrite)
                  :use (lstk-1 (:instance bitn-shift-up (x (prod)) (k (lshift)) (n (- 51 (lshift))))))))

(local-defthmd lgrd-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (lgrd)
	          (if (= (bitn (frac105) 52) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable lgrd-5 ash-rewrite lfrac105 bitn-bits)
                  :use ((:instance bitn-shift-up (x (BITS (LPRODSHFT) 104 0)) (k 1) (n 51))))))

(local-defthmd lgrd-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (lgrd)
	          (if (= (bitn (frac105) 52) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable mulovf)
                  :use (lgrd-3 lgrd-6))))

(local-defthmd lsbmask-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (lsbmask)
	          (expt 2 (- 53 (lshift)))))
  :hints (("Goal" :in-theory (enable bvecp ash-rewrite lsbmask ovfmask bits)
                  :nonlinearp t
                  :use (lstk-1))))

(local-defthmd llsb-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (llsb)
	          (if (= (bitn (prod) (- 53 (lshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable llsb lsbmask-rewrite bitn-bits)  
                  :use ((:instance logand-bit (n (- 53 (lshift))) (x (prod)))))))

(local-defthmd llsb-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (llsb)
	          (if (= (bitn (lprodshft) 53) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable llsb-1 lprodshft bitn-bits ash-rewrite)
                  :use (lstk-1 (:instance bitn-shift-up (x (prod)) (k (lshift)) (n (- 53 (lshift))))))))

(local-defthmd llsb-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 1))
	   (equal (llsb)
	          (if (= (bitn (frac105) 53) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable llsb-2 lfrac105 bitn-bits))))

(local-defthmd llsb-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (llsb)
	          (if (= (bitn (prod) (- 52 (lshift))) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable llsb lsbmask-rewrite ash-rewrite bitn-bits)
                  :use (lstk-1 (:instance logand-bit (n (- 52 (lshift))) (x (prod)))))))

(local-defthmd llsb-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (llsb)
	          (if (= (bitn (lprodshft) 52) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable llsb-4 lprodshft bitn-bits ash-rewrite)
                  :use (lstk-1 (:instance bitn-shift-up (x (prod)) (k (lshift)) (n (- 52 (lshift))))))))

(local-defthmd llsb-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (mulovf) 0))
	   (equal (llsb)
	          (if (= (bitn (frac105) 53) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable llsb-5 ash-rewrite lfrac105 bitn-bits)
                  :use ((:instance bitn-shift-up (x (BITS (LPRODSHFT) 104 0)) (k 1) (n 52))))))

(local-defthmd llsb-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (llsb)
	          (if (= (bitn (frac105) 53) 1)
		      1 0)))
  :hints (("Goal" :in-theory (enable mulovf)
                  :use (llsb-3 llsb-6))))

(defthmd stk-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0))
	   (equal (stk)
	          (if (and (= (bits (frac105) 51 0) 0)
		           (= (stkshft) 0))
		      0 1)))
  :hints (("Goal" :use (rstk-rewrite lstk-rewrite)
                  :cases ((> (+ (ea) (eb) (1- (expt 2 10))) 0)))))

(defthmd grd-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0))
	   (equal (grd)
	          (bitn (frac105) 52)))
  :hints (("Goal" :use (rgrd-rewrite lgrd-rewrite (:instance bitn-0-1 (x (frac105)) (n 52)))
                  :cases ((> (+ (ea) (eb) (1- (expt 2 10))) 0)))))

(defthmd lsb-rewrite
  (implies (and (not (specialp))
                (= (hugeposscale) 0))
	   (equal (lsb)
	          (bitn (frac105) 53)))
  :hints (("Goal" :use (rlsb-rewrite llsb-rewrite (:instance bitn-0-1 (x (frac105)) (n 53)))
                  :cases ((> (+ (ea) (eb) (1- (expt 2 10))) 0)))))

