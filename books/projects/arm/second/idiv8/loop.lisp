(in-package "RTL")

(include-book "early")

;; The number of SRT iterations: 

(defund n () (1+ (cg (/ (del) 3))))
(in-theory (disable (n)))

(defthmd n-bounds
  (implies (not (earlyp))
	   (and (>= (n) 2)
		(<= (n) 22)))
  :hints (("Goal" :in-theory (enable bvecp n)
	   :use (del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(defthmd c-rewrite
  (implies (not (earlyp))
	   (equal (c) (cg (/ (1- (n)) 2))))
  :hints (("Goal" :in-theory (enable bvecp bitsmod6 c n)
	   :use (del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(defthmd c-bounds
  (implies (not (earlyp))
	   (and (>= (c) 1)
		(<= (c) 11)))
  :hints (("Goal" :in-theory (enable bvecp bitsmod6 c n)
	   :use (del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(defthmd only1iter-rewrite
  (implies (not (earlyp))
	   (equal (only1iter)
		  (if (= (n) 2) 1 0)))
  :hints (("Goal" :in-theory (enable bvecp only1iter bitsmod6 c n)
	   :use (del-bounds (:instance bvecp-member (x (del)) (n 6))))))

(defthmd skipiter-rewrite
  (implies (not (earlyp))
	   (equal (skipiter)
		  (if (and (> (n) 2) (= (mod (n) 2) 0))
		      1 0)))
  :hints (("Goal" :in-theory (enable bvecp skipiter only1iter bitsmod6 c n)
	   :use (del-bounds (:instance bvecp-member (x (del)) (n 6))))))

;; Iteration j occurs as the first iteration of a cycle:

(defund it1 (j)
  (and (> j 1)
       (or (= j (1- (n)))
	   (= (n) 2)
	   (and (< j (1- (n)))
		(= (mod j 2) 0)))))

;; We define the sequences of values (q j), (rp j), (rn j), (quot j), etc., as a
;; set of mutually recursive functions, as they are computed by idiv8-loop-1, and
;; prove that the constants (rpf), etc., are related to these functions as follows:
;;   (equal (rpf) (rp (n)))
;;   (equal (rnf) (rn (n)))
;;   (equal (quotf) (quot (n)))
;;   (equal (quotmf) (quotm (n)))
;;   (equal (quotpf) (quotp (n)))
;; 

(mutual-recursion

(defund q (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      (q-1)
    (nextdigit (rs10 (1- j)) (cmpconst))))

(defund divsigned (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if1 (bitn (rs10 (1- j)) 9)
         (div)
       (bits (lognot (div)) 70 0))))

(defund div3signed (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if1 (bitn (rs10 (1- j)) 9)
         (div3)
       (bits (lognot (div3)) 70 0))))

(defund rs11 (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (computers11 (rp (1- j)) (rn (1- j)) (q j) (divsigned j) (div3signed j))
      (rs11 (1- j)))))

(Defund rp (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rp-1)
    (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (bitn (rs10 (1- j)) 9) (q j) (divsigned j) (div3signed j) (int32))))))

(defund rn (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rn-1)
    (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (bitn (rs10 (1- j)) 9) (q j) (divsigned j) (div3signed j) (int32))))))

(defund rs10 (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (zp j)
      (rs10-0)
    (if (= j 1)
        (rs10-1)
      (if (it1 j)
          (bits (+ (+ (bits (rp j) 67 58) (lognot (bits (rn j) 67 58))) 1) 9 0)
        (computers10 (divsigned j) (div3signed j) (q j) (rs11 (1- j)))))))

(defund quot (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (quot-1)
    (mv-nth 0 (mv-list 2 (nextquot (sgnq) (q j) (quot (1- j)) (quotm (1- j)))))))

(defund quotm (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (quotm-1)
    (mv-nth 1 (mv-list 2 (nextquot (sgnq) (q j) (quot (1- j)) (quotm (1- j)))))))

(defund qlast (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (q j)
      (qlast (1- j)))))

(defund quotlast (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
	(quot (1- j))
      (quotlast (1- j)))))

(defund quotmlast (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (quotm (1- j))
      (quotmlast (1- j)))))

(defund quotp (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (bits (+ (quot j) (ash 1 (k))) 64 0)
      (incquot (sgnq) (q j) (quot (1- j)) (quotm (1- j)) (qlast j) (quotlast j) (quotmlast j) (k)))))

)
      
(in-theory (disable (q) (divsigned) (div3signed) (rs11) (rp) (rn) (rs10) (quot) (quotm) (qlast) (quotlast) (quotmlast) (quotp)))

;;******************************************************************************************************************************

(local-defthmd idiv8-loop-1-1
  (implies (and (not (earlyp))
		(= (n) 2))
           (equal (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                                 (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1))
                  (list (q 2) (qlast 2) (quotlast 2) (quotmlast 2) (rs11 2) (rp 2) (rn 2) (rs10 2) (quot 2) (quotm 2) (quotp 2))))
  :hints (("goal" :in-theory (enable it1 c-rewrite only1iter-rewrite skipiter-rewrite divsigned div3signed q qlast quotlast
				     quotmlast rs11 rp rn rs10 quot quotm quotp quotp-1)
                  :expand ((:free (i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
				  (idiv8-loop-1 i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                                 rs11 rp rn rs10 quot quotm quotp))
			   (:free (j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
			          (idiv8-loop-0 j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast
				                 quotmlast rs11 rp rn rs10 quot quotm quotp))))))

(local-defthmd idiv8-loop-1-2
  (implies (and (not (earlyp))
		(> (n) 2)
                (= (mod (n) 2) 1))
           (equal (idiv8-loop-1 (c) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 2))
				 (qlast (- (n) 2)) (quotlast (- (n) 2)) (quotmlast (- (n) 2)) (rs11 (- (n) 2)) 
                                 (rp (- (n) 2)) (rn (- (n) 2)) (rs10 (- (n) 2)) (quot (- (n) 2)) (quotm (- (n) 2)) (quotp (- (n) 2)))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :in-theory (enable it1 only1iter-rewrite skipiter-rewrite divsigned div3signed q qlast quotlast quotmlast rs11
				     rp rn rs10 quot quotm quotp)
                  :use (c-bounds)
	          :expand ((q (n))
                           (qlast (n))
                           (quotlast (n))
                           (quotmlast (n))
                           (rs11 (n))
                           (rp (n))
                           (rn (n))
                           (rs10 (n))
                           (quot (n))
                           (quotm (n))
                           (quotp (n))
			   (:free (i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
				  (idiv8-loop-1 i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                                 rs11 rp rn rs10 quot quotm quotp))
			   (:free (j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
			          (idiv8-loop-0 j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast
				                 quotmlast rs11 rp rn rs10 quot quotm quotp))))))

(local-defthmd idiv8-loop-1-3
  (implies (and (not (earlyp))
		(> (n) 2)
                (= (mod (n) 2) 0))
           (equal (idiv8-loop-1 (c) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 2))
				 (qlast (- (n) 2)) (quotlast (- (n) 2)) (quotmlast (- (n) 2)) (rs11 (- (n) 2)) 
                                 (rp (- (n) 2)) (rn (- (n) 2)) (rs10 (- (n) 2)) (quot (- (n) 2)) (quotm (- (n) 2)) (quotp (- (n) 2)))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :in-theory (enable it1 only1iter-rewrite skipiter-rewrite divsigned div3signed q qlast quotlast quotmlast rs11
				     rp rn rs10 quot quotm quotp)
                  :use (c-bounds)
                  :expand ((q (n))
                           (qlast (n))
                           (quotlast (n))
                           (quotmlast (n))
                           (rs11 (n))
                           (rp (n))
                           (rn (n))
                           (rs10 (n))
                           (quot (n))
                           (quotm (n))
                           (quotp (n))
			   (:free (i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
				  (idiv8-loop-1 i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                                 rs11 rp rn rs10 quot quotm quotp))
			   (:free (j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
			          (idiv8-loop-0 j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast
				                 quotmlast rs11 rp rn rs10 quot quotm quotp))))))

(local-defthmd idiv8-loop-1-4
  (implies (and (not (earlyp))
		(> (n) 2))
           (equal (idiv8-loop-1 (c) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 2))
				 (qlast (- (n) 2)) (quotlast (- (n) 2)) (quotmlast (- (n) 2)) (rs11 (- (n) 2)) 
                                 (rp (- (n) 2)) (rn (- (n) 2)) (rs10 (- (n) 2)) (quot (- (n) 2)) (quotm (- (n) 2)) (quotp (- (n) 2)))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :use (idiv8-loop-1-2 idiv8-loop-1-3))))

(local-defthmd idiv8-loop-1-5
  (implies (and (not (earlyp))
		(= (n) 3))
           (equal (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                                 (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1))
                  (list (q 3) (qlast 3) (quotlast 3) (quotmlast 3) (rs11 3) (rp 3) (rn 3) (rs10 3) (quot 3) (quotm 3) (quotp 3))))
  :hints (("goal" :in-theory (enable c-rewrite q qlast quotlast quotmlast rs11 rp rn rs10 quot quotm quotp)
	          :use (idiv8-loop-1-4))))

(local-defthmd idiv8-loop-1-6
  (implies (and (not (earlyp))
		(> (n) 3)
                (= (mod (n) 2) 0))
           (equal (idiv8-loop-1 (1- (c)) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k)
		  	         (q (- (n) 3)) (qlast (- (n) 3)) (quotlast (- (n) 3)) (quotmlast (- (n) 3)) (rs11 (- (n) 3)) 
                                 (rp (- (n) 3)) (rn (- (n) 3)) (rs10 (- (n) 3)) (quot (- (n) 3)) (quotm (- (n) 3)) (quotp (- (n) 3)))
                  (idiv8-loop-1 (c) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 2))
				 (qlast (- (n) 2)) (quotlast (- (n) 2)) (quotmlast (- (n) 2)) (rs11 (- (n) 2))
                                 (rp (- (n) 2)) (rn (- (n) 2)) (rs10 (- (n) 2)) (quot (- (n) 2)) (quotm (- (n) 2)) (quotp (- (n) 2)))))
  :hints (("goal" :in-theory (enable it1 only1iter-rewrite skipiter-rewrite divsigned div3signed q qlast quotlast quotmlast
				     rs11 rp rn rs10 quot quotm quotp)
                  :expand ((:free (i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
				  (idiv8-loop-1 i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                                 rs11 rp rn rs10 quot quotm quotp))
			   (:free (j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
			          (idiv8-loop-0 j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast
				                 quotmlast rs11 rp rn rs10 quot quotm quotp))))))

(local-defthmd idiv8-loop-1-7
  (implies (and (not (earlyp))
		(> (n) 3)
                (= (mod (n) 2) 1))
           (equal (idiv8-loop-1 (1- (c)) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 4))
				 (qlast (- (n) 4)) (quotlast (- (n) 4)) (quotmlast (- (n) 4)) (rs11 (- (n) 4)) 
                                 (rp (- (n) 4)) (rn (- (n) 4)) (rs10 (- (n) 4)) (quot (- (n) 4)) (quotm (- (n) 4)) (quotp (- (n) 4)))
                  (idiv8-loop-1 (c) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 2))
				 (qlast (- (n) 2)) (quotlast (- (n) 2)) (quotmlast (- (n) 2)) (rs11 (- (n) 2))
                                 (rp (- (n) 2)) (rn (- (n) 2)) (rs10 (- (n) 2)) (quot (- (n) 2)) (quotm (- (n) 2)) (quotp (- (n) 2)))))
  :hints (("goal" :in-theory (enable it1 only1iter-rewrite skipiter-rewrite divsigned div3signed q qlast quotlast quotmlast rs11
				     rp rn rs10 quot quotm quotp)
                  :expand ((q (+ -2 (n)))
                           (qlast (+ -2 (n)))
                           (quotlast (+ -2 (n)))
                           (quotmlast (+ -2 (n)))
                           (rs11 (+ -2 (n)))
                           (rp (+ -2 (n)))
                           (rn (+ -2 (n)))
                           (rs10 (+ -2 (n)))
                           (quot (+ -2 (n)))
                           (quotm (+ -2 (n)))
                           (quotp (+ -2 (n)))
		           (:free (only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
				  (idiv8-loop-1 (+ -1 (c)) only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                                 rs11 rp rn rs10 quot quotm quotp))
			   (:free (j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
			          (idiv8-loop-0 j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast
				                 quotmlast rs11 rp rn rs10 quot quotm quotp))))))

(local-defthmd idiv8-loop-1-8
  (implies (and (not (earlyp))
		(> (n) 3)
                (= (mod (n) 2) 0))
           (equal (idiv8-loop-1 (1- (c)) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k)
		  	         (q (- (n) 3)) (qlast (- (n) 3)) (quotlast (- (n) 3)) (quotmlast (- (n) 3)) (rs11 (- (n) 3)) 
                                 (rp (- (n) 3)) (rn (- (n) 3)) (rs10 (- (n) 3)) (quot (- (n) 3)) (quotm (- (n) 3)) (quotp (- (n) 3)))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :use (idiv8-loop-1-4 idiv8-loop-1-6))))

(local-defthmd idiv8-loop-1-9
  (implies (and (not (earlyp))
		(> (n) 3)
                (= (mod (n) 2) 1))
           (equal (idiv8-loop-1 (1- (c)) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (- (n) 4))
				 (qlast (- (n) 4)) (quotlast (- (n) 4)) (quotmlast (- (n) 4)) (rs11 (- (n) 4)) 
                                 (rp (- (n) 4)) (rn (- (n) 4)) (rs10 (- (n) 4)) (quot (- (n) 4)) (quotm (- (n) 4)) (quotp (- (n) 4)))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :use (idiv8-loop-1-4 idiv8-loop-1-7))))

(local-defthmd idiv8-loop-1-10
  (implies (and (not (earlyp))
		(> (n) 3)
		(natp i)
		(natp j)
		(> i 0)
		(< i (1- (c)))
		(= (mod j 2) 1)
		(<= j (- (n) 4)))
           (equal (idiv8-loop-1 i (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q j) (qlast j)
	                         (quotlast j) (quotmlast j) (rs11 j) 
                                 (rp j) (rn j) (rs10 j) (quot j) (quotm j) (quotp j))
                  (idiv8-loop-1 (1+ i) (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (+ j 2))
				 (qlast (+ j 2)) (quotlast (+ j 2)) (quotmlast (+ j 2)) (rs11 (+ j 2))
                                 (rp (+ j 2)) (rn (+ j 2)) (rs10 (+ j 2)) (quot (+ j 2)) (quotm (+ j 2)) (quotp (+ j 2)))))
  :hints (("goal" :in-theory (enable it1 only1iter-rewrite divsigned div3signed q qlast quotlast quotmlast rs11 rp rn rs10 quot
				     quotm quotp)
	          :use (c-bounds)
                  :expand ((q (+ 2 j))
                           (qlast (+ 2 j))
                           (quotlast (+ 2 j))
                           (quotmlast (+ 2 j))
                           (rs11 (+ 2 j))
                           (rp (+ 2 j))
                           (rn (+ 2 j))
                           (rs10 (+ 2 j))
                           (quot (+ 2 j))
                           (quotm (+ 2 j))
                           (quotp (+ 2 j))
			   (:free (only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
				  (idiv8-loop-1 i only1iter skipiter c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                                 rs11 rp rn rs10 quot quotm quotp))
			   (:free (j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast quotmlast
                                   rs11 rp rn rs10 quot quotm quotp)
			          (idiv8-loop-0 j only1iter skipiter i c cmpconst div div3 int32 sgnq k q qlast quotlast
				                 quotmlast rs11 rp rn rs10 quot quotm quotp))))))

(local-defthmd idiv8-loop-1-11
  (implies (and (not (earlyp))
		(> (n) 3)
		(natp i)
		(> i 0)
		(<= i (1- (c))))
           (equal (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q 1) (qlast 1)
	                         (quotlast 1) (quotmlast 1) (rs11 1) 
                                 (rp 1) (rn 1) (rs10 1) (quot 1) (quotm 1) (quotp 1))
                  (idiv8-loop-1 i (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q (1- (* 2 i)))
				 (qlast (1- (* 2 i))) (quotlast (1- (* 2 i))) (quotmlast (1- (* 2 i))) (rs11 (1- (* 2 i)))
                                 (rp (1- (* 2 i))) (rn (1- (* 2 i))) (rs10 (1- (* 2 i))) (quot (1- (* 2 i))) (quotm (1- (* 2 i)))
				 (quotp (1- (* 2 i))))))
  :hints (("goal" :induct (nats i))
	  ("subgoal *1/2" :in-theory (enable c-rewrite)
	   :use ((:instance idiv8-loop-1-10 (i (1- i)) (j (- (* 2 i) 3)))))))

(local-defthmd idiv8-loop-1-12
  (implies (and (not (earlyp))
		(> (n) 3))
           (equal (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q 1) (qlast 1)
	                         (quotlast 1) (quotmlast 1) (rs11 1) 
                                 (rp 1) (rn 1) (rs10 1) (quot 1) (quotm 1) (quotp 1))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :in-theory (enable bvecp c-rewrite)
	          :use (n-bounds idiv8-loop-1-8 idiv8-loop-1-9
		        (:instance bvecp-member (x (n)) (n 5))
			(:instance idiv8-loop-1-11 (i (1- (c))))))))

(local-defthmd idiv8-loop-1-lemma
  (implies (not (earlyp))
           (equal (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                                 (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1))
                  (list (q (n)) (qlast (n)) (quotlast (n)) (quotmlast (n)) (rs11 (n)) (rp (n)) (rn (n)) (rs10 (n))
		        (quot (n)) (quotm (n)) (quotp (n)))))
  :hints (("goal" :expand ((q 1) (qlast 1) (quotlast 1) (quotmlast 1) (rs11 1) (rp 1) (rn 1) (rs10 1) (quot 1) (quotm 1) (quotp 1))
                  :in-theory (enable bvecp)
	          :use (n-bounds idiv8-loop-1-1 idiv8-loop-1-5 idiv8-loop-1-12 (:instance bvecp-member (x (n)) (n 2))))))

(defthmd rpf-rewrite
  (implies (not (earlyp))
           (equal (rpf) (rp (n))))
  :hints (("goal" :use (idiv8-loop-1-lemma)  
                  :in-theory (enable rpf))))

(defthmd rnf-rewrite
  (implies (not (earlyp))
           (equal (rnf) (rn (n))))
  :hints (("goal" :use (idiv8-loop-1-lemma)  
                  :in-theory (enable rnf))))

(defthmd quotf-rewrite
  (implies (not (earlyp))
           (equal (quotf) (quot (n))))
  :hints (("goal" :use (idiv8-loop-1-lemma)  
                  :in-theory (enable quotf))))

(defthmd quotmf-rewrite
  (implies (not (earlyp))
           (equal (quotmf) (quotm (n))))
  :hints (("goal" :use (idiv8-loop-1-lemma)  
                  :in-theory (enable quotmf))))

(defthmd quotpf-rewrite
  (implies (not (earlyp))
           (equal (quotpf) (quotp (n))))
  :hints (("goal" :use (idiv8-loop-1-lemma)  
                  :in-theory (enable quotpf))))

