(in-package "RTL")

(include-book "first")

(defund approx (j)
  (/ (si (rs10 j) 10) 64))

(defund hyp (j)
  (and (= (q j) (maxk (approx (1- j))))
       (< (abs (- (approx (1- j)) (* 8 (r (1- j))))) 1/64)
       (<= (abs (r j)) (* 4/7 (d)))
       (bvecp (rp j) 71)
       (bvecp (rn j) 71)
       (= (mod (* (expt 2 67) (r j)) (expt 2 71)) (mod (- (rp j) (rn j)) (expt 2 71)))
       (= (bits (rp j) (- 63 (p)) 0) 0)
       (= (bits (rn j) (- 63 (p)) 0) 0)))

(in-theory (disable (approx) (hyp)))

;; Objective:

;; (local-defthmd main-induction
;;   (implies (and (not (zp j)) (<= j (n)))
;;            (hyp j)))

(defthmd bvecp-div
  (bvecp (div) 71)
  :hints (("Goal" :in-theory (enable div))))

(local-defthmd bvecp-rp-1
  (bvecp (rp-1) 71)
  :hints (("Goal" :in-theory (enable rp-1))))

(local-defthmd bvecp-rn-1
  (bvecp (rn-1) 71)
  :hints (("Goal" :in-theory (enable rn-1 div div2))))

(local-defthmd hyp-1
  (implies (not (earlyp))
           (hyp 1))
  :hints (("Goal" :in-theory (enable si rs10 rp rn hyp approx bvecp-div bvecp-rp-1 bvecp-rn-1 q q-1)
                  :use (p-vals rs10-0-9 a0-error q1-max r1-bound r1-rp1-rn1 bits-rp1-0 bits-rn1-0
		        (:instance bits-plus-bits (x (rp 1)) (n (- 66 (p))) (p (- 64 (p))) (m 0))
		        (:instance bits-plus-bits (x (rn 1)) (n (- 66 (p))) (p (- 64 (p))) (m 0))))))

(in-theory (disable (maxk)))

(set-rewrite-stack-limit 10000)

(local-defthmd nextdigit-maxk
  (implies (bvecp rs10 10)
           (equal (nextdigit rs10 (computecmpconst (bits (div) 65 60)))
	          (maxk (/ (si rs10 10) 64))))
  :hints (("Goal" :in-theory (enable m maxk computecmpconst nextdigit)
                  :use ((:instance bvecp-member (x rs10) (n 10))
		        (:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(set-rewrite-stack-limit acl2::*default-rewrite-stack-limit*)

(local-defthmd q-nextdigit
  (implies (and (not (earlyp))
                (integerp j)
		(> j 1))
	   (equal (q j) (nextdigit (rs10 (1- j)) (computecmpconst (bits (div) 65 60)))))
  :hints (("Goal" :in-theory (enable q cmpconst))))

(local-defthm bvecp-rems6
  (implies (and (not (earlyp))
                (integerp j)
		(>= j 1))
           (bvecp (rs10 j) 10))
  :hints (("Goal" :in-theory (enable rs10 computers10 rs10-1)
                  :expand ((:free (j) (rs10 j))))))

(local-defthmd q-maxk
  (implies (and (not (earlyp))
                (integerp j)
		(> j 1))
           (equal (q j) (maxk (approx (1- j)))))
  :hints (("Goal" :in-theory (enable approx nextdigit-maxk q-nextdigit))))

(local-defthmd approx-error-1
  (implies (and (not (earlyp))
                (not (zp j))
		(or (= j 1) (it1 j)))
	   (equal (rs10 j)
	          (mod (- (bits (rp j) 67 58) (bits (rn j) 67 58)) 1024)))
  :hints (("Goal" :in-theory (enable rs10 rs10-1 bits-mod rp rn lognot))))

(local-defthmd approx-error-2
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (equal (mod (* (expt 2 67) (r j)) (expt 2 71))
	          (mod (- (rp j) (rn j)) (expt 2 71))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd approx-error-3
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (equal (mod (* (expt 2 67) (r j)) (expt 2 68))
	          (mod (- (rp j) (rn j)) (expt 2 68))))
  :hints (("Goal" :use (approx-error-2
                        (:instance mod-of-mod-cor (x (* (expt 2 67) (r j))) (a 71) (b 68))
                        (:instance mod-of-mod-cor (x (- (rp j) (rn j))) (a 71) (b 68))))))

(local-defthmd approx-error-4
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (and (bvecp (rp j) 71)
	        (bvecp (rn j) 71)))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd approx-error-5
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (equal (mod (- (rp j) (rn j)) (expt 2 68))
	          (mod (- (mod (rp j) (expt 2 68)) (mod (rn j) (expt 2 68))) (expt 2 68))))
  :hints (("Goal" :use (approx-error-4
                        (:instance mod-sum (a (- (rn j))) (b (rp j)) (n (expt 2 68)))
                        (:instance mod-diff (a (mod (rp j) (expt 2 68))) (b (rn j)) (n (expt 2 68)))))))

(defund x* (j)
  (- (bits (rp j) 67 0)
     (bits (rn j) 67 0)))

(in-theory (disable (x*)))

(local-defthmd approx-error-6
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (equal (mod (x* j) (expt 2 68))
	          (mod (- (mod (rp j) (expt 2 68)) (mod (rn j) (expt 2 68))) (expt 2 68))))
  :hints (("Goal" :use (approx-error-4) :in-theory (enable x* bits-mod))))

(local-defthmd approx-error-7
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (equal (mod (x* j) (expt 2 68))
	          (mod (* (expt 2 67) (r j)) (expt 2 68))))
  :hints (("Goal" :use (approx-error-3 approx-error-5  approx-error-6))))

(defund y* (j)
  (* (expt 2 58) (- (bits (rp j) 67 58) (bits (rn j) 67 58))))

(in-theory (disable (y*)))

(local-defthmd approx-error-8
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (equal (mod (y* j) (expt 2 68))
	          (mod (* (expt 2 58) (rs10 j)) (expt 2 68))))
  :hints (("Goal" :in-theory (enable y* approx-error-1)
                  :use ((:instance mod-prod (k (expt 2 58)) (n (expt 2 10)) (m (- (bits (rp j) 67 58) (bits (rn j) 67 58))))
		        (:instance mod-prod (k (expt 2 58)) (n (expt 2 10)) (m (mod (- (bits (rp j) 67 58) (bits (rn j) 67 58)) (expt 2 10))))
		        (:instance mod-of-mod-cor (x (- (bits (rp j) 67 58) (bits (rn j) 67 58))) (a 10) (b 10))))))

(local-defthmd approx-error-8-a
  (implies (and (not (earlyp))
                (not (zp j)))
	   (equal (mod (* (expt 2 58) (rs10 j)) (expt 2 68))
	          (* (expt 2 58) (rs10 j))))
  :hints (("Goal" :use (bvecp-rems6) :in-theory (e/d (bvecp) (bvecp-rems6)))))



(local-defthmd approx-error-9
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (< (abs (- (x* j) (y* j)))
	      (expt 2 58)))
  :hints (("Goal" :in-theory (enable x* y*)
                  :use (approx-error-4
		        (:instance bits-plus-bits (x (rp j)) (n 67) (p 58) (m 0)) 
		        (:instance bits-plus-bits (x (rn j)) (n 67) (p 58) (m 0)) 
		        (:instance bits-bounds (x (rp j)) (i 57) (j 0))
		        (:instance bits-bounds (x (rn j)) (i 57) (j 0))))))

(local-defthmd approx-error-10
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (< (abs (r j)) 4/7))
  :hints (("Goal" :in-theory (enable hyp)
                  :use (d-bounds))))

(local-defthmd approx-error-11
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (equal (si (mod (x* j) (expt 2 68)) 68)
	          (* (expt 2 67) (r j))))
  :hints (("Goal" :use (approx-error-7 approx-error-10 int-r p-vals
                        (:instance si-bits (x (* (expt 2 67) (r j))) (n 68)))
		  :in-theory (enable bits-mod))))

(local-defthmd approx-error-12
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (<= (abs (si (mod (x* j) (expt 2 68)) 68))
	       (* (expt 2 67) 4/7)))
  :hints (("Goal" :use (approx-error-11 approx-error-10 int-r))))

(local-defthmd approx-error-13
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (equal (abs (- (si (mod (x* j) (expt 2 68)) 68)
	                  (si (mod (y* j) (expt 2 68)) 68)))
		  (abs (- (x* j) (y* j)))))
  :hints (("Goal" :use (approx-error-9 approx-error-12
                        (:instance si-approx (x (x* j)) (y (y* j)) (n 68))))))

(local-defthmd approx-error-14
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (< (abs (- (* (expt 2 67) (r j))
	              (si (mod (y* j) (expt 2 68)) 68)))
	      (expt 2 58)))
  :hints (("Goal" :use (approx-error-9 approx-error-11 approx-error-13)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd approx-error-15
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (equal (si (mod (y* j) (expt 2 68)) 68)
	          (* (expt 2 58) (si (rs10 j) 10))))  
  :hints (("Goal" :use (approx-error-8 approx-error-8-a
                        (:instance si-shift (n 10) (k 58) (r (rs10 j)))))))

(local-defthmd approx-error-16
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (< (abs (- (* (expt 2 67) (r j))
	              (* (expt 2 58) (si (rs10 j) 10))))
	      (expt 2 58)))
  :hints (("Goal" :use (approx-error-14 approx-error-15))))

(local-defthmd approx-error-even
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (= j 1) (it1 j)))
	   (< (abs (- (* 8 (r j)) (approx j)))
	      1/64))
  :hints (("Goal" :use (approx-error-16) :in-theory (enable approx))))

;;---------------------------------------------------------------------------------------

(defund alpha* (j)
  (if (<= (q (1- j)) 0)
      0 1))

(defund delta* (j)
  (- (+ (* (q (1- j)) (div)) (alpha* j))))

(defund pi* (j)
  (+ (mod (* 8 (rp (- j 2))) (expt 2 65))
     4
     (alpha* j)))

(defund nu* (j)
  (+ (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
     4))

(defund del* (j)
  (mod (delta* j) (expt 2 65)))

(in-theory (disable (alpha*) (delta*) (pi*) (nu*) (del*)))

(local-defthmd approx-error-17
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (equal (mod (+ (pi* j) (nu* j) (del* j)) (expt 2 65))
	          (mod (+ (mod (* 8 (rp (- j 2))) (expt 2 65)) 
		          (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
			  (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			  8
			  (alpha* j))
		       (expt 2 65))))
  :hints (("Goal" :in-theory (enable pi* nu* del* delta*))))

(defthmd bvecp-rp-rn
  (implies (hyp j)
           (and (bvecp (rp j) 71)
	        (bvecp (rn j) 71)))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd approx-error-18
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (+ (mod (* 8 (rp (- j 2))) (expt 2 65)) 
		          (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
			  (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			  8
			  (alpha* j))
		       (expt 2 65))
		  (mod (+ (* 8 (rp (- j 2)))
		          (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
			  (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			  8
			  (alpha* j))
		       (expt 2 65))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-sum (a (+ (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
			                      (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
		                              8
			                      (alpha* j)))
					   (b (* 8 (rp (- j 2))))
					   (n (expt 2 65)))))))

(local-defthmd approx-error-19
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (+ (* 8 (rp (- j 2)))
		          (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
			  (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			  8
			  (alpha* j))
		       (expt 2 65))
		  (mod (+ (* 8 (rp (- j 2)))
		          (* -8 (rn (- j 2)))
			  (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			  (alpha* j))
		       (expt 2 65))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-sum (a (+ (* 8 (rp (- j 2)))
		 	                         (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			                         8
			                         (alpha* j)))
					   (b (* -8 (1+ (rn (- j 2)))))
					   (n (expt 2 65)))))))

(local-defthmd approx-error-20
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (+ (* 8 (rp (- j 2)))
		          (* -8 (rn (- j 2)))
			  (mod (- (+ (* (q (1- j)) (div)) (alpha* j))) (expt 2 65))
			  (alpha* j))
		       (expt 2 65))
		  (mod (+ (* 8 (rp (- j 2)))
		          (* -8 (rn (- j 2)))
			  (- (* (q (1- j)) (div))))
		       (expt 2 65))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-sum (a (+ (* 8 (rp (- j 2)))
		 	                         (* -8 (rn (- j 2)))
			                         (alpha* j)))
					   (b (- (+ (* (q (1- j)) (div)) (alpha* j))))
					   (n (expt 2 65)))))))

(local-defthmd approx-error-21
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (+ (* 8 (rp (- j 2)))
		          (* -8 (rn (- j 2)))
			  (- (* (q (1- j)) (div))))
		       (expt 2 65))
		  (mod (+ (mod (* 8 (- (rp (- j 2)) (rn (- j 2)))) (expt 2 65))
			  (- (* (q (1- j)) (div))))
		       (expt 2 65))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-sum (b (* 8 (- (rp (- j 2)) (rn (- j 2)))))
					   (a (- (* (q (1- j)) (div))))
					   (n (expt 2 65)))))))

(local-defthmd approx-error-22
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (* 8 (- (rp (- j 2)) (rn (- j 2)))) (expt 2 65))
	          (* 8 (mod (- (rp (- j 2)) (rn (- j 2))) (expt 2 62)))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-prod (k 8) (m (- (rp (- j 2)) (rn (- j 2)))) (n (expt 2 62)))))))

(local-defthmd approx-error-23
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (- (rp (- j 2)) (rn (- j 2))) (expt 2 62))
	          (mod (* (expt 2 67) (r (- j 2))) (expt 2 62))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-of-mod-cor (x (- (rp (- j 2)) (rn (- j 2)))) (a 71) (b 62))
                        (:instance mod-of-mod-cor (x (* (expt 2 67) (r (- j 2)))) (a 71) (b 62)))
	          :in-theory (enable hyp))))

(local-defthmd approx-error-24
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (* 8 (mod (* (expt 2 67) (r (- j 2))) (expt 2 62)))
	          (mod (* (expt 2 70) (r (- j 2))) (expt 2 65))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-prod (k 8) (m (* (expt 2 67) (r (- j 2)))) (n (expt 2 62)))))))

(local-defthmd approx-error-25
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (+ (mod (* (expt 2 70) (r (- j 2))) (expt 2 65))
	                  (- (* (q (1- j)) (div))))
		       (expt 2 65))
		  (mod (+ (* (expt 2 70) (r (- j 2)))
	                  (- (* (q (1- j)) (div))))
		       (expt 2 65))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-sum (b (* (expt 2 70) (r (- j 2))))
					   (a (- (* (q (1- j)) (div))))
					   (n (expt 2 65)))))))

(local-defthmd approx-error-26
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (+ (* (expt 2 70) (r (- j 2)))
	             (- (* (q (1- j)) (div))))
		  (* (expt 2 67) (r (1- j)))))
  :hints (("Goal" :use (div-rewrite (:instance r-recurrence (j (- j 2)))))))

(local-defthmd approx-error-27
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
	   (equal (mod (+ (pi* j) (nu* j) (del* j)) (expt 2 65))
	          (mod (* (expt 2 67) (r (1- j)))
		       (expt 2 65))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (approx-error-17 approx-error-18 approx-error-19 approx-error-20 approx-error-21 approx-error-22
		        approx-error-23 approx-error-24 approx-error-25 approx-error-26))))

(defund sig* (j)
  (if (= (q (1- j)) 0)
      (pi* j)
    (logxor (logxor (pi* j) (nu* j))
            (del* j))))

(defund chi* (j)
  (if (= (q (1- j)) 0)
      (nu* j)
    (* 2 (logior (logand (pi* j) (nu* j))
                 (logand (logior (pi* j) (nu* j))
  	                 (del* j))))))

(defund r* (j) (+ (sig* j) (bits (chi* j) 64 0)))

(in-theory (disable (sig*) (del*) (r*)))

(defthm natp-pi*
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (natp (pi* j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable pi* nu* del*))))

(defthm natp-nu*
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (natp (nu* j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable pi* nu* del*))))

(defthm natp-del*
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (natp (del* j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable pi* nu* del*))))

(local-defthm approx-error-28-a
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j)
		(= (q (1- j)) 0))
	   (equal (del* j) 0))
  :hints (("Goal" :in-theory (enable alpha* del* delta*))))

(local-defthmd approx-error-28
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (equal (+ (sig* j) (chi* j))
	          (+ (pi* j) (nu* j) (del* j))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance logior-logand-2 (y (pi* j)) (z (nu* j)) (x (del* j)))
                        (:instance add-3 (x (pi* j)) (y (nu* j)) (z (del* j))))
		  :in-theory (enable sig* chi* bvecp))))

(local-defthmd approx-error-32
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (<= (mod (* 8 (rp (- j 2))) (expt 2 65))
	       (* 8 (1- (expt 2 62)))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-prod (k 8) (m (rp (- j 2))) (n (expt 2 62)))))))

(local-defthmd approx-error-33
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (bvecp (pi* j) 65))
  :hints (("Goal" :use (approx-error-32 (:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable bvecp alpha* pi*))))

(local-defthmd approx-error-34
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (<= (mod (* -8 (1+ (rn (- j 2)))) (expt 2 65))
	       (* 8 (1- (expt 2 62)))))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-prod (k 8) (m (- (1+ (rn (- j 2))))) (n (expt 2 62)))))))

(local-defthmd approx-error-35
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (bvecp (nu* j) 65))
  :hints (("Goal" :use (approx-error-34 (:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable bvecp nu*))))

(local-defthmd approx-error-36
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (bvecp (del* j) 65))
  :hints (("Goal" :use ((:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable bvecp del*))))

(local-defthmd approx-error-37
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (bvecp (sig* j) 65))
  :hints (("Goal" :use (approx-error-33 approx-error-35 approx-error-36 (:instance bvecp-rp-rn (j (- j 2))))
                  :in-theory (enable sig*))))

(local-defthmd approx-error-29
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (equal (mod (r* j) (expt 2 65))
	          (mod (+ (sig* j) (chi* j)) (expt 2 65))))
  :hints (("Goal" :use ((:instance mod-sum (a (sig* j)) (b (chi* j)) (n (expt 2 65))))
		  :in-theory (enable bits-mod sig* chi* r*))))

(local-defthmd approx-error-30
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (equal (mod (r* j) (expt 2 65))
	          (mod (* (expt 2 67) (r (1- j))) (expt 2 65))))
  :hints (("Goal" :use (approx-error-27 approx-error-28 approx-error-29))))

(defund eps* (j)
  (if (and (= (bitn (sig* j) 53) 0)
           (= (bitn (chi* j) 53) 0))
      0 1))

(defund rt* (j)
  (* (expt 2 54)
     (+ (bits (sig* j) 64 54)
        (bits (chi* j) 64 54)
	(eps* j))))

(in-theory (disable (eps*) (rt*)))

(local-defthmd approx-error-38
  (implies (and (not (earlyp))
                (not (zp j))
		(>= j 3)
		(hyp (- j 2))
		(hyp j))
           (< (abs (- (r* j) (rt* j)))
	      (expt 2 54)))
  :hints (("Goal" :use (approx-error-37
                        (:instance bits-plus-bits (x (sig* j)) (n 64) (p 54) (m 0))
			(:instance bitn-plus-bits (x (sig* j)) (n 53) (m 0))
                        (:instance bits-plus-bits (x (chi* j)) (n 64) (p 54) (m 0))
			(:instance bitn-plus-bits (x (chi* j)) (n 53) (m 0))
			(:instance bitn-0-1 (x (sig* j)) (n 53))
			(:instance bitn-0-1 (x (chi* j)) (n 53))
			(:instance bits-bounds (x (sig* j)) (i 52) (j 0))
			(:instance bits-bounds (x (chi* j)) (i 52) (j 0)))
                  :in-theory (enable bvecp eps* r* rt*))))

(defund rp13 (j)
  (bits (rp (- j 2)) 61 49))

(defund rn13 (j)
  (bits (rn (- j 2)) 61 49))

(defund divmult (j)
  (case (q (1- j))
    ((4 -4) (bits (divsigned (1- j)) 62 50))
    ((3 -3) (bits (div3signed (1- j)) 64 52))
    ((2 -2) (bits (divsigned (1- j)) 63 51))
    ((1 -1) (bits (divsigned (1- j)) 64 52))
    (t 0)))

(defund sum (j)
  (bits (logxor (logxor (bits (rp13 j) 12 1)
                        (bits (rn13 j) 12 1))
                (bits (divmult j) 12 1))
        11 0))

(defund carry (j)
  (bits (logior (logand (bits (rp13 j) 11 0)
                        (lognot (bits (rn13 j) 11 0)))
                (logand (logior (bits (rp13 j) 11 0)
                                (lognot (bits (rn13 j) 11 0)))
                        (bits (divmult j) 11 0)))
        11 0))

(defund sum12 (j)
  (if1 (log= (q (1- j)) 0)
       (bits (+ (+ (bits (rp13 j) 12 1)
                   (lognot (bits (rn13 j) 12 1)))
                1)
             11 0)
       (bits (+ (+ (carry j) (lognot (sum j))) 1)
             11 0)))

(in-theory (disable (rp13) (rn13) (divmult) (sum) (carry) (sum12)))

(defthmd computers11-lemma
  (equal (computers11 (rp (- j 2)) (rn (- j 2)) (q (1- j)) (divsigned (1- j)) (div3signed (1- j)))
         (bits (sum12 j) 11 1))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(rp13 rn13 divmult sum carry sum12 computers11))))

(defthm it1-j-1
  (implies (and (natp j)
                (> j 1)
		(<= j (n))
		(not (it1 j)))
	   (it1 (+ -1 j)))
  :hints (("Goal" :in-theory (enable it1))))

(in-theory (disable (it1)))

(defthm it1-2
  (implies (not (earlyp))
           (it1 2))
  :hints (("Goal" :in-theory (enable it1))))

(local-defthmd approx-error-39
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs11 (1- j))
	          (bits (sum12 j) 11 1)))
  :hints (("Goal" :expand ((rs11 (+ -1 j)))
                  :use (computers11-lemma
                        (:instance mod-mod-2-not-equal (m (1- j)))
                        (:instance mod012 (m (1- j)))))))

(local-defthmd approx-error-40
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (pi* j) 64 3)
	          (bits (rp (- j 2)) 61 0)))
  :hints (("Goal" :in-theory (enable bits pi*)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-prod (k 8) (m (rp (- j 2))) (n (expt 2 62)))))))

(local-defthmd approx-error-41
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (nu* j) 64 3)
	          (bits (lognot (rn (- j 2))) 61 0)))
  :hints (("Goal" :in-theory (enable bits nu* lognot)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
                        (:instance mod-prod (k 8) (m (lognot (rn (- j 2)))) (n (expt 2 62)))))))

(local-defthmd approx-error-42
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (del* j) 64 52)
	          (bits (- (+ (* (q (1- j)) (div)) (alpha* j))) 64 52)))
  :hints (("Goal" :in-theory (enable bits delta* del*)
                  :use (q-vals))))

(set-rewrite-stack-limit 10000)

(local-defthm nextdigit-sign
  (implies (bvecp rs10 10)
           (or (= (nextdigit rs10 (computecmpconst (bits (div) 65 60))) 0)
	       (and (> (nextdigit rs10 (computecmpconst (bits (div) 65 60))) 0)
	            (= (bitn rs10 9) 0))
	       (and (< (nextdigit rs10 (computecmpconst (bits (div) 65 60))) 0)
	            (= (bitn rs10 9) 1))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable m maxk computecmpconst nextdigit)
                  :use ((:instance bvecp-member (x rs10) (n 10))
		        (:instance bvecp-member (x (bits (div) 65 60)) (n 6))))))

(set-rewrite-stack-limit acl2::*default-rewrite-stack-limit*)

(local-defthm q-sign
  (implies (and (not (earlyp)) (not (zp j)) (> j 1))
           (or (= (q j) 0)
	       (and (> (q j) 0)
	            (= (bitn (rs10 (1- j)) 9) 0))
	       (and (< (q j) 0)
	            (= (bitn (rs10 (1- j)) 9) 1))))
  :rule-classes ()
  :hints (("Goal" :expand ((q j))
                  :use ((:instance nextdigit-sign (rs10 (rs10 (1- j)))))
		  :in-theory (enable cmpconst))))

(defthmd div3-div
  (implies (not (earlyp))
           (equal (div3) (* 3 (div))))
  :hints (("Goal" :in-theory (enable div3-rewrite div-rewrite))))

(local-defthmd approx-error-43
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (del* j) 64 52)
	          (bits (divmult j) 12 0)))
  :hints (("Goal" :in-theory (enable div3-div approx-error-42 divmult divsigned div3signed alpha* lognot)
                  :use ((:instance q-vals (j (1- j)))
		        (:instance bits-shift-up-1 (k 1) (x (div)) (i 64) (j 52))
		        (:instance bits-shift-up-1 (k 2) (x (div)) (i 64) (j 52))
			(:instance bits-plus-mult-1 (k 1) (x 1) (y (- (1+ (div)))) (n 64) (m 52))
			(:instance bits-plus-mult-1 (k 2) (x 3) (y (- (1+ (div)))) (n 64) (m 52))
		        (:instance q-sign (j (1- j)))))))

(local-defthmd approx-error-44
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (rp13 j) 12 1)
	          (bits (rp (- j 2)) 61 50)))
  :hints (("Goal" :in-theory (enable bits-bits rp13)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))))))

(local-defthmd approx-error-45
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(= (q (1- j)) 0))
           (equal (bits (sig* j) 64 53)
	          (bits (rp13 j) 12 1)))
  :hints (("Goal" :in-theory (enable sig* approx-error-40 approx-error-44)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-bits (x (pi* j)) (i 64) (j 3) (k 61) (l 50))
		        (:instance bits-bits (x (rp (- j 2))) (i 61) (j 0) (k 61) (l 50))))))

(local-defthmd approx-error-46
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (lognot (bits (rn13 j) 12 1)) 11 0)
	          (bits (lognot (rn (- j 2))) 61 50)))
  :hints (("Goal" :in-theory (enable bits-lognot-bits bits-bits rn13)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))))))

(local-defthmd approx-error-47
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(= (q (1- j)) 0))
           (equal (bits (chi* j) 64 53)
	          (bits (lognot (bits (rn13 j) 12 1)) 11 0)))
  :hints (("Goal" :in-theory (enable chi* approx-error-41 approx-error-46)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-bits (x (nu* j)) (i 64) (j 3) (k 61) (l 50))
		        (:instance bits-bits (x (lognot (rn (- j 2)))) (i 61) (j 0) (k 61) (l 50))))))

(local-defthmd approx-error-48
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(= (q (1- j)) 0))
           (equal (sum12 j)
	          (mod (+ (bits (rp13 j) 12 1)
		          (bits (lognot (bits (rn13 j) 12 1)) 11 0)
			  1)
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable bits-mod sum12)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
		        (:instance mod-sum (a (1+ (bits (rp13 j) 12 1))) (b (lognot (bits (rn13 j) 12 1))) (n (expt 2 12)))))))

(local-defthmd approx-error-49
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(= (q (1- j)) 0))
           (equal (sum12 j)
	          (mod (+ (bits (sig* j) 64 53)
		          (bits (chi* j) 64 53)
			  1)
		       (expt 2 12))))
  :hints (("Goal" :in-theory (enable approx-error-45 approx-error-47 approx-error-48))))

(local-defthmd approx-error-50
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (pi* j) 64 53)
	          (bits (rp13 j) 12 1)))
  :hints (("Goal" :in-theory (enable approx-error-40 approx-error-44)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-bits (x (pi* j)) (i 64) (j 3) (k 61) (l 50))
		        (:instance bits-bits (x (rp (- j 2))) (i 61) (j 0) (k 61) (l 50))))))

(local-defthmd approx-error-51
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (nu* j) 64 53)
	          (bits (lognot (rn13 j)) 12 1)))
  :hints (("Goal" :in-theory (enable bits-lognot-bits approx-error-41)
                  :use (approx-error-46
		        (:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-bits (x (nu* j)) (i 64) (j 3) (k 61) (l 50))
		        (:instance bits-bits (x (lognot (rn (- j 2)))) (i 61) (j 0) (k 61) (l 50))))))

(local-defthmd approx-error-52
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (del* j) 64 53)
	          (bits (divmult j) 12 1)))
  :hints (("Goal" :in-theory (enable approx-error-43)
                  :use ((:instance bits-bits (x (del* j)) (i 64) (j 52) (k 12) (l 1))
		        (:instance bits-bits (x (divmult j)) (i 12) (j 0) (k 12) (l 1))))))

(defund sig* (j)
  (if (= (q (1- j)) 0)
      (pi* j)
    (logxor (logxor (pi* j) (nu* j))
            (del* j))))

(defthm int-pi*
  (implies (and (natp j) (hyp (- j 2)))
           (integerp (pi* j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable pi*)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))))))

(defthm int-nu*
  (implies (and (natp j) (hyp (- j 2)))
           (integerp (nu* j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable nu*)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))))))

(local-defthmd approx-error-53
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (sig* j) 64 53)
	          (logxor (logxor (bits (rp13 j) 12 1)
		                  (bits (lognot (rn13 j)) 12 1))
		          (bits (divmult j) 12 1))))
  :hints (("Goal" :in-theory (enable sig* bits-logxor approx-error-50 approx-error-51 approx-error-52))))

(local-defthmd approx-error-54
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (sum j)
	          (logxor (logxor (bits (rp13 j) 12 1)
		                  (bits (rn13 j) 12 1)
		          (bits (divmult j) 12 1)))))
  :hints (("Goal" :in-theory (enable sum bits-logxor))))

(local-defthmd approx-error-55
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (lognot (sum j))
	          (logxor (logxor (bits (rp13 j) 12 1)
		                  (lognot (bits (rn13 j) 12 1))
		          (bits (divmult j) 12 1)))))
  :hints (("Goal" :in-theory (enable approx-error-54 lognot-logxor))))

(local-defthmd approx-error-56
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (lognot (sum j)) 11 0)
	          (logxor (logxor (bits (rp13 j) 12 1)
		                  (bits (lognot (rn13 j)) 12 1))
		          (bits (divmult j) 12 1))))
  :hints (("Goal" :in-theory (enable approx-error-55 bits-logxor bits-bits bits-lognot-bits))))

(local-defthmd approx-error-57
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (lognot (sum j)) 11 0)
	          (bits (sig* j) 64 53)))
  :hints (("Goal" :use (approx-error-56 approx-error-53))))

(local-defthmd approx-error-58
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (chi* j) 64 53)
	          (bits (logior (logand (pi* j) (nu* j))
                                (logand (logior (pi* j) (nu* j))
  	                                (del* j)))
			63 52)))
  :hints (("Goal" :in-theory (enable chi*)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-shift-up-1 (k 1) (i 64) (j 53)
			                           (x (logior (logand (pi* j) (nu* j))
                                                      (logand (logior (pi* j) (nu* j))
  	                                                      (del* j)))))))))

(local-defthmd approx-error-59
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (rp13 j) 11 0)
	          (bits (rp (- j 2)) 60 49)))
  :hints (("Goal" :in-theory (enable bits-bits rp13)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))))))

(local-defthmd approx-error-60
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (pi* j) 63 52)
	          (bits (rp13 j) 11 0)))
  :hints (("Goal" :in-theory (enable approx-error-40 approx-error-59)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-bits (x (pi* j)) (i 64) (j 3) (k 60) (l 49))
		        (:instance bits-bits (x (rp (- j 2))) (i 61) (j 0) (k 60) (l 49))))))

(local-defthmd approx-error-61
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (lognot (bits (rn13 j) 11 0)) 11 0)
	          (bits (lognot (rn (- j 2))) 60 49)))
  :hints (("Goal" :in-theory (enable bits-lognot-bits bits-bits rn13)
                  :use ((:instance bvecp-rp-rn (j (- j 2)))))))

(local-defthmd approx-error-62
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (nu* j) 63 52)
	          (bits (lognot (rn13 j)) 11 0)))
  :hints (("Goal" :in-theory (enable bits-lognot-bits approx-error-41)
                  :use (approx-error-61
		        (:instance bvecp-rp-rn (j (- j 2)))
		        (:instance bits-bits (x (nu* j)) (i 64) (j 3) (k 60) (l 49))
		        (:instance bits-bits (x (lognot (rn (- j 2)))) (i 61) (j 0) (k 60) (l 49))))))

(local-defthmd approx-error-63
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (del* j) 63 52)
	          (bits (divmult j) 11 0)))
  :hints (("Goal" :in-theory (enable approx-error-43)
                  :use ((:instance bits-bits (x (del* j)) (i 64) (j 52) (k 11) (l 0))
		        (:instance bits-bits (x (divmult j)) (i 12) (j 0) (k 11) (l 0))))))

(local-defthmd approx-error-64
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (bits (chi* j) 64 53)
	          (logior (logand (bits (rp13 j) 11 0) (bits (lognot (rn13 j)) 11 0))
                          (logand (logior (bits (rp13 j) 11 0) (bits (lognot (rn13 j)) 11 0))
  	                          (bits (divmult j) 11 0)))))
  :hints (("Goal" :in-theory (enable approx-error-58 approx-error-60 approx-error-62 approx-error-63
                                     bits-logand bits-logior bits-lognot-bits))))

(local-defthmd approx-error-65
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (carry j)
	          (bits (chi* j) 64 53)))
  :hints (("Goal" :in-theory (enable approx-error-64 carry bits-lognot-bits bits-logand bits-logior))))

(local-defthmd approx-error-66
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j)
		(not (= (q (1- j)) 0)))
           (equal (sum12 j)
	          (mod (+ (+ (carry j) (bits (lognot (sum j)) 11 0)) 1)
                       4096)))
  :hints (("Goal" :in-theory (enable bits-mod sum12)
                  :use ((:instance mod-sum (a (1+ (carry j))) (b (lognot (sum j))) (n 4096))))))

(local-defthmd approx-error-67
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (sum12 j)
	          (mod (+ (bits (sig* j) 64 53)
		          (bits (chi* j) 64 53)
			  1)
                       (expt 2 12))))
  :hints (("Goal" :use (approx-error-49) :in-theory (enable approx-error-57 approx-error-65 approx-error-66))))

(local-defthmd approx-error-68
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (sum12 j)
	          (mod (+ (* 2 (bits (sig* j) 64 54))
		          (bitn (sig* j) 53)
		          (* 2 (bits (chi* j) 64 54))
		          (bitn (chi* j) 53)
			  1)
                       (expt 2 12))))
  :hints (("Goal" :in-theory (enable approx-error-67)
                  :use ((:instance bits-plus-bitn (x (sig* j)) (n 64) (m 53))
		        (:instance bits-plus-bitn (x (chi* j)) (n 64) (m 53))))))

(local-defthmd approx-error-69
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs11 (+ -1 j))
	          (fl (/ (mod (+ (* 2 (bits (sig* j) 64 54))
		                 (bitn (sig* j) 53)
		                 (* 2 (bits (chi* j) 64 54))
		                 (bitn (chi* j) 53)
			         1)
			      (expt 2 12))
			 2))))
  :hints (("Goal" :use (approx-error-39) :in-theory (enable approx-error-68 bits))))

(local-defthmd approx-error-70
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs11 (+ -1 j))
	          (mod (fl (/ (+ (* 2 (bits (sig* j) 64 54))
		                 (bitn (sig* j) 53)
		                 (* 2 (bits (chi* j) 64 54))
		                 (bitn (chi* j) 53)
			         1)
			      2))
		       (expt 2 11))))
  :hints (("Goal" :use ((:instance fl-mod (a (+ (* 2 (bits (sig* j) 64 54))
		                                (bitn (sig* j) 53)
		                                (* 2 (bits (chi* j) 64 54))
		                                (bitn (chi* j) 53)
			                        1))
				          (m 2048)
					  (n 2)))
                  :in-theory (enable approx-error-69))))

(local-defthmd approx-error-71
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (fl (/ (+ (* 2 (bits (sig* j) 64 54))
   	                    (bitn (sig* j) 53)
		            (* 2 (bits (chi* j) 64 54))
		            (bitn (chi* j) 53)
			    1)
		         2))
		  (+ (bits (sig* j) 64 54)
		     (bits (chi* j) 64 54)
		     (fl (/ (+ (bitn (sig* j) 53) (bitn (chi* j) 53) 1) 2))))))

(local-defthmd approx-error-72
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs11 (+ -1 j))
	          (mod (+ (bits (sig* j) 64 54)
		          (bits (chi* j) 64 54)
		          (fl (/ (+ (bitn (sig* j) 53) (bitn (chi* j) 53) 1) 2)))
		       (expt 2 11))))
  :hints (("Goal" :use (approx-error-70 approx-error-71))))

(local-defthmd approx-error-73
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs11 (+ -1 j))
	          (mod (/ (rt* j) (expt 2 54))
		       (expt 2 11))))
  :hints (("Goal" :in-theory (enable rt* approx-error-72 eps*)
                  :use ((:instance bitn-0-1 (x (sig* j)) (n 53))
		        (:instance bitn-0-1 (x (chi* j)) (n 53))))))

;;----------------------------------------------------------------------------

(defund d* (j) (- (* (q j) (div))))

(defund dt* (j)
  (if (<= (q j) 0)
      (- (* (q j) (div)))
    (- (1+ (* (q j) (div))))))

(defthm dt-error
  (implies (not (earlyp))
           (and (>= (- (d* j) (dt* j)) 0)
	        (<= (- (d* j) (dt* j)) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable d* dt*))))

(defund c* (j)
  (if (and (= (bitn (rt* j) 54) 0)
           (= (bitn (dt* j) 57) 0))
      0 1))

(defund s* (j)
  (+ (fl (/ (rt* j) (expt 2 55)))
     (fl (/ (dt* j) (expt 2 58)))
     (c* j)))

(defund divmult11 (j)
  (case (q j)
    ((4 -4) (bits (divsigned j) 65 55))
    ((3 -3) (bits (div3signed j) 67 57))
    ((2 -2) (bits (divsigned j) 66 56))
    ((1 -1) (bits (divsigned j) 67 57))
    (0 (bits 0 10 0))
    (t 0)))

(defund sum11 (j)
  (bits (+ (+ (rs11 (1- j)) (divmult11 j)) 1) 10 0))

(in-theory (disable (divmult11) (sum11)))

(defthmd computers10-lemma
  (equal (computers10 (divsigned j) (div3signed j) (q j) (rs11 (+ -1 j)))
         (bits (sum11 j) 10 1))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(divmult11 sum11 computers10))))

(local-defthmd approx-error-74
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs10 j)
	          (bits (sum11 j) 10 1)))
  :hints (("Goal" :expand ((rs10 j))
                  :use (computers10-lemma
                        (:instance mod012 (m j))))))

(local-defthmd approx-error-75
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (divmult11 j)
	          (bits (dt* j) 67 57)))
  :hints (("Goal" :in-theory (enable div3-div dt* divmult11 divsigned div3signed lognot)
                  :use (q-sign q-vals
			(:instance bits-plus-mult-1 (k 1) (x 1) (y (- (1+ (div)))) (n 67) (m 57))
			(:instance bits-plus-mult-1 (k 2) (x 3) (y (- (1+ (div)))) (n 67) (m 57))
		        (:instance bits-shift-up-1 (k 1) (x (div)) (i 67) (j 57))
		        (:instance bits-shift-up-1 (k 2) (x (div)) (i 67) (j 57))))))

(local-defthmd approx-error-76
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (divmult11 j)
	          (mod (fl (/ (dt* j) (expt 2 57))) (expt 2 11))))
  :hints (("Goal" :in-theory (enable approx-error-75)
                  :use ((:instance bits-mod-fl (x (dt* j)) (i 68) (j 57))))))

(local-defthmd approx-error-77
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (sum11 j)
	          (mod (+ (rs11 (1- j)) (mod (fl (/ (dt* j) (expt 2 57))) (expt 2 11)) 1)
		       (expt 2 11))))
  :hints (("Goal" :in-theory (enable sum11 bits-mod approx-error-76))))

(local-defthmd approx-error-78
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (sum11 j)
	          (mod (+ (mod (/ (rt* j) (expt 2 54)) (expt 2 11)) (fl (/ (dt* j) (expt 2 57))) 1)
		       (expt 2 11))))
  :hints (("Goal" :in-theory (enable approx-error-73 approx-error-77)
                  :use ((:instance mod-sum (a (+ 1 (rs11 (1- j)))) (b (fl (/ (dt* j) (expt 2 57)))) (n (expt 2 11)))))))

(local-defthmd approx-error-79
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (sum11 j)
	          (mod (+ (/ (rt* j) (expt 2 54))
		          (fl (/ (dt* j) (expt 2 57)))
			  1)
		       (expt 2 11))))
  :hints (("Goal" :in-theory (enable rt* approx-error-78)
                  :use ((:instance mod-sum (a (+ 1 (fl (/ (dt* j) (expt 2 57)))))
		                           (b (/ (rt* j) (expt 2 54)))
					   (n (expt 2 11)))))))

(local-defthmd approx-error-80
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
	   (integerp (/ (rt* j) (expt 2 54))))
  :hints (("Goal" :in-theory (enable rt*))))

(local-defthmd approx-error-81
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
	   (equal (/ (rt* j) (expt 2 54))
	          (+ (* 2 (fl (/ (rt* j) (expt 2 55))))
		     (bitn (rt* j) 54))))
  :hints (("Goal" :use (approx-error-80 (:instance mod-def (x (/ (rt* j) (expt 2 54))) (y 2)))
                  :in-theory (enable bitn-def))))

(local-defthmd approx-error-82
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
	   (equal (fl (/ (dt* j) (expt 2 57)))
	          (+ (* 2 (fl (* (expt 2 -58) (dt* j))))
		     (bitn (dt* j) 57))))
  :hints (("Goal" :use (bvecp-div (:instance fl/int-rewrite (x (/ (dt* j) (expt 2 57))) (n 2))
                        (:instance mod-def (x (fl (/ (dt* j) (expt 2 57)))) (y 2)))
                  :in-theory (enable dt* bitn-def))))

(local-defthmd approx-error-83
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (sum11 j)
	          (mod (+ (* 2 (fl (/ (rt* j) (expt 2 55))))
		          (bitn (rt* j) 54)
			  (* 2 (fl (* (expt 2 -58) (dt* j))))
		          (bitn (dt* j) 57)
		          1)
		       (expt 2 11))))
  :hints (("Goal" :in-theory (enable approx-error-79)
                  :use (approx-error-81 approx-error-82))))

(local-defthmd approx-error-84
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs10 j)
	          (mod (fl (+ (fl (/ (rt* j) (expt 2 55)))
		              (fl (* (expt 2 -58) (dt* j)))
		              (/ (+ (bitn (rt* j) 54)			  
		                    (bitn (dt* j) 57)
		                    1)
				 2)))
		       (expt 2 10))))
  :hints (("Goal" :in-theory (enable approx-error-74 approx-error-83)
                  :use ((:instance bits-mod-fl (x (mod (+ (* 2 (fl (/ (rt* j) (expt 2 55))))
		                                          (bitn (rt* j) 54)
		                                     	  (* 2 (fl (* (expt 2 -58) (dt* j))))
		                                          (bitn (dt* j) 57)
		                                          1)
						       2048))
					       (i 11)
					       (j 1))
			(:instance fl-mod (a (+ (* 2 (fl (/ (rt* j) (expt 2 55))))
		                                (bitn (rt* j) 54)
		                                (* 2 (fl (* (expt 2 -58) (dt* j))))
		                                (bitn (dt* j) 57)
		                                1))
					  (m 1024)
					  (n 2))))))

(local-defthmd approx-error-85
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rs10 j)
	          (mod (+ (fl (/ (rt* j) (expt 2 55)))
		          (fl (* (expt 2 -58) (dt* j)))
		          (fl (/ (+ (bitn (rt* j) 54)			  
		                    (bitn (dt* j) 57)
		                    1)
				 2)))
		       (expt 2 10))))
  :hints (("Goal" :in-theory (enable approx-error-84)
                  :use ((:instance fl+int-rewrite (x (/ (+ (bitn (rt* j) 54) (bitn (dt* j) 57) 1) 2))
		                                  (n (+ (fl (/ (rt* j) (expt 2 55))) (fl (* (expt 2 -58) (dt* j))))))))))

(local-defthmd approx-error-86
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
	   (equal (rs10 j)
	          (mod (s* j) 1024)))
  :hints (("Goal" :in-theory (enable approx-error-85 c* s*)
                  :use ((:instance bitn-0-1 (x (rt* j)) (n 54))
		        (:instance bitn-0-1 (x (dt* j)) (n 57))))))

(local-defun x! (j) (+ (* 8 (r* j)) (d* j)))

(local-defun y! (j) (* (expt 2 58) (s* j)))

(defthm int-r*
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp (- j 2))
		(>= j 3))
	   (integerp (r* j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use ((:instance approx-error-4 (j (- j 2))))
                  :in-theory (enable pi* sig* r* alpha* chi*))))

(local-defthmd approx-error-87
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (mod (* 8(r* j)) (expt 2 68))
	          (mod (* (expt 2 70) (r (1- j))) (expt 2 68))))
  :hints (("Goal" :use (approx-error-30
                        (:instance mod-prod (k 8) (m (r* j)) (n (expt 2 65)))
                        (:instance mod-prod (k 8) (m (* (expt 2 67) (r (1- j)))) (n (expt 2 65)))))))

(local-defthmd approx-error-88
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (mod (x! j) (expt 2 68))
	          (mod (- (* (expt 2 70) (r (1- j))) (* (expt 2 67) (q j) (d))) (expt 2 68))))
  :hints (("Goal" :in-theory (e/d (x! d* div-rewrite) (ACL2::PREFER-POSITIVE-ADDENDS-EQUAL ACL2::PREFER-POSITIVE-ADDENDS-<))
                  :use (q-vals approx-error-87
		        (:instance mod-sum (b (* (expt 2 67) (r (1- j)))) (a (- (* (q j) (div)))) (n (expt 2 68)))
			(:instance mod-sum (b (r* j)) (a (- (* (q j) (div)))) (n (expt 2 68)))))))

(local-defthmd approx-error-89
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (- (* (expt 2 70) (r (1- j))) (* (expt 2 67) (q j) (d)))
	          (* (expt 2 67) (r j))))
  :hints (("Goal" :use (q-vals
		        (:instance r-recurrence (j (1- j)))))))

(local-defthmd approx-error-90
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (mod (x! j) (expt 2 68))
	          (mod (* (expt 2 67) (r j)) (expt 2 68))))
  :hints (("Goal" :use (approx-error-88 approx-error-89)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd approx-error-91
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (si (mod (x! j) (expt 2 68)) 68)
	          (* (expt 2 67) (r j))))
  :hints (("Goal" :use (int-r p-vals approx-error-10 approx-error-90 (:instance si-bits (x (* (expt 2 67) (r j))) (n 68))))))

(local-defthmd approx-error-92
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (si (mod (y! j) (expt 2 68)) 68)
	          (* (expt 2 58) (si (rs10 j) 10))))
  :hints (("Goal" :in-theory (enable bvecp approx-error-86 y!)
                  :use ((:instance mod-prod (k (expt 2 58)) (m (s* j)) (n 1024))
		        (:instance si-shift (r (rs10 j)) (k 58) (n 10))))))

(local-defthmd approx-error-93
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (bits (rt* j) 53 0)
	          0))
  :hints (("Goal" :in-theory (enable rt*)
                  :use ((:instance bits-shift-up-1 (x (+ (bits (sig* j) 64 54) (bits (chi* j) 64 54) (eps* j)))
		                                   (k 54) (i 53) (j 0))))))

(local-defthmd approx-error-94
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (rt* j)
	          (+ (* (expt 2 55) (fl (/ (rt* j) (expt 2 55))))
		     (* (expt 2 54) (bitn (rt* j) 54)))))
  :hints (("Goal" :in-theory (enable approx-error-93 bits-mod)
                  :use ((:instance mod-def (x (rt* j)) (y (expt 2 55)))
		        (:instance bitn-plus-bits (x (rt* j)) (n 54) (m 0))))))

(local-defthmd approx-error-95
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (dt* j)
	          (+ (* (expt 2 58) (fl (/ (dt* j) (expt 2 58))))
		     (* (expt 2 57) (bitn (dt* j) 57))
		     (bits (dt* j) 56 0))))
  :hints (("Goal" :in-theory (enable bits-mod)
                  :use ((:instance mod-def (x (dt* j)) (y (expt 2 58)))
		        (:instance bitn-plus-bits (x (dt* j)) (n 57) (m 0))))))

(local-defthmd approx-error-96
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (equal (- (+ (* 8 (rt* j)) (dt* j))
	             (* (expt 2 58) (s* j)))
	          (+ (* (expt 2 57) (- (+ (bitn (rt* j) 54) (bitn (dt* j) 57)) (* 2 (c* j))))
		     (bits (dt* j) 56 0))))
  :hints (("Goal" :in-theory (enable s*) :use (approx-error-94 approx-error-95))))

(local-defthmd approx-error-97
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (<= (abs (- (+ (* 8 (rt* j)) (dt* j))
	               (* (expt 2 58) (s* j))))
	       (expt 2 57)))
  :hints (("Goal" :in-theory (enable c*)
                  :use (approx-error-96
		        (:instance bitn-0-1 (x (dt* j)) (n 57))
			(:instance bitn-0-1 (x (rt* j)) (n 54))
			(:instance bits-bounds (x (dt* j)) (i 56) (j 0))))))

(local-defthmd approx-error-98
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (<= (abs (- (r* j) (rt* j)))
	       (1- (expt 2 54))))
  :hints (("Goal" :in-theory (enable sig* chi* r* rt*) :use (approx-error-38))))

(local-defthmd approx-error-99
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (< (abs (- (x! j) (y! j)))
	      (expt 2 58)))
  :hints (("Goal" :in-theory (enable x! y!)
                  :use (approx-error-97 approx-error-98 dt-error))))

(local-defthmd approx-error-100
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (< (abs (- (* (expt 2 67) (r j))
	              (* (expt 2 58) (si (rs10 j) 10))))
	      (expt 2 58)))
  :hints (("Goal" :in-theory (enable sig* r*)
                  :use (approx-error-10 approx-error-91 approx-error-92 approx-error-99
                        (:instance si-approx (x (x! j)) (y (y! j)) (n 68))))))

(local-defthmd approx-error-odd
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
		(<= j (n))
		(not (it1 j))
		(hyp (- j 2))
		(hyp j))
           (< (abs (- (* 8 (r j)) (approx j)))
	      1/64))
  :hints (("Goal" :use (approx-error-100) :in-theory (enable approx))))

(local-defthmd approx-error
  (implies (and (not (earlyp))
                (not (zp j))
		(<= j (n))
		(hyp j)
		(or (< j 3) (hyp (- j 2))))
           (< (abs (- (* 8 (r j)) (approx j)))
	      1/64))
  :hints (("Goal" :use (approx-error-odd approx-error-even))))

;;-----------------------------------------------------------------------------------------

(local-defthmd int-approx64
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j)
		(or (< j 3) (hyp (- j 2))))
	   (and (rationalp (approx j))
	        (integerp (* 64 (approx j)))))
  :hints (("Goal" :in-theory (enable approx si rs10))))

(local-defthmd hyp-r-bound
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
	   (<= (abs (r j)) (* 4/7 (d))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd r-bound-induct
  (implies (and (not (earlyp))
                (not (zp j))
		(<= j (n))
		(hyp j)
		(or (< j 3) (hyp (- j 2))))
	   (<= (abs (r (1+ j)))
	       (* 4/7 (d))))
  :hints (("Goal" :use (approx-error int-approx64 hyp-r-bound
                        (:instance q-maxk (j (1+ j)))
			(:instance r-bound-inv (approx (approx j)))))))

;;-----------------------------------------------------------------------------------------

(defund remsign (j) (bitn (rs10 (1- j)) 9))

(in-theory (disable (remsign)))

(local-defthmd rp-rewrite-1
  (implies (and (natp j) (> j 1))
           (equal (rp j)
	          (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (remsign j) (q j) (divsigned j) (div3signed j) (int32))))))
  :hints (("Goal" :in-theory (enable remsign rp rn))))

(local-defthmd rn-rewrite-1
  (implies (and (natp j) (> j 1))
           (equal (rn j)
	          (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (remsign j) (q j) (divsigned j) (div3signed j) (int32))))))
  :hints (("Goal" :in-theory (enable remsign rp rn))))

(local-defund divmult71 (j)
  (case (q j)
    ((4 -4) (let* ((divmult (bits (ash (divsigned j) 2) 70 0))
                   (divmult (setbitn divmult 71 0 (lognot1 (remsign j)))))
              (setbitn divmult 71 1 (lognot1 (remsign j)))))
    ((3 -3) (div3signed j))
    ((2 -2) (let ((divmult (bits (ash (divsigned j) 1) 70 0)))
              (setbitn divmult 71 0 (lognot1 (remsign j)))))
    ((1 -1) (divsigned j))
    (t 0)))

(local-defund rp8 (j) (bits (ash (rp (1- j)) 3) 70 0))

(local-defund rn8 (j) (bits (ash (rn (1- j)) 3) 70 0))

(local-defund sum71 (j)
  (logxor (logxor (rn8 j) (rp8 j)) (divmult71 j)))

(local-defund carry71 (j)
  (logior (logand (bits (lognot (rn8 j)) 70 0) (rp8 j))
          (logand (logior (bits (lognot (rn8 j)) 70 0) (rp8 j))
                  (divmult71 j))))
		  
(local-defund rp* (j)
  (if1 (log= (q j) 0)
       (rp8 j)
    (if1 (int32)
         (setbitn (setbits (rp (1- j)) 71 70 33 (bits (carry71 j) 69 32)) 71 32 (lognot1 (remsign j)))
       (setbitn (setbits (rp (1- j)) 71 70 1 (bits (carry71 j) 69 0)) 71 0 (lognot1 (remsign j))))))

(local-defund rn* (j)
  (if1 (log= (q j) 0)
       (rn8 j)
    (if1 (int32)
         (setbits (rn (1- j)) 71 70 32 (bits (sum71 j) 70 32))
       (sum71 j))))

(local-in-theory (disable (divmult71) (rp8) (rn8) (sum71) (carry71) (rp*) (rn*)))

(local-defthmd nextrem-lemma
  (implies (and (natp j) (> j 1))
           (and (equal (rp j) (rp* j))
	        (equal (rn j) (rn* j))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(divmult71 rp8 rn8 sum71 carry71 rp* rn* rp-rewrite-1 rn-rewrite-1 nextrem))))

(local-defthm int-r-1
  (implies (not (earlyp))
           (integerp (* (expt 2 (p)) (d))))
  :hints (("Goal" :use (int-quot clza>=0 clza<=clzb clzb<=62)
                  :in-theory (enable d p b0-rewrite))))

(local-defthmd bits-div-0
  (implies (not (earlyp))
           (equal (bits (div) (- 66 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable div-rewrite)
                  :use (p-vals int-r-1 (:instance bits-shift-up-2 (x (* (expt 2 (p)) (d))) (i -1) (k (- 67 (p))))))))

(local-defthmd nextrem-1
  (implies (hyp j)
           (and (bvecp (rp j) 71)
                (bvecp (rn j) 71)
                (= (bits (rp j) (- 63 (p)) 0) 0)
                (= (bits (rn j) (- 63 (p)) 0) 0)))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd nextrem-2
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) -1))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (* (expt 2 (+ (p) 3)) (d))))
  :hints (("Goal" :in-theory (enable divmult71 divsigned)
                  :use (p-vals div-bounds div-rewrite bits-div-0 q-sign
                        (:instance bits-plus-bits (x (div)) (n (- 66 (p))) (p (- 64 (p))) (m 0))
                        (:instance bits-plus-bits (x (div)) (n 70) (p (- 64 (p))) (m 0))))))

(local-defthmd nextrem-3
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) -2))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (* (expt 2 (+ (p) 4)) (d))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 divsigned remsign)
                  :use (p-vals div-bounds div-rewrite bits-div-0 q-sign
		        (:instance bits-shift-up-1 (k 1) (x (div)) (i 70) (j (- 64 (p))))
                        (:instance bits-plus-bits (x (div)) (n (- 66 (p))) (p (- 63 (p))) (m 0))
                        (:instance bits-plus-bits (x (div)) (n 69) (p (- 63 (p))) (m 0))))
	  ("Subgoal 2" :in-theory (enable cat))))

(local-defthmd nextrem-4
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) -4))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (* (expt 2 (+ (p) 5)) (d))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 divsigned remsign)
                  :use (p-vals div-bounds div-rewrite bits-div-0 q-sign
		        (:instance bits-shift-up-1 (k 2) (x (div)) (i 70) (j (- 64 (p))))
                        (:instance bits-plus-bits (x (div)) (n (- 66 (p))) (p (- 62 (p))) (m 0))
                        (:instance bits-plus-bits (x (div)) (n 68) (p (- 62 (p))) (m 0))))
	  ("Subgoal 2" :in-theory (enable cat))))
	  
(local-defthmd nextrem-5
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 1))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (bits (lognot (div)) 70 (- 64 (p)))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 divsigned remsign)
                  :use (p-vals q-sign))))

(local-defthm nextrem-6
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 1))
           (equal (bits (lognot (div)) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 3)) (d))))))
  :hints (("Goal" :in-theory (enable bits-lognot bvecp)
                  :use (p-vals div-bounds div-rewrite bits-div-0
                        (:instance bits-plus-bits (x (div)) (n (- 66 (p))) (p (- 64 (p))) (m 0))
                        (:instance bits-plus-bits (x (div)) (n 70) (p (- 64 (p))) (m 0))))))

(local-defthmd nextrem-7
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 1))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 3)) (d))))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 divsigned)
                  :use (nextrem-5 nextrem-6))))

(local-defthmd nextrem-8-64
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 2))
           (equal (bits (divmult71 j) 70 0)
	          (1+ (* 2 (bits (lognot (div)) 69 0)))))
  :hints (("Goal" :in-theory (enable cat bvecp bits-bits divmult71 divsigned remsign)
                  :use (p-vals q-sign
		        (:instance bits-bounds (x (lognot (div))) (i 69) (j 0))
		        (:instance bits-shift-up-1 (k 1) (x (bits (lognot (div)) 70 0)) (i 70) (j 1))))))

(local-defthmd nextrem-10-64
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 2))
           (equal (bits (divmult71 j) 70 0)
	          (- (expt 2 71) (1+ (* (expt 2 68) (d))))))
  :hints (("Goal" :in-theory (enable nextrem-8-64 bits-lognot bvecp) :use (div-bounds div-rewrite))))

(local-defthmd nextrem-8-32
  (implies (and (not (earlyp))
                (= (p) 32)
                (not (zp j))
		(> j 1)
                (= (q j) 2))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (bits (lognot (div)) 69 (- 63 (p)))))
  :hints (("Goal" :in-theory (enable bvecp bits-bits divmult71 divsigned remsign)
                  :use (p-vals q-sign		  
		        (:instance bits-shift-up-1 (k 1) (x (bits (lognot (div)) 70 0)) (i 70) (j (- 64 (p))))))))

(local-defthmd nextrem-9-32
  (implies (and (not (earlyp))
                (= (p) 32)
                (not (zp j))
		(> j 1)
                (= (q j) 2))
           (equal (bits (lognot (div)) 69 (- 63 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 4)) (d))))))
  :hints (("Goal" :in-theory (enable bits-lognot bvecp)
                  :use (p-vals div-bounds div-rewrite bits-div-0
                        (:instance bits-plus-bits (x (div)) (n (- 66 (p))) (p (- 63 (p))) (m 0))
                        (:instance bits-plus-bits (x (div)) (n 69) (p (- 63 (p))) (m 0))))))

(local-defthmd nextrem-10-32
  (implies (and (not (earlyp))
                (= (p) 32)
                (not (zp j))
		(> j 1)
                (= (q j) 2))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 4)) (d))))))
  :hints (("Goal" :use (nextrem-8-32 nextrem-9-32))))

(local-defthmd nextrem-10
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 2))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 4)) (d))))))
  :hints (("Goal" :use (nextrem-10-64 nextrem-10-32 p-vals))))

(local-defthmd nextrem-11-64
  (implies (and (not (earlyp))
                (= (p) 64)
                (not (zp j))
		(> j 1)
                (= (q j) 4))
           (equal (bits (divmult71 j) 70 0)
	          (+ 3 (* 4 (bits (lognot (div)) 68 0)))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 divsigned remsign)
                  :use (p-vals q-sign))
	  ("Goal'''" :in-theory (enable cat)
	             :use ((:instance bits-bounds (x (lognot (div))) (i 68) (j 0))
		           (:instance bits-shift-up-1 (k 2) (x (bits (lognot (div)) 70 0)) (i 70) (j 2))))))

(local-defthmd nextrem-13-64
  (implies (and (not (earlyp))
                (= (p) 64)
                (not (zp j))
		(> j 1)
                (= (q j) 4))
           (equal (bits (divmult71 j) 70 0)
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 5)) (d))))))
  :hints (("Goal" :in-theory (enable nextrem-11-64 bits-lognot bvecp) :use (div-bounds div-rewrite))))

(local-defthmd nextrem-11-32
  (implies (and (not (earlyp))
                (= (p) 32)
                (not (zp j))
		(> j 1)
                (= (q j) 4))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (bits (lognot (div)) 68 (- 62 (p)))))
  :hints (("Goal" :in-theory (enable bvecp bits-bits divmult71 divsigned)
                  :use (p-vals q-sign
		        (:instance bits-shift-up-1 (k 2) (x (bits (lognot (div)) 70 0)) (i 70) (j (- 64 (p))))))))

(local-defthmd nextrem-12-32
  (implies (and (not (earlyp))
                (= (p) 32)
                (not (zp j))
		(> j 1)
                (= (q j) 4))
           (equal (bits (lognot (div)) 68 (- 62 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 5)) (d))))))
  :hints (("Goal" :in-theory (enable bits-lognot bvecp)
                  :use (p-vals div-bounds div-rewrite bits-div-0
                        (:instance bits-plus-bits (x (div)) (n (- 66 (p))) (p (- 62 (p))) (m 0))
                        (:instance bits-plus-bits (x (div)) (n 68) (p (- 62 (p))) (m 0))))))

(local-defthmd nextrem-13-32
  (implies (and (not (earlyp))
                (= (p) 32)
                (not (zp j))
		(> j 1)
                (= (q j) 4))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 5)) (d))))))
  :hints (("Goal" :use (nextrem-11-32 nextrem-12-32))))

(local-defthmd nextrem-13
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 4))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 5)) (d))))))
  :hints (("Goal" :use (nextrem-13-64 nextrem-13-32 p-vals))))

(local-defthmd bits-div3-0
  (implies (not (earlyp))
           (equal (bits (div3) (- 66 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable div3-rewrite bits-mod)
                  :use (p-vals int-r-1
		        (:instance mod-def (x (div)) (y (expt 2 (- 67 (p)))))))))

(local-defthmd nextrem-14
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) -3))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (* (expt 2 (+ (p) 3)) 3 (d))))
  :hints (("Goal" :in-theory (enable divmult71 div3signed)
                  :use (p-vals div-bounds div3-rewrite div-rewrite bits-div3-0 q-sign
                        (:instance bits-plus-bits (x (div3)) (n (- 66 (p))) (p (- 64 (p))) (m 0))
                        (:instance bits-plus-bits (x (div3)) (n 70) (p (- 64 (p))) (m 0))))))

(local-defthmd nextrem-15
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 3))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (bits (lognot (div3)) 70 (- 64 (p)))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 div3signed)
                  :use (p-vals q-sign))))

(local-defthm nextrem-16
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 3))
           (equal (bits (lognot (div3)) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 3)) 3 (d))))))
  :hints (("Goal" :in-theory (enable bits-lognot bvecp)
                  :use (p-vals div-bounds div3-rewrite div-rewrite bits-div3-0
                        (:instance bits-plus-bits (x (div3)) (n (- 66 (p))) (p (- 64 (p))) (m 0))
                        (:instance bits-plus-bits (x (div3)) (n 70) (p (- 64 (p))) (m 0))))))

(local-defthmd nextrem-17
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (= (q j) 3))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
	          (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 3)) 3 (d))))))
  :hints (("Goal" :in-theory (enable bvecp divmult71 divsigned)
                  :use (nextrem-15 nextrem-16))))

(local-defthm nextrem-20
  (implies (and (not (earlyp))
                (not (zp j))
		(> j 1)
                (not (= (q j) 0)))
           (equal (bits (divmult71 j) 70 (- 64 (p)))
                  (if (< (q j) 0)
                      (- (* (expt 2 (+ (p) 3)) (q j) (d)))
		    (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 3)) (q j) (d)))))))
  :hints (("Goal" :use (p-vals q-vals nextrem-2 nextrem-3 nextrem-4 nextrem-7 nextrem-10 nextrem-13 nextrem-14 nextrem-17))))

(local-defthm nextrem-21
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (and (bvecp (rp8 (1+ j)) 71)
	        (bvecp (rn8 (1+ j)) 71)))
  :hints (("Goal" :in-theory (enable rp8 rn8))))

(local-defthm nextrem-22
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (and (equal (bits (rp8 (1+ j)) (- 66 (p)) 0) 0)
	        (equal (bits (rn8 (1+ j)) (- 66 (p)) 0) 0)))
  :hints (("Goal" :in-theory (enable rp8 rn8)
                  :use (p-vals nextrem-1 
		        (:instance bits-shift-up-2 (k 3) (x (rp j)) (i (- 63 (p))))
		        (:instance bits-shift-up-2 (k 3) (x (rn j)) (i (- 63 (p))))))))

(local-defthm nextrem-23
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (and (equal (bits (rp8 (1+ j)) (- 63 (p)) 0) 0)
	        (equal (bits (rn8 (1+ j)) (- 63 (p)) 0) 0)))
  :hints (("Goal" :use (p-vals nextrem-22
		        (:instance bits-plus-bits (x (rp8 (1+ j))) (n (- 66 (p))) (p (- 64 (p))) (m 0))
		        (:instance bits-plus-bits (x (rn8 (1+ j))) (n (- 66 (p))) (p (- 64 (p))) (m 0))))))

(local-defthm nextrem-24
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 64 (p)))
	             (mod (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p))))
			  (expt 2 (+ (p) 7))))
	          (mod (* (expt 2 (- 64 (p)))
		          (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p)))))
		       (expt 2 71))))
  :hints (("Goal" :use (p-vals nextrem-21
                        (:instance mod-prod (k (expt 2 (- 64 (p))))
			                    (m (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		                                  (bits (rn8 (1+ j)) 70 (- 64 (p)))))
				            (n (expt 2 (+ (p) 7))))))))

(local-defthm nextrem-25
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 64 (p)))
	             (mod (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p))))
			  (expt 2 (+ (p) 7))))
	          (mod (- (rp8 (1+ j)) (rn8 (1+ j)))
		       (expt 2 71))))
  :hints (("Goal" :use (p-vals nextrem-24 nextrem-23 nextrem-21
                        (:instance bits-plus-bits (x (rp8 (1+ j))) (n 70) (p (- 64 (p))) (m 0))
                        (:instance bits-plus-bits (x (rn8 (1+ j))) (n 70) (p (- 64 (p))) (m 0))))))

(local-defthm nextrem-26
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp8 (1+ j)) (rn8 (1+ j)))
		       (expt 2 71))
		  (mod (* 8 (- (rp j) (rn j)))
		       (expt 2 71))))
  :hints (("Goal" :use (p-vals nextrem-1
                        (:instance mod-sum (b (* 8 (rp j))) (a (- (mod (* 8 (rn j)) (expt 2 71)))) (n (expt 2 71)))
                        (:instance mod-diff (b (* 8 (rn j))) (a (* 8 (rp j))) (n (expt 2 71))))
                  :in-theory (enable bits rp8 rn8))))

(local-defthm nextrem-27
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (* (expt 2 67) (r j)) (expt 2 71)) (mod (- (rp j) (rn j)) (expt 2 71))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthm nextrem-28
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (* 8 (- (rp j) (rn j)))
		       (expt 2 71))
		  (mod (* (expt 2 70) (r j))
		       (expt 2 71))))
  :hints (("Goal" :use (nextrem-1 nextrem-27 int-r p-vals
                        (:instance mod-mod-times (a (- (rp j) (rn j))) (b 8) (n (expt 2 71)))
                        (:instance mod-mod-times (a (* (expt 2 67) (r j))) (b 8) (n (expt 2 71)))))))

(local-defthm nextrem-29
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (* 8 (- (rp j) (rn j)))
		       (expt 2 71))
		  (* (expt 2 (- 64 (p)))
		     (mod (* (expt 2 (+ (p) 6)) (r j))
		          (expt 2 (+ (p) 7))))))
  :hints (("Goal" :use (nextrem-28 p-vals
                        (:instance mod-prod (k (expt 2 (- 64 (p)))) (m (* (expt 2 (+ (p) 6)) (r j))) (n (expt 2 (+ (p) 7))))))))

(local-defthm nextrem-30
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 64 (p)))
	             (mod (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p))))
			  (expt 2 (+ (p) 7))))
	          (* (expt 2 (- 64 (p)))
		     (mod (* (expt 2 (+ (p) 6)) (r j))
		          (expt 2 (+ (p) 7))))))
  :hints (("Goal" :use (nextrem-29 nextrem-26 nextrem-25)
	   :in-theory (theory 'minimal-theory))))

(local-defthm hack-1
  (implies (and (rationalp x) (rationalp y)
		(equal (* (expt 2 (- 64 (p))) x)
		       (* (expt 2 (- 64 (p))) y)))
	   (equal x y))
  :rule-classes ())

(local-defthmd hack-2
  (and (rationalp (mod (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		          (bits (rn8 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7))))
       (rationalp (mod (* (expt 2 (+ (p) 6)) (r j))
		       (expt 2 (+ (p) 7))))))

(local-defthm nextrem-31
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		          (bits (rn8 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
                  (mod (* (expt 2 (+ (p) 6)) (r j))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p-vals nextrem-30 hack-2
	                (:instance hack-1 (x (mod (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		                                     (bits (rn8 (1+ j)) 70 (- 64 (p))))
		                                  (expt 2 (+ (p) 7))	))
				          (y (mod (* (expt 2 (+ (p) 6)) (r j))
	                                          (expt 2 (+ (p) 7)))))))))

(local-defthm nextrem-32
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (lognot (sum71 (1+ j)))
	          (logxor (logxor (lognot (rn8 (1+ j)))
		                  (rp8 (1+ j)))
		          (divmult71 (1+ j)))))
  :hints (("Goal" :in-theory (enable lognot-logxor sum71))))

(local-defthm integerp-divmult71
  (implies (not (earlyp))
           (integerp (divmult71 j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable bvecp divmult71) :use (bvecp-div))))

(local-defthm nextrem-33
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))
	          (logxor (logxor (bits (lognot (rn8 (1+ j))) 70 (- 64 (p)))
		                  (bits (rp8 (1+ j)) 70 (- 64 (p))))
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))))
  :hints (("Goal" :use (p-vals nextrem-32)
                  :in-theory (enable bits-logxor))))

(local-defthm integerp-carry71
  (implies (not (earlyp))
           (integerp (carry71 j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable bvecp carry71))))

(local-defthm nextrem-34
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry71 (1+ j)) 70 (- 64 (p)))
                  (logior (logand (bits (lognot (rn8 (1+ j))) 70 (- 64 (p))) (bits (rp8 (1+ j)) 70 (- 64 (p))))
                          (logand (logior (bits (lognot (rn8 (1+ j))) 70 (- 64 (p))) (bits (rp8 (1+ j)) 70 (- 64 (p))))
                                  (bits (divmult71 (1+ j)) 70 (- 64 (p)))))))
  :hints (("Goal" :use (p-vals nextrem-32 nextrem-1)
                  :in-theory (enable carry71 bits-logior bits-logand))))

(local-defthm nextrem-35
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))
	          (logxor (bits (rp8 (1+ j)) 70 (- 64 (p)))
		          (logxor (bits (lognot (rn8 (1+ j))) 70 (- 64 (p)))
			          (bits (divmult71 (1+ j)) 70 (- 64 (p)))))))
  :hints (("Goal" :use (p-vals nextrem-33))))

(local-defthm nextrem-36
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry71 (1+ j)) 70 (- 64 (p)))
	          (logior (logand (bits (rp8 (1+ j)) 70 (- 64 (p))) (bits (lognot (rn8 (1+ j))) 70 (- 64 (p))))
                          (logior (logand (bits (rp8 (1+ j)) 70 (- 64 (p))) (bits (divmult71 (1+ j)) 70 (- 64 (p))))
			          (logand (bits (lognot (rn8 (1+ j))) 70 (- 64 (p))) (bits (divmult71 (1+ j)) 70 (- 64 (p))))))))
  :hints (("Goal" :use (p-vals nextrem-34
                        (:instance logand-logior (x (bits (divmult71 (1+ j)) 70 (- 64 (p))))
			                         (y (bits (lognot (rn8 (1+ j))) 70 (- 64 (p))))
						 (z (bits (rp8 (1+ j)) 70 (- 64 (p))))))))) 

(local-defthm nextrem-37
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))
	             (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))))
		  (+ (bits (rp8 (1+ j)) 70 (- 64 (p)))
		     (bits (lognot (rn8 (1+ j))) 70 (- 64 (p)))
		     (bits (divmult71 (1+ j)) 70 (- 64 (p))))))
  :hints (("Goal" :use (p-vals nextrem-35 nextrem-36
                        (:instance add-3 (x (bits (rp8 (1+ j)) 70 (- 64 (p))))
			                 (y (bits (lognot (rn8 (1+ j))) 70 (- 64 (p))))
			                 (z (bits (divmult71 (1+ j)) 70 (- 64 (p)))))))))

(local-defthm nextrem-38
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (bits (rp8 (1+ j)) 70 (- 64 (p)))
		          (bits (lognot (rn8 (1+ j))) 70 (- 64 (p)))
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p))))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals) :in-theory (enable bits-lognot))))

(local-defthm nextrem-39
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))
  	                  (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p))))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (nextrem-38 nextrem-37) :in-theory (theory 'minimal-theory))))

(local-defthm nextrem-40
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		             (bits (rn8 (1+ j)) 70 (- 64 (p))))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (disable ACL2::MOD-CANCEL-*-REWRITING-GOAL-LITERAL ACL2::MOD-SUMS-CANCEL-1)
                  :use (nextrem-31 p-vals
                        (:instance mod-sum (a (1- (bits (divmult71 (1+ j)) 70 (- 64 (p)))))
			                   (b (- (bits (rp8 (1+ j)) 70 (- 64 (p)))
		                                 (bits (rn8 (1+ j)) 70 (- 64 (p)))))
				           (n (expt 2 (+ (p) 7))))
                        (:instance mod-sum (a (1- (bits (divmult71 (1+ j)) 70 (- 64 (p)))))
			                   (b (* (expt 2 (+ (p) 6)) (r j)))
				           (n (expt 2 (+ (p) 7))))))))

(local-defun pos (j) (if (> (q (1+ j)) 0) 1 0))

(local-defthm rat-r
  (implies (not (zp j))
           (rationalp (r j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable r))))

(local-defthm nextrem-41
  (implies (and (not (earlyp))
                (not (zp j))
		(< (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals
                        (:instance q-vals (j (1+ j)))
                        (:instance nextrem-20 (j (1+ j)))))))

(local-defthm nextrem-42
  (implies (and (not (earlyp))
                (not (zp (1+ j)))
		(> (1+ j) 1)
		(> (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
			  (- (expt 2 (+ (p) 7)) (1+ (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals
                        (:instance q-vals (j (1+ j)))
                        (:instance nextrem-20 (j (1+ j))))
	          :in-theory (theory 'minimal-theory))))	          

(local-defthm nextrem-43
  (implies (and (not (earlyp))
                (not (zp j))
		(> (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (expt 2 (+ (p) 7))
			  (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (enable pos)
                  :use (p-vals nextrem-42
                        (:instance q-vals (j (1+ j)))))))

(local-defthm nextrem-44
  (implies (and (not (earlyp))
                (not (zp j))
		(> (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
			  (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (enable pos)
                  :use (p-vals nextrem-43
		        (:instance mod-mult (a 1)
			                    (n (expt 2 (+ (p) 7)))
					    (m (+ (* (expt 2 (+ (p) 6)) (r j))
			                          -1
			                          (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			                          (- (pos j)))))
                        (:instance q-vals (j (1+ j)))))))

(local-defthm nextrem-45
  (implies (and (not (earlyp))
                (not (zp j))
		(not (= (q (1+ j)) 0))
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
			  (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p-vals nextrem-41 nextrem-44))))

(local-defthm nextrem-46
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (+ (* (expt 2 (+ (p) 6)) (r j))
		     -1
		     (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
		     (- (pos j)))
	          (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
	             -1
		     (- (pos j)))))
  :hints (("Goal" :in-theory (enable r-recurrence pos)
                  :use (p-vals (:instance q-vals (j (1+ j)))))))

(local-defthm nextrem-47
  (implies (and (not (earlyp))
		(not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 6)) (r j))
			  -1
		          (bits (divmult71 (1+ j)) 70 (- 64 (p))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
			  -1
			  (- (pos j)))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (nextrem-45 nextrem-46))))

(local-defthm nextrem-48
  (implies (and (not (earlyp))
		(not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))
  	                  (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))))
		       (expt 2 (+ (p) 7)))
		  (mod (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
			  -1
			  (- (pos j)))
		       (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (nextrem-39 nextrem-40 nextrem-47))))

(local-defthm nextrem-49
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry71 (1+ j)) 69 (- 64 (p)))
	          (bits (bits (carry71 (1+ j)) 70 (- 64 (p))) (+ (p) 5) 0)))
  :hints (("Goal" :use (p-vals)
		  :in-theory (enable bits-bits carry71))))

(local-defthmd nextrem-50
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry71 (1+ j)) 69 (- 64 (p)))
	          (mod (bits (carry71 (1+ j)) 70 (- 64 (p))) (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-49)
		  :in-theory (e/d (bits) (bits-bits)))))

(local-defthmd nextrem-51
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) 70 (- 65 (p)))
	          (mod (bits (carry71 (1+ j)) 70 (- 64 (p))) (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable p rp* nextrem-lemma)
                  :use (nextrem-50))))

(local-defthmd nextrem-52
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (bitn (rp (1+ j)) (- 64 (p)))
	          (pos j)))
  :hints (("Goal" :in-theory (enable p remsign rp* nextrem-lemma pos) 
                  :use ((:instance q-sign (j (1+ j))) (:instance q-vals (j (1+ j)))))))

(local-defthmd nextrem-53
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) 70 (- 64 (p)))
	          (+ (* 2 (mod (bits (carry71 (1+ j)) 70 (- 64 (p))) (expt 2 (+ (p) 6))))
		     (pos j))))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma p) 
                  :use (nextrem-51 nextrem-52
		        (:instance bits-plus-bitn (x (rp (1+ j))) (n 70) (m (- 64 (p))))))))

(local-defthmd nextrem-54
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) 70 (- 64 (p)))
	          (+ (mod (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))) (expt 2 (+ (p) 7)))
		     (pos j))))
  :hints (("Goal" :use (p-vals nextrem-53
                        (:instance mod-prod (k 2) (m (bits (carry71 (1+ j)) 70 (- 64 (p)))) (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-55
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (bits (rn (1+ j)) 70 (- 64 (p)))
	          (bits (sum71 (1+ j)) 70 (- 64 (p))))) 
  :hints (("Goal" :in-theory (enable rn* nextrem-lemma p))))

(local-in-theory (disable nextrem-32))

(local-defthmd nextrem-56
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (sum71 (1+ j)) 70 (- 64 (p)))) (expt 2 (+ (p) 7)))
	          (mod (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))) (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals) :in-theory (e/d (bits-lognot) (ACL2::|(mod (- x) y)| acl2::mod-zero)))))

(local-defthmd nextrem-57
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rn (1+ j)) 70 (- 64 (p)))) (expt 2 (+ (p) 7)))
	          (mod (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))) (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (nextrem-55 nextrem-56))))
                  
(local-defthmd nextrem-58
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) (- 63 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rp* rp8 nextrem-lemma p)
                  :use (nextrem-1
		        (:instance bits-shift-up-2 (k 3) (x (rp j)) (i (- 60 (p))))
			(:instance bits-plus-bits (x (rp j)) (n (- 63 (p))) (p (- 61 (p))) (m 0))))))

(local-defthmd nextrem-59
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (bvecp (rp (1+ j)) 71))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma p))))

(local-defthmd nextrem-60
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (bits (rn (1+ j)) (- 63 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rn* rn8 nextrem-lemma p)
                  :use (nextrem-1
		        (:instance bits-shift-up-2 (k 3) (x (rn j)) (i (- 60 (p))))
			(:instance bits-plus-bits (x (rn j)) (n (- 63 (p))) (p (- 61 (p))) (m 0))))))

(local-defthmd nextrem-61
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (bvecp (rn (1+ j)) 71))
  :hints (("Goal" :in-theory (enable divsigned div3signed div3 rn* sum71 divmult71 rp8 rn8 nextrem-lemma p)
                  :use (bvecp-div
		        ;(:instance bvecp-monotone (x (div)) (n 57) (m 59))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextrem-62
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 71))
		  (mod (* (expt 2 (- 64 (p)))
		          (- (bits (rp (1+ j)) 70 (- 64 (p)))
			     (bits (rn (1+ j)) 70 (- 64 (p)))))
	               (expt 2 71))))		
  :hints (("Goal" :use (p-vals nextrem-61 nextrem-60 nextrem-59 nextrem-58
                        (:instance bits-plus-bits (x (rp (1+ j))) (n 70) (p (- 64 (p))) (m 0))
			(:instance bits-plus-bits (x (rn (1+ j))) (n 70) (p (- 64 (p))) (m 0))))))

(local-defthmd nextrem-63
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 71))
		  (* (expt 2 (- 64 (p)))
		     (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			     (bits (rn (1+ j)) 70 (- 64 (p))))
	                  (expt 2 (+ (p) 7))))))
  :hints (("Goal" :use (p-vals nextrem-62
                        (:instance mod-prod (k (expt 2 (- 64 (p))))
			                    (m (- (bits (rp (1+ j)) 70 (- 64 (p))) (bits (rn (1+ j)) 70 (- 64 (p)))))
					    (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-64
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (bits (rp (1+ j)) 70 (- 64 (p)))
		          (mod (- (bits (rn (1+ j)) 70 (- 64 (p)))) (expt 2 (+ (p) 7))))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals
                        (:instance mod-sum (b (- (bits (rn (1+ j)) 70 (- 64 (p)))))
			                   (a (bits (rp (1+ j)) 70 (- 64 (p))))
					   (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-65
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (bits (rp (1+ j)) 70 (- 64 (p)))
		          (mod (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))) (expt 2 (+ (p) 7))))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals nextrem-64 nextrem-57)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-66
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (bits (rp (1+ j)) 70 (- 64 (p)))
		          (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals nextrem-65
                        (:instance mod-sum (a (bits (rp (1+ j)) 70 (- 64 (p))))
			                   (b (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))))
					   (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-67
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (+ (mod (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))) (expt 2 (+ (p) 7)))
		             (pos j))
		          (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals nextrem-66 nextrem-54)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-68
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p))))
		          (pos j)
		          (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals nextrem-67
                        (:instance mod-sum (a (+ (pos j) (1+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p))))))
			                   (b (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))))
					   (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-69
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (mod (+ (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))
  	                          (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p)))))
		               (expt 2 (+ (p) 7)))
		          1 (pos j))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals nextrem-68
                        (:instance mod-sum (a (1+ (pos j)))
			                   (b (+ (* 2 (bits (carry71 (1+ j)) 70 (- 64 (p))))
		                                 (bits (lognot (sum71 (1+ j))) 70 (- 64 (p)))))
					   (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-70
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (+ (mod (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
			          -1
			          (- (pos j)))
			       (expt 2 (+ (p) 7)))
		          1 (pos j))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :use (p-vals nextrem-48 nextrem-69)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-71
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 70 (- 64 (p)))
			  (bits (rn (1+ j)) 70 (- 64 (p))))
	               (expt 2 (+ (p) 7)))
		  (mod (* (expt 2 (+ (p) 3)) (r (1+ j)))
	               (expt 2 (+ (p) 7)))))
  :hints (("Goal" :in-theory (disable ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-< ACL2::MOD-CANCEL-*-REWRITING-GOAL-LITERAL ACL2::MOD-SUMS-CANCEL-1)
                  :use (p-vals nextrem-70
                        (:instance mod-sum (a (1+ (pos j)))
			                   (b (+ (* (expt 2 (+ (p) 3)) (r (1+ j))) -1 (- (pos j))))
					   (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-72
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 71))
		  (* (expt 2 (- 64 (p)))
		     (mod (* (expt 2 (+ (p) 3)) (r (1+ j)))
	                  (expt 2 (+ (p) 7))))))
  :hints (("Goal" :use (p-vals nextrem-63 nextrem-71)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-73
  (implies (and (not (earlyp))
                (not (= (q (1+ j)) 0))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 71))
                  (mod (* (expt 2 67) (r (1+ j)))
	               (expt 2 71))))
  :hints (("Goal" :use (p-vals nextrem-72 nextrem-59 nextrem-61
                        (:instance mod-prod (k (expt 2 (- 64 (p))))
			                    (m (* (expt 2 (+ (p) 3)) (r (1+ j))))
					    (n (expt 2 (+ (p) 7))))))))

(local-defthmd nextrem-74
  (implies (and (not (earlyp))
                (= (q (1+ j)) 0)
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 71))
                  (mod (* (expt 2 67) (r (1+ j)))
	               (expt 2 71))))
  :hints (("Goal" :use (p-vals nextrem-26 nextrem-28)
                  :in-theory (enable r-recurrence rp* rn* nextrem-lemma))))

(local-defthmd nextrem-75
  (implies (and (not (earlyp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 71))
                  (mod (* (expt 2 67) (r (1+ j)))
	               (expt 2 71))))
  :hints (("Goal" :use (p-vals nextrem-73 nextrem-74))))

(local-defund hyp3 (j)
  (and (hyp j)
       (or (< j 2)
           (hyp (- j 1)))
       (or (< j 3)
           (hyp (- j 2)))))

(local-in-theory (disable (hyp3)))

(local-defthmd hyp3-1
  (implies (not (earlyp))
           (hyp3 1))
  :hints (("Goal" :in-theory (enable hyp3) :use (hyp-1))))

(local-defthmd hyp3-2
  (implies (and (not (earlyp))
                (not (zp j))
		(< j (n))
		(or (< j 3) (hyp (- j 2)))
		(hyp j))
	   (hyp (1+ j)))
  :hints (("Goal" :expand ((hyp 2) (hyp (+ 1 j)))
                  :use (p-vals approx-error r-bound-induct nextrem-59 nextrem-61 nextrem-75 nextrem-58 nextrem-60
		        (:instance q-maxk (j (1+ j)))))))

(local-defthmd hyp3-3
  (implies (and (not (earlyp))
                (not (zp j))
		(< j (n))
		(hyp3 j))
	   (hyp3 (1+ j)))
  :hints (("Goal" :in-theory (enable hyp3)
                  :use (hyp-1 hyp3-2))))

(local-defthmd induct-step
  (implies (and (not (earlyp))
                (not (zp j))
		(not (= j 1))
		(<= j (n))
		(hyp3 (1- j)))
	   (hyp3 j))
  :hints (("Goal" :use ((:instance hyp3-3 (j (1- j)))))))

(local-in-theory (enable quotient))

(local-defthmd main-induction
  (implies (and (not (earlyp))
                (not (zp j))
		(<= j (n)))
           (hyp3 j))
  :hints (("Goal" :induct (quotient j))  
          ("Subgoal *1/2" :use (hyp3-1))
          ("Subgoal *1/1" :use (hyp3-1 induct-step))))

(defthmd induction-result
  (implies (and (not (earlyp))
                (not (zp j))
		(<= j (n)))
           (and (= (q j) (maxk (approx (1- j))))
                (< (abs (- (approx (1- j)) (* 8 (r (1- j))))) 1/64)
                (<= (abs (r j)) (* 4/7 (d)))
                (bvecp (rp j) 71)
                (bvecp (rn j) 71)
                (= (mod (* (expt 2 67) (r j)) (expt 2 71)) (mod (- (rp j) (rn j)) (expt 2 71)))
                (= (bits (rp j) (- 63 (p)) 0) 0)
                (= (bits (rn j) (- 63 (p)) 0) 0)))
  :hints (("Goal" :use (main-induction)
                  :in-theory '(hyp3 hyp))))

(defund qf () (quotient (n)))

(defund rf () (r (n)))

(in-theory (disable (qf) (rf)))

(defthmd rf-bound
  (implies (not (earlyp))
           (<= (abs (rf)) (* 4/7 (d))))
  :hints (("Goal" :in-theory (enable rf) :use ((:instance induction-result (j (n)))))))

(defthmd rf-rpf-rnf
  (implies (not (earlyp))
           (equal (mod (* (expt 2 67) (rf)) (expt 2 71))
   	          (mod (- (rpf) (rnf)) (expt 2 71))))
  :hints (("Goal" :in-theory (enable rf rpf-rewrite rnf-rewrite)
	          :use ((:instance induction-result (j (n)))))))

(defthmd bvecp-rpf-rnf
  (implies (not (earlyp))
           (and (bvecp (rpf) 71)
	        (bvecp (rnf) 71)))
  :hints (("Goal" :in-theory (enable rpf-rewrite rnf-rewrite)
	          :use ((:instance induction-result (j (n)))))))
