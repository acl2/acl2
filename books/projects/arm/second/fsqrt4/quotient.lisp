(in-package "RTL")

(include-book "induct")

(local-in-theory (enable lsbis2 n p f dp sp hp prec))

(in-theory (disable rootpf-rewrite rootm1pf-rewrite))

(local-defthmd bvecp-roots
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (n)))
           (and (bvecp (root j) 55)
	        (bvecp (rootm1 j) 55)))
  :hints (("Goal" :use (fnum-vals inv-lemma)
		  :in-theory (enable inv root-inv))))

(local-defthmd roots-rewrite
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (n)))
	   (and (equal (root j) (* (expt 2 54) (quot j)))
                (equal (rootm1 j) (- (root j) (expt 2 (- 54 (* 2 j)))))))
  :hints (("Goal" :use (fnum-vals inv-lemma)
                  :in-theory (enable inv root-inv))))

(local-defthm roots-low
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (n))
                (natp k)
		(<= k (- 53 (* 2 j))))
           (and (equal (bits (root j) k 0) 0)
	        (equal (bits (rootm1 j) k 0) 0)))
  :hints (("Goal" :use (fnum-vals inv-lemma
                        (:instance bits-bits (x (rootm1 j)) (i (- 53 (* 2 j))) (j 0) (l 0))
                        (:instance bits-bits (x (root j)) (i (- 53 (* 2 j))) (j 0) (l 0)))
		  :in-theory (e/d (inv root-inv) (bits-bits)))))

(local-defthmd roots-high-1
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (n))
                (natp k)
		(<= k (- 54 (* 2 j))))
           (and (equal (* (expt 2 k) (bits (root j) 54 k)) (root j))
	        (equal (* (expt 2 k) (bits (rootm1 j) 54 k)) (rootm1 j))))
  :hints (("Goal" :use (bvecp-roots
		        (:instance roots-low (k (1- k)))
                        (:instance bits-plus-bits (x (rootm1 j)) (n 54) (p k) (m 0))
                        (:instance bits-plus-bits (x (root j)) (n 54) (p k) (m 0)))
		  :in-theory (e/d (bvecp inv root-inv) (ACL2::PREFER-POSITIVE-ADDENDS-< roots-low)))))

(local-defthmd roots-high
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (n))
                (natp k)
		(<= k (- 54 (* 2 j))))
           (and (equal (bits (root j) 54 k) (* (expt 2 (- k)) (root j)))
	        (equal (bits (rootm1 j) 54 k) (* (expt 2 (- k)) (rootm1 j)))))
  :hints (("Goal" :use (roots-high-1
                        (:instance bvecp-member (x k) (n 6))))))

(local-defthmd bvecp-rootpf
  (implies (not (specialp))
           (and (bvecp (rootpf) 55)
	        (bvecp (rootm1pf) 55)))
  :hints (("Goal" :in-theory (enable rootpf-rewrite rootm1pf-rewrite incroot))))

(local-defthmd rootpf-sp-1
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (bits (root (- (n) 2)) 54 (- 58 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable bvecp rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp-2
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 58)) (root (- (n) 2)))))
  :hints (("Goal" :in-theory (enable roots-high) :use (rootpf-sp-1))))

(local-defthmd rootpf-sp-3
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) (- 57 (* 2 (n))) (- 56 (* 2 (n))))
	          (1+ (q (1- (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp-4
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (q (n))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))))))

(local-defthmd rootpf-sp-5
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-sp-6
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (rootpf)
	          (+ (root (- (n) 2))
		     (* (expt 2 (- 56 (* 2 (n))))
		        (1+ (q (1- (n)))))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (q (n))))))
  :hints (("Goal" :use (bvecp-rootpf rootpf-sp-2 rootpf-sp-3 rootpf-sp-4 rootpf-sp-5
		        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 58 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 57 (* 2 (n)))) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(defund inc ()
  (if (= (fnum) 1)
      (expt 2 (- 56 (* 2 (n))))
    (expt 2 (- 55 (* 2 (n))))))

(local-in-theory (disable (inc)))

(local-defthmd rootpf-sp-7
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(>= (q (1- (n))) -1))
           (equal (rootpf)
	          (+ (root (n)) (inc))))
  :hints (("Goal" :in-theory (enable rootpf-sp-6 roots-rewrite quot inc))))

(local-defthmd rootpf-sp-8
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (bits (rootm1 (- (n) 2)) 54 (- 58 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable bvecp rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp-9
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 58)) (rootm1 (- (n) 2)))))
  :hints (("Goal" :in-theory (enable roots-high) :use (rootpf-sp-8))))

(local-defthmd rootpf-sp-10
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) (- 57 (* 2 (n))) (- 56 (* 2 (n))))
	          (+ 5 (q (1- (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp-11
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (q (n))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))))))

(local-defthmd rootpf-sp-12
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-sp-13
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0)
		(< (q (1- (n))) -1))
           (equal (rootpf)
	          (+ (rootm1 (- (n) 2))
		     (* (expt 2 (- 56 (* 2 (n))))
		        (+ 5 (q (1- (n)))))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (q (n))))))
  :hints (("Goal" :use (bvecp-rootpf rootpf-sp-9 rootpf-sp-10 rootpf-sp-11 rootpf-sp-12
		        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 58 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 57 (* 2 (n)))) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp-14
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 0))
           (equal (rootpf)
	          (+ (root (n)) (inc))))
  :hints (("Goal" :use (rootpf-sp-7) :in-theory (enable rootpf-sp-13 roots-rewrite quot inc))))

(local-defthmd rootpf-sp-15
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 0))
           (equal (bits (rootpf) 54 (- 56 (* 2 (n))))
	          (bits (root (1- (n))) 54 (- 56 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable bvecp rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp-16
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 0))
           (equal (bits (rootpf) 54 (- 56 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 56)) (root (1- (n))))))
  :hints (("Goal" :in-theory (enable roots-high) :use (rootpf-sp-15))))

(local-defthmd rootpf-sp-17
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 0))
           (equal (bits (rootpf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (+ 4 (q (n)))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))))))

(local-defthmd rootpf-sp-18
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 0))
           (equal (bits (rootpf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-sp-19
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 0))
           (equal (rootpf)
	          (+ (root (1- (n)))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (+ 4 (q (n)))))))
  :hints (("Goal" :use (bvecp-rootpf rootpf-sp-16 rootpf-sp-17 rootpf-sp-18
		        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-sp
  (implies (and (not (specialp))
                (= (lsbis2) 1))
           (equal (rootpf)
	          (+ (root (n)) (inc))))
  :hints (("Goal" :use (rootpf-sp-14) :in-theory (enable rootpf-sp-19 roots-rewrite quot inc))))

(local-defthmd rootm1pf-sp-1
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (bits (rootm1pf) 54 (- 58 (* 2 (n))))
	          (bits (root (- (n) 2)) 54 (- 58 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable bvecp rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-2
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (bits (rootm1pf) 54 (- 58 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 58)) (root (- (n) 2)))))
  :hints (("Goal" :in-theory (enable roots-high) :use (rootm1pf-sp-1))))

(local-defthmd rootm1pf-sp-3
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (bits (rootm1pf) (- 57 (* 2 (n))) (- 56 (* 2 (n))))
	          (1+ (q (1- (n))))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-4
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (bits (rootm1pf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (1- (q (n)))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))))))

(local-defthmd rootm1pf-sp-5
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-sp-6
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (rootm1pf)
	          (+ (root (- (n) 2))
		     (* (expt 2 (- 56 (* 2 (n))))
		        (1+ (q (1- (n)))))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (1- (q (n)))))))
  :hints (("Goal" :use (bvecp-rootpf rootm1pf-sp-2 rootm1pf-sp-3 rootm1pf-sp-4 rootm1pf-sp-5
		        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 58 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 57 (* 2 (n)))) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-7
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(>= (q (1- (n))) -1))
           (equal (rootm1pf)
	          (+ (rootm1 (n)) (inc))))
  :hints (("Goal" :in-theory (enable rootm1pf-sp-6 roots-rewrite quot inc))))

(local-defthmd rootm1pf-sp-8
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(< (q (1- (n))) -1))
           (equal (bits (rootm1pf) 54 (- 58 (* 2 (n))))
	          (bits (rootm1 (- (n) 2)) 54 (- 58 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable bvecp rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-9
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(< (q (1- (n))) -1))
           (equal (bits (rootm1pf) 54 (- 58 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 58)) (rootm1 (- (n) 2)))))
  :hints (("Goal" :in-theory (enable roots-high) :use (rootm1pf-sp-8))))

(local-defthmd rootm1pf-sp-10
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(< (q (1- (n))) -1))
           (equal (bits (rootm1pf) (- 57 (* 2 (n))) (- 56 (* 2 (n))))
	          (+ 5 (q (1- (n))))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-11
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(< (q (1- (n))) -1))
           (equal (bits (rootm1pf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (1- (q (n)))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))))))

(local-defthmd rootm1pf-sp-12
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(< (q (1- (n))) -1))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-sp-13
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1)
		(< (q (1- (n))) -1))
           (equal (rootm1pf)
	          (+ (rootm1 (- (n) 2))
		     (* (expt 2 (- 56 (* 2 (n))))
		        (+ 5 (q (1- (n)))))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (1- (q (n)))))))
  :hints (("Goal" :use (bvecp-rootpf rootm1pf-sp-9 rootm1pf-sp-10 rootm1pf-sp-11 rootm1pf-sp-12
		        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 58 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 57 (* 2 (n)))) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-14
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(>= (q (n)) 1))
           (equal (rootm1pf)
	          (+ (rootm1 (n)) (inc))))
  :hints (("Goal" :use (rootm1pf-sp-7) :in-theory (enable rootm1pf-sp-13 roots-rewrite quot inc))))

(local-defthmd rootm1pf-sp-15
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 1))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (bits (root (1- (n))) 54 (- 56 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable bvecp rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp-16
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 1))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 56)) (root (1- (n))))))
  :hints (("Goal" :in-theory (enable roots-high) :use (rootm1pf-sp-15))))

(local-defthmd rootm1pf-sp-17
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 1))
           (equal (bits (rootm1pf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (+ 3 (q (n)))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot)
                  :use ((:instance q-vals (j (n)))))))

(local-defthmd rootm1pf-sp-18
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 1))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-sp-19
  (implies (and (not (specialp))
                (= (lsbis2) 1)
		(< (q (n)) 1))
           (equal (rootm1pf)
	          (+ (root (1- (n)))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (+ 3 (q (n)))))))
  :hints (("Goal" :use (bvecp-rootpf rootm1pf-sp-16 rootm1pf-sp-17 rootm1pf-sp-18
		        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (n)))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootm1pf-sp
  (implies (and (not (specialp))
                (= (lsbis2) 1))
           (equal (rootm1pf)
	          (+ (rootm1 (n)) (inc))))
  :hints (("Goal" :use (rootm1pf-sp-14) :in-theory (enable rootm1pf-sp-19 roots-rewrite quot inc))))

(local-defthmd rootpf-dp-hp-qn=2-1
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (bits (root (- (n) 2)) 54 (- 58 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-dp-hp-qn=2-2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 58)) (root (- (n) 2)))))
  :hints (("Goal" :in-theory (enable roots-high) :use (fnum-vals rootpf-dp-hp-qn=2-1))))

(local-defthmd rootpf-dp-hp-qn=2-3
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) (- 57 (* 2 (n))) (- 56 (* 2 (n))))
	          (1+ (q (1- (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use (fnum-vals (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-dp-hp-qn=2-4
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(>= (q (1- (n))) -1))
           (equal (bits (rootpf) (- 55 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-dp-hp-qn=2-5
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(>= (q (1- (n))) -1))
           (equal (rootpf)
	          (+ (root (- (n) 2))
		     (* (expt 2 (- 56 (* 2 (n))))
		        (1+ (q (1- (n))))))))
  :hints (("Goal" :use (fnum-vals bvecp-rootpf rootpf-dp-hp-qn=2-2 rootpf-dp-hp-qn=2-3 rootpf-dp-hp-qn=2-4
		        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 58 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 57 (* 2 (n)))) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-dp-hp-qn=2-7
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(>= (q (1- (n))) -1))
           (equal (rootpf)
	          (+ (root (n)) (inc))))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable rootpf-dp-hp-qn=2-5 roots-rewrite quot inc))))

(local-defthmd rootpf-dp-hp-qn=2-8
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (bits (rootm1 (- (n) 2)) 54 (- 58 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use ((:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-dp-hp-qn=2-9
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) 54 (- 58 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 58)) (rootm1 (- (n) 2)))))
  :hints (("Goal" :in-theory (enable roots-high) :use (fnum-vals rootpf-dp-hp-qn=2-8))))

(local-defthmd rootpf-dp-hp-qn=2-10
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) (- 57 (* 2 (n))) (- 56 (* 2 (n))))
	          (+ 5 (q (1- (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot)
                  :use (fnum-vals (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-dp-hp-qn=2-11
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(< (q (1- (n))) -1))
           (equal (bits (rootpf) (- 55 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-dp-hp-qn=2-12
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2)
		(< (q (1- (n))) -1))
           (equal (rootpf)
	          (+ (rootm1 (- (n) 2))
		     (* (expt 2 (- 56 (* 2 (n))))
		        (+ 5 (q (1- (n))))))))
  :hints (("Goal" :use (fnum-vals bvecp-rootpf rootpf-dp-hp-qn=2-9 rootpf-dp-hp-qn=2-10 rootpf-dp-hp-qn=2-11
		        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 58 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 57 (* 2 (n)))) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance q-vals (j (1- (n))))))))

(local-defthmd rootpf-dp-hp-qn=2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (rootpf)
	          (+ (root (n)) (inc))))
  :hints (("Goal" :use (fnum-vals rootpf-dp-hp-qn=2-7)
                  :in-theory (enable rootpf-dp-hp-qn=2-12 roots-rewrite quot inc))))

(local-defthmd rootm1pf-dp-hp-qn=2-1
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (bits (root (1- (n))) 54 (- 56 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn=2-2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 56)) (root (1- (n))))))
  :hints (("Goal" :in-theory (enable roots-high) :use (fnum-vals rootm1pf-dp-hp-qn=2-1))))

(local-defthmd rootm1pf-dp-hp-qn=2-3
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (bits (rootm1pf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          3))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn=2-4
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn=2-5
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (rootm1pf)
	          (+ (root (1- (n)))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (1+ (q (n)))))))
  :hints (("Goal" :use (fnum-vals bvecp-rootpf rootm1pf-dp-hp-qn=2-2 rootm1pf-dp-hp-qn=2-3 rootm1pf-dp-hp-qn=2-4
		        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))))))

(local-defthmd rootm1pf-dp-hp-qn=2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(= (q (n)) 2))
           (equal (rootm1pf)
	          (+ (rootm1 (n)) (inc))))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable rootm1pf-dp-hp-qn=2-5 roots-rewrite quot inc))))

(local-defthmd rootpf-dp-hp-qn<2-1
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2))
           (equal (bits (rootpf) 54 (- 56 (* 2 (n))))
	          (bits (root (1- (n))) 54 (- 56 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-dp-hp-qn<2-2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2))
           (equal (bits (rootpf) 54 (- 56 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 56)) (root (1- (n))))))
  :hints (("Goal" :in-theory (enable roots-high) :use (fnum-vals rootpf-dp-hp-qn<2-1))))

(local-defthmd rootpf-dp-hp-qn<2-3
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2))
           (equal (bits (rootpf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (+ 2 (q (n)))))
  :hints (("Goal" :use (fnum-vals (:instance q-vals (j (n))))
                  :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-dp-hp-qn<2-4
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2))
           (equal (bits (rootpf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootpf-rewrite incroot))))

(local-defthmd rootpf-dp-hp-qn<2-5
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2))
           (equal (rootpf)
	          (+ (root (1- (n)))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (+ 2 (q (n)))))))
  :hints (("Goal" :use (fnum-vals bvecp-rootpf rootpf-dp-hp-qn<2-2 rootpf-dp-hp-qn<2-3 rootpf-dp-hp-qn<2-4
		        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootpf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))))))

(defthmd rootpf-lemma
  (implies (not (specialp))
           (equal (rootpf)
	          (+ (root (n)) (inc))))
  :hints (("Goal" :use (fnum-vals rootpf-sp rootpf-dp-hp-qn=2 (:instance q-vals (j (n))))
                  :in-theory (enable rootpf-dp-hp-qn<2-5 roots-rewrite quot inc))))

(local-defthmd rootm1pf-dp-hp-qn<2-1
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(>= (q (n)) -1))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (bits (root (1- (n))) 54 (- 56 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn<2-2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(>= (q (n)) -1))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 56)) (root (1- (n))))))
  :hints (("Goal" :in-theory (enable roots-high) :use (fnum-vals rootm1pf-dp-hp-qn<2-1))))

(local-defthmd rootm1pf-dp-hp-qn<2-3
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(>= (q (n)) -1))
           (equal (bits (rootm1pf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (1+ (q (n)))))
  :hints (("Goal" :use (fnum-vals (:instance q-vals (j (n))))
                  :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn<2-4
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(>= (q (n)) -1))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn<2-5
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(>= (q (n)) -1))
           (equal (rootm1pf)
	          (+ (root (1- (n)))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (1+ (q (n)))))))
  :hints (("Goal" :use (fnum-vals bvecp-rootpf rootm1pf-dp-hp-qn<2-2 rootm1pf-dp-hp-qn<2-3 rootm1pf-dp-hp-qn<2-4
		        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))))))

(local-defthmd rootm1pf-dp-hp-qn<2-6
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(>= (q (n)) -1))
           (equal (rootm1pf)
	          (+ (rootm1 (n)) (inc))))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable rootm1pf-dp-hp-qn<2-5 roots-rewrite quot inc))))

(local-defthmd rootm1pf-dp-hp-qn<2-7
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(< (q (n)) -1))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (bits (rootm1 (1- (n))) 54 (- 56 (* 2 (n))))))
  :hints (("Goal" :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn<2-8
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(< (q (n)) -1))
           (equal (bits (rootm1pf) 54 (- 56 (* 2 (n))))
	          (* (expt 2 (- (* 2 (n)) 56)) (rootm1 (1- (n))))))
  :hints (("Goal" :in-theory (enable roots-high) :use (fnum-vals rootm1pf-dp-hp-qn<2-7))))

(local-defthmd rootm1pf-dp-hp-qn<2-9
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(< (q (n)) -1))
           (equal (bits (rootm1pf) (- 55 (* 2 (n))) (- 54 (* 2 (n))))
	          (+ 5 (q (n)))))
  :hints (("Goal" :use (fnum-vals (:instance q-vals (j (n))))
                  :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn<2-10
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(< (q (n)) -1))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootm1pf-rewrite incroot))))

(local-defthmd rootm1pf-dp-hp-qn<2-11
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (n)) 2)
		(< (q (n)) -1))
           (equal (rootm1pf)
	          (+ (rootm1 (1- (n)))
		     (* (expt 2 (- 54 (* 2 (n))))
		        (+ 5 (q (n)))))))
  :hints (("Goal" :use (fnum-vals bvecp-rootpf rootm1pf-dp-hp-qn<2-8 rootm1pf-dp-hp-qn<2-9 rootm1pf-dp-hp-qn<2-10
		        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 56 (* 2 (n)))) (m 0))
		        (:instance bits-plus-bits (x (rootm1pf)) (n (- 55 (* 2 (n)))) (p (- 54 (* 2 (n)))) (m 0))))))

(defthmd rootm1pf-lemma
  (implies (not (specialp))
           (equal (rootm1pf)
	          (+ (rootm1 (n)) (inc))))
  :hints (("Goal" :use (fnum-vals rootm1pf-sp rootm1pf-dp-hp-qn=2 rootm1pf-dp-hp-qn<2-6 (:instance q-vals (j (n))))
                  :in-theory (enable rootm1pf-dp-hp-qn<2-11 roots-rewrite quot inc))))

;;---------------------------------------------------------------------------------------

(defthmd sqrt-a-x
  (implies (not (specialp))
           (equal (qsqrt (a) (1+ (* 2 (n))))
                  (* (expt 2 (1+ (- (expq) (bias (f)))))
                     (qsqrt (x) (1+ (* 2 (n)))))))
  :hints (("Goal" :in-theory (enable n a-x dp sp hp p prec bias f)
                  :use (fnum-vals x-bounds
                        (:instance qsqrt-shift (x (x)) (n (1+ (* 2 (n)))) (k (1+ (- (expq) (bias (f))))))))))

(local-defthmd error-1
  (implies (not (specialp))
           (and (<= (blo (n)) (rf))
                (>= (bhi (n)) (rf))))
  :hints (("Goal" :in-theory (enable rf n inv r-bnds-inv)
                  :use ((:instance inv-lemma (j (n)))))))

(in-theory (disable (blo) (bhi)))

(defthmd quotf-error-a
  (implies (not (specialp))
           (and (<= (expt (- (quotf) (* 2/3 (expt 4 (- (n))))) 2)
	           (x))
                (>= (expt (+ (quotf) (* 2/3 (expt 4 (- (n))))) 2)
	           (x))))
  :hints (("Goal" :in-theory (enable rf quotf n)
                  :use (error-1 (:instance r-bounds (j (n)))))))

(defthmd quotf-bounds
  (implies (not (specialp))
           (and (<= (quotf) 1)
                (>= (quotf) 1/2)))
  :hints (("Goal" :in-theory (enable quotf n inv quot-bnds-inv)
                  :use ((:instance inv-lemma (j (n)))))))

(local-defthmd error-4
  (implies (not (specialp))
           (and (< (expt (- (quotf) (expt 4 (- (n)))) 2)
	           (x))
                (> (expt (+ (quotf) (expt 4 (- (n)))) 2)
	           (x))))
  :hints (("Goal" :in-theory (enable expt rf quotf n)
                  :nonlinearp t
                  :use (fnum-vals quotf-error-a quotf-bounds))))

(local-defthmd error-5
  (implies (not (specialp))
           (<= (expo (- (quotf) (expt 4 (- (n)))))
	       -1))
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quotf-bounds (:instance expo<= (x (- (quotf) (expt 4 (- (n))))) (n -1))))))

(local-defthmd error-6
  (implies (not (specialp))
           (exactp (- (quotf) (expt 4 (- (n))))
	           (* 2 (n))))
  :hints (("Goal" :in-theory (enable quotf exactp2 n)
                  :use (fnum-vals error-5
		        (:instance exactp-<= (x (- (quotf) (expt 4 (- (n)))))
			                     (m (+ (* 2 (n)) (expo (- (quotf) (expt 4 (- (n))))) 1))
					     (n (* 2 (n))))
		        (:instance int-quot (j (n)))))))

(local-defthmd error-7
  (implies (not (specialp))
           (exactp (sig (a)) (p)))
  :hints (("Goal" :in-theory (enable exactp exactp-sig)
                  :use (exactp-a p-vals))))

(defthmd exactp-x
  (implies (not (specialp))
           (exactp (x) (p)))
  :hints (("Goal" :in-theory (enable x)
                  :use (error-7 p-vals
                        (:instance exactp-shift (x (sig (a))) (n (p)) (k -1))
                        (:instance exactp-shift (x (sig (a))) (n (p)) (k -2))))))

(local-defthmd error-9
  (implies (not (specialp))
           (< (x)
	      (* (- 1 (expt 2 (- (1+ (p)))))
	         (- 1 (expt 2 (- (1+ (p))))))))
  :hints (("Goal" :use (p-vals exactp-x x-bounds (:instance fp-2 (n (p)) (x 1) (y (x)))))))

(local-defthmd error-10
  (implies (not (specialp))
           (< (- (quotf) (expt 4 (- (n))))
	      (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :in-theory (enable n) :use (p-vals error-4 error-9) :nonlinearp t)))

(local-defthmd error-11
  (implies (not (specialp))
           (< (quotf) 1))
  :hints (("Goal" :in-theory (enable n f dp sp hp p prec)
                  :use (fnum-vals error-10)
		  :nonlinearp t)))

(local-defthmd error-12
  (implies (not (specialp))
           (<= (* (expt 4 (n)) (quotf))
	       (1- (expt 4 (n)))))
  :hints (("Goal" :in-theory (enable quotf n)
                  :use (error-11 (:instance int-quot (j (n))))
		  :nonlinearp t)))

(local-defthm error-13
  (implies (not (specialp))
           (or (= (+ (quotf) (expt 4 (- (n)))) 1)
               (<= (expo (+ (quotf) (expt 4 (- (n)))))
	           -1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable n)
                  :use (fnum-vals quotf-bounds error-12
		        (:instance expo<= (x (+ (quotf) (expt 4 (- (n))))) (n -1))))))

(local-defthmd error-14
  (implies (not (specialp))
           (exactp (+ (quotf) (expt 4 (- (n))))
	           (* 2 (n))))
  :hints (("Goal" :in-theory (enable quotf exactp2 n)
                  :use (fnum-vals error-13
		        (:instance exactp-<= (x (+ (quotf) (expt 4 (- (n)))))
			                     (m (+ (* 2 (n)) (expo (+ (quotf) (expt 4 (- (n))))) 1))
					     (n (* 2 (n))))
		        (:instance int-quot (j (n)))))))

(defthmd quotf-error-b
  (implies (not (specialp))
           (< (abs (- (qsqrt (x) (1+ (* 2 (n))))
	              (quotf)))
	      (expt 2 (- (* 2 (n))))))
  :hints (("Goal" :in-theory (enable expt n)
                  :use (fnum-vals error-4 error-6 error-14 x-bounds
		        (:instance exactp-cmp-qsqrt (x (x)) (n (1+ (* 2 (n)))) (q (- (quotf) (expt 4 (- (n))))))
		        (:instance exactp-cmp-qsqrt (x (x)) (n (1+ (* 2 (n)))) (q (+ (quotf) (expt 4 (- (n))))))))))

(defthmd qsqrt-x-upper
  (implies (not (specialp))
           (< (qsqrt (x) (1+ (* 2 (n))))
	      (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (fnum-vals error-9 x-bounds
                        (:instance exactp-cmp-qsqrt (x (x)) (n (1+ (* 2 (n)))) (q (- 1 (expt 2 (- (1+ (p))))))))
		  :in-theory (enable n p prec f dp sp hp))))

(local-defthmd quotf-upper-1
  (implies (and (not (specialp))
                (= (* 2 (n)) (1+ (p))))
	   (< (quotf) 1))
  :hints (("Goal" :use (p-vals qsqrt-x-upper quotf-error-b)
		  :in-theory (enable n))))

(local-defthmd quotf-upper-2
  (implies (and (not (specialp))
                (= (* 2 (n)) (1+ (p))))
	   (<= (* (expt 2 (* 2 (n))) (quotf))
	       (1- (expt 2 (* 2 (n))))))
  :hints (("Goal" :use (p-vals quotf-upper-1 (:instance int-quot (j (n))))
		  :in-theory (enable quotf n))))

(local-defthmd quotf-upper-3
  (implies (and (not (specialp))
                (= (* 2 (n)) (1+ (p))))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (p-vals quotf-upper-2)
                  :nonlinearp t
		  :in-theory (enable n))))

(local-defthmd quotf-upper-4
  (implies (and (not (specialp))
                (= (* 2 (n)) (+ 2 (p))))
	   (< (quotf) (- 1 (expt 2 (- (+ 2 (p)))))))
  :hints (("Goal" :use (p-vals qsqrt-x-upper quotf-error-b)
		  :in-theory (enable n))))

(local-defthmd quotf-upper-5
  (implies (and (not (specialp))
                (= (* 2 (n)) (+ 2 (p))))
	   (<= (* (expt 2 (* 2 (n))) (quotf))
	       (- (expt 2 (* 2 (n))) 2)))
  :hints (("Goal" :use (p-vals quotf-upper-4 (:instance int-quot (j (n))))
                  :nonlinearp t
		  :in-theory (enable quotf n))))

(local-defthmd quotf-upper-6
  (implies (and (not (specialp))
                (= (* 2 (n)) (+ 2 (p))))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (p-vals quotf-upper-5)
                  :nonlinearp t
		  :in-theory (enable quotf n))))

(defthmd quotf-upper
  (implies (not (specialp))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p)))))))
  :hints (("Goal" :use (quotf-upper-3 quotf-upper-6 fnum-vals)
		  :in-theory (enable n f dp sp hp p prec))))


;;---------------------------------------------------------------------------------------

(local-defund remsgn ()
  (bitn (bits (+ (+ (rpf) (lognot (rnf))) 1) 58 0) 58))

(local-defund remzero () (log= (logxor (rpf) (rnf)) 0))

(local-defund rootlo () (bits (if1 (remsgn) (rootm1shft) (rootshft)) 54 0))

(local-defund rootlop () (bits (if1 (remsgn) (rootm1pshft) (rootpshft)) 54 0))

(local-defund qtrunc* ()
  (if1 (lsbis2)
       (bits (rootlo) 53 1)
     (bits (rootlo) 52 0)))
     
(local-defund qinc* ()
  (if1 (lsbis2)
       (bits (rootlop) 53 1)
     (bits (rootlop) 52 0)))
     
(local-defund stk* () 
  (if1 (lsbis2)
       (logior1 (bitn (rootlo) 0) (lognot1 (remzero)))
     (lognot1 (remzero))))
  
(local-defthmd computeq-lemma
  (and (equal (qtrunc) (qtrunc*))
       (equal (qinc) (qinc*))
       (equal (stk) (stk*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(remsgn remzero rootlo rootlop qtrunc* qinc* stk* qtrunc qinc stk computeq))))

(local-in-theory (disable (remsgn) (remzero) (rootlo) (rootlop) (qtrunc*) (qinc*) (stk*) (qtrunc) (qinc) (stk) (computeq)))

(defthm integerp-qinc
  (integerp (qinc))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable computeq-lemma qinc*))))

(local-defthmd bvecp-rp-j
  (bvecp (rp j) 59)
  :hints (("Goal" :expand ((rp j)) :use (fnum-vals) :in-theory (enable rp-1 firstiter nextrem))))

(local-defthmd bvecp-rn-j
  (bvecp (rn j) 59)
  :hints (("Goal" :expand ((rn j)) :use (fnum-vals) :in-theory (enable rn-1 firstiter nextrem))))

(local-defthmd bvecp-rpf-rnf
  (implies (not (specialp))
           (and (bvecp (rpf) 59)
	        (bvecp (rnf) 59)))
  :hints (("Goal" :use ((:instance bvecp-rp-j (j (n))) (:instance bvecp-rn-j (j (n))))
                  :in-theory (enable rpf rnf))))

(local-defthmd r-rp-rn
  (implies (not (specialp))
	   (equal (mod (* (expt 2 55) (rf)) (expt 2 59))
	          (mod (- (rpf) (rnf)) (expt 2 59))))
  :hints (("Goal" :use (fnum-vals (:instance inv-lemma (j (n))))
                  :in-theory (enable n rf rpf rnf inv rpn-inv))))

(local-defthmd r-bound
  (implies (and (not (specialp))
                (not (zp j))
		(inv j))
           (< (abs (* (expt 2 55) (r j)))
              (expt 2 56)))
  :hints (("Goal" :in-theory (enable inv r-bnds-inv blo bhi quot-bnds-inv)
                  :nonlinearp t)))

(local-defthmd rf-bound
  (implies (not (specialp))
           (< (abs (* (expt 2 55) (rf))) (expt 2 56)))
  :hints (("Goal" :use (fnum-vals (:instance inv-lemma (j (n))) (:instance r-bound (j (n))))
                  :in-theory (enable n rf))))

(local-defthmd r-rp-rn-0
  (implies (not (specialp))
	   (iff (= (rf) 0)
	        (= (rpf) (rnf))))
  :hints (("Goal" :use (r-rp-rn bvecp-rpf-rnf rf-bound
                        (:instance mod-force-equal (a (* (expt 2 55) (rf))) (b 0) (n (expt 2 59)))
                        (:instance mod-force-equal (a (- (rpf) (rnf))) (b 0) (n (expt 2 59))))
		  :in-theory (enable rf rpf rnf bvecp))))

(local-defthmd remzero-rewrite-1
  (implies (not (specialp))
           (equal (remzero)
	          (if (= (logxor (rpf) (rnf)) 0) 1 0)))
  :hints (("Goal" :in-theory (enable remzero rpf rnf))))

(local-defthm integerp-rpf
  (implies (not (specialp))
	   (integerp (rpf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthm integerp-rnf
  (implies (not (specialp))
	   (integerp (rnf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd remzero-rewrite-2
  (implies (not (specialp))
	   (equal (remzero)
	          (if (= (rf) 0) 1 0)))
  :hints (("Goal" :use (r-rp-rn-0
                        (:instance logxor-not-0 (x (rpf)) (y (rnf))))
		  :in-theory (enable remzero-rewrite-1))))
                        
(local-defthmd remsgn-rewrite-1
  (implies (not (specialp))
           (equal (remsgn)
                  (bitn (bits (- (rpf) (rnf)) 58 0) 58)))
  :hints (("Goal" :use (bvecp-rpf-rnf) :in-theory (enable lognot rpf rnf remsgn))))

(local-defthmd remsgn-rewrite-2
  (implies (not (specialp))
           (equal (remsgn)
                  (bitn (bits (* (expt 2 55) (rf)) 58 0) 58)))
  :hints (("Goal" :use (r-rp-rn) :in-theory (enable remsgn-rewrite-1 bits))))

(local-defthmd remsgn-rewrite-3
  (implies (not (specialp))
           (equal (remsgn)
                  (if (< (si (bits (* (expt 2 55) (rf)) 58 0) 59) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable si remsgn-rewrite-2)
                  :use ((:instance bits-bounds (x (* (expt 2 55) (rf))) (i 58) (j 0))))))

(local-defthmd int-rf
  (implies (not (specialp))
           (integerp (* (expt 2 55) (rf))))
  :hints (("Goal" :in-theory (enable rf n inv rpn-inv)
                  :use (fnum-vals (:instance inv-lemma (j (n)))))))
		  
(local-defthmd remsgn-rewrite-4
  (implies (not (specialp))
           (equal (remsgn)
                  (if (< (rf) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable remsgn-rewrite-3)
                  :nonlinearp t
                  :use (rf-bound int-rf (:instance si-bits (x (* (expt 2 55) (rf))) (n 59))))))

(local-defthmd remsgn-rewrite-5
  (implies (not (specialp))
           (<= (expo (quotf)) -1))
  :hints (("Goal" :use (p-vals quotf-upper (:instance expo<= (x (quotf)) (n -1))))))

(local-defthmd remsgn-rewrite-6
  (implies (not (specialp))
           (exactp (quotf) (* 2 (n))))
  :hints (("Goal" :in-theory (enable quotf exactp2 n)
                  :use (fnum-vals remsgn-rewrite-5
		        (:instance exactp-<= (x (quotf))
			                     (m (+ (* 2 (n)) (expo (quotf)) 1))
					     (n (* 2 (n))))
		        (:instance int-quot (j (n)))))))

(local-defthmd remsgn-rewrite
  (implies (not (specialp))
           (equal (remsgn)
                  (if (< (qsqrt (x) (1+ (* 2 (n))))
                         (quotf))
		      1 0)))
  :hints (("Goal" :in-theory (enable remsgn-rewrite-4 quotf rf r n)
                  :nonlinearp t
                  :use (fnum-vals remsgn-rewrite-6 quotf-bounds
                        (:instance exactp-cmp-qsqrt (n (1+ (* 2 (n)))) (q (quotf)) (x (x)))))))

(local-defthmd remzero-rewrite
  (implies (not (specialp))
           (equal (remzero)
                  (if (= (qsqrt (x) (1+ (* 2 (n))))
                         (quotf))
		      1 0)))
  :hints (("Goal" :in-theory (enable remzero-rewrite-2 quotf rf r n)
                  :nonlinearp t
                  :use (fnum-vals remsgn-rewrite-6 quotf-bounds
                        (:instance exactp-cmp-qsqrt (n (1+ (* 2 (n)))) (q (quotf)) (x (x)))))))

(local-defthmd bvecp-rootf
  (implies (not (specialp))
           (and (bvecp (rootf) 55)
	        (bvecp (rootm1f) 55)))
  :hints (("Goal" :use (fnum-vals (:instance bvecp-roots (j (n))))
                  :in-theory (enable rootf-rewrite rootm1f-rewrite))))

(local-defthmd rootshft-1
  (implies (not (specialp))
           (equal (rootshft)
	          (* (expt 2 (- (* 2 (n)) 54)) (rootf))))
  :hints (("Goal" :use (fnum-vals bvecp-rootf) :in-theory (enable roots-high rootshft))))

(local-defthmd rootshft-rewrite
  (implies (not (specialp))
           (equal (rootshft)
	          (* (expt 2 (* 2 (n))) (quotf))))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootshft-1 quotf roots-rewrite))))

(local-defthmd rootm1shft-1
  (implies (not (specialp))
           (equal (rootm1shft)
	          (* (expt 2 (- (* 2 (n)) 54)) (rootm1f))))
  :hints (("Goal" :use (fnum-vals bvecp-rootf) :in-theory (enable roots-high rootm1shft))))

(local-defthmd rootm1shft-rewrite
  (implies (not (specialp))
           (equal (rootm1shft)
	          (1- (* (expt 2 (* 2 (n))) (quotf)))))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable rootm1shft-1 quotf roots-rewrite))))

(local-defthmd rootpshft-1
  (implies (not (specialp))
           (integerp (* (expt 2 (- (* 2 (n)) 54)) (rootpf))))
  :hints (("Goal" :use (fnum-vals bvecp-rootf
                        (:instance bits-plus-bits (x (rootf)) (n 54) (p (- 54 (* 2 (n)))) (m 0)))
                  :in-theory (enable rootpf-lemma rootf inc))))

(local-defthmd rootpshft-2
  (implies (not (specialp))
           (equal (bits (rootpf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals rootpshft-1 bvecp-rootpf
                        (:instance bits-shift-up-2 (x (* (expt 2 (- (* 2 (n)) 54)) (rootpf))) (i -1) (k (- 54 (* 2 (n)))))))))

(local-defthmd rootpshft-3
  (implies (not (specialp))
           (equal (rootpshft)
	          (* (expt 2 (- (* 2 (n)) 54)) (rootpf))))
  :hints (("Goal" :in-theory (enable rootpshft)
                  :use (fnum-vals bvecp-rootpf rootpshft-2
                        (:instance bits-plus-bits (x (rootpf)) (n 54) (p (- 54 (* 2 (n)))) (m 0))))))

(local-defthmd rootpshft-rewrite
  (implies (not (specialp))
           (equal (rootpshft)
	          (+ (* (expt 2 (* 2 (n))) (quotf))
		     (expt 2 (1+ (lsbis2))))))
  :hints (("Goal" :in-theory (enable rootpshft-3 roots-rewrite quotf rootpf-lemma inc lsbis2)
                  :use (fnum-vals))))

(local-defthmd rootm1pshft-1
  (implies (not (specialp))
           (integerp (* (expt 2 (- (* 2 (n)) 54)) (rootm1pf))))
  :hints (("Goal" :use (fnum-vals bvecp-rootf
                        (:instance bits-plus-bits (x (rootm1f)) (n 54) (p (- 54 (* 2 (n)))) (m 0)))
                  :in-theory (enable rootm1pf-lemma rootm1f inc))))

(local-defthmd rootm1pshft-2
  (implies (not (specialp))
           (equal (bits (rootm1pf) (- 53 (* 2 (n))) 0)
	          0))
  :hints (("Goal" :use (fnum-vals rootm1pshft-1 bvecp-rootpf
                        (:instance bits-shift-up-2 (x (* (expt 2 (- (* 2 (n)) 54)) (rootm1pf))) (i -1) (k (- 54 (* 2 (n)))))))))

(local-defthmd rootm1pshft-3
  (implies (not (specialp))
           (equal (rootm1pshft)
	          (* (expt 2 (- (* 2 (n)) 54)) (rootm1pf))))
  :hints (("Goal" :in-theory (enable rootm1pshft)
                  :use (fnum-vals bvecp-rootpf rootm1pshft-2
                        (:instance bits-plus-bits (x (rootm1pf)) (n 54) (p (- 54 (* 2 (n)))) (m 0))))))

(local-defthmd rootm1pshft-rewrite
  (implies (not (specialp))
           (equal (rootm1pshft)
	          (+ (* (expt 2 (* 2 (n))) (quotf))
		     (expt 2 (1+ (lsbis2)))
		     -1)))
  :hints (("Goal" :in-theory (enable rootm1pshft-3 roots-rewrite quotf rootm1pf-lemma inc lsbis2)
                  :use (fnum-vals))))

(local-defthmd qtrunc-1
  (implies (not (specialp))
           (< (abs (- (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
	              (* (expt 2 (* 2 (n))) (quotf))))
	      1))
  :hints (("Goal" :nonlinearp t
                  :use (fnum-vals quotf-error-b))))

(local-defthmd qtrunc-2
  (implies (and (not (specialp))
                (= (remsgn) 0))
	   (and (<= (* (expt 2 (* 2 (n))) (quotf))
	            (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		(< (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
		   (1+ (* (expt 2 (* 2 (n))) (quotf))))))
  :hints (("Goal" :in-theory (enable remsgn-rewrite)
                  :use (fnum-vals qtrunc-1))))

(local-defthmd qtrunc-3
  (implies (not (specialp))
           (integerp (* (expt 2 (* 2 (n))) (quotf))))
  :hints (("Goal" :in-theory (enable quotf)
                  :use (fnum-vals (:instance int-quot (j (n)))))))

(local-defthmd qtrunc-4
  (implies (and (not (specialp))
                (= (remsgn) 0))
           (equal (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
	          (* (expt 2 (* 2 (n))) (quotf))))
  :hints (("Goal" :use (qtrunc-2 qtrunc-3))))

(local-defthmd bvecp-rootshft
  (implies (not (specialp))
           (and (bvecp (rootshft) 55)
	        (bvecp (rootm1shft) 55)
                (bvecp (rootpshft) 55)
                (bvecp (rootm1pshft) 55)))
  :hints (("Goal" :in-theory (enable rootshft rootm1shft rootpshft rootm1pshft bvecp)
                  :use (fnum-vals bvecp bvecp-rootpf rootf rootm1f
		        (:instance bvecp-roots (j (n)))
			(:instance bits-bounds (x (rootf)) (i 54) (j (- 54 (* 2 (n)))))
			(:instance bits-bounds (x (rootm1f)) (i 54) (j (- 54 (* 2 (n)))))
			(:instance bits-bounds (x (rootpf)) (i 54) (j (- 54 (* 2 (n)))))
			(:instance bits-bounds (x (rootm1pf)) (i 54) (j (- 54 (* 2 (n)))))))))
		
(local-defthmd qtrunc-5
  (implies (and (not (specialp))
                (= (remsgn) 0))
           (equal (rootlo)
	          (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
  :hints (("Goal" :use (bvecp-rootshft qtrunc-4)
                  :in-theory (enable rootlo rootshft-rewrite))))

(local-defthmd qtrunc-6
  (implies (and (not (specialp))
                (= (remsgn) 0))
           (equal (rootlop)
	          (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		     (expt 2 (1+ (lsbis2))))))
  :hints (("Goal" :use (bvecp-rootshft qtrunc-4)
                  :in-theory (enable rootlop rootpshft-rewrite))))

(local-defthmd qtrunc-7
  (implies (and (not (specialp))
                (= (remsgn) 1))
	   (and (< (1- (* (expt 2 (* 2 (n))) (quotf)))
	           (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		(< (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
		   (* (expt 2 (* 2 (n))) (quotf)))))
  :hints (("Goal" :in-theory (enable remsgn-rewrite)
                  :use (fnum-vals qtrunc-1))))

(local-defthmd qtrunc-8
  (implies (and (not (specialp))
                (= (remsgn) 1))
           (equal (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
	          (1- (* (expt 2 (* 2 (n))) (quotf)))))
  :hints (("Goal" :use (qtrunc-3 qtrunc-7))))

(local-defthmd qtrunc-9
  (implies (and (not (specialp))
                (= (remsgn) 1))
           (equal (rootlo)
	          (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
  :hints (("Goal" :use (bvecp-rootshft qtrunc-8)
                  :in-theory (enable rootlo rootm1shft-rewrite))))

(local-defthmd qtrunc-10
  (implies (and (not (specialp))
                (= (remsgn) 1))
           (equal (rootlop)
	          (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		     (expt 2 (1+ (lsbis2))))))
  :hints (("Goal" :use (bvecp-rootshft qtrunc-8)
                  :in-theory (enable rootlop rootm1pshft-rewrite))))

(local-defthmd qtrunc-11
  (implies (not (specialp))
           (equal (rootlo)
	          (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
  :hints (("Goal" :use (qtrunc-5 qtrunc-9)
                  :in-theory (enable remsgn))))

(local-defthmd qtrunc-12
  (implies (not (specialp))
           (equal (rootlop)
	          (+ (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		     (expt 2 (1+ (lsbis2))))))
  :hints (("Goal" :use (qtrunc-6 qtrunc-10)
                  :in-theory (enable remsgn))))
		  
(local-defthmd qtrunc-13
  (implies (and (not (specialp))
		(= (lsbis2) 0))
           (equal (qtrunc)
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qtrunc* qtrunc-11 bits lsbis2)
                  :use (fnum-vals))))

(local-defthmd qtrunc-14
  (implies (and (not (specialp))
		(= (lsbis2) 0))
           (equal (qinc)
	          (mod (+ 2 (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qinc* qtrunc-12 bits lsbis2)
                  :use (fnum-vals))))

(local-defthmd qtrunc-15
  (implies (and (not (specialp))
		(= (lsbis2) 1))
           (equal (qtrunc)
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qtrunc* bits qtrunc-11 lsbis2)
                  :use (fnum-vals (:instance bits-shift-down-1 (x (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))))
		                                               (k 1) (i 52) (j 0))))))

(local-defthmd qtrunc-16
  (implies (and (not (specialp))
		(= (lsbis2) 1))
           (equal (qinc)
	          (mod (fl (+ 2 (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2)))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qinc* bits qtrunc-12 lsbis2)
                  :use (fnum-vals
                        (:instance bits-shift-down-1 (x (+ 4 (fl (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
		                                     (k 1) (i 52) (j 0))))))

(local-defthmd qtrunc-17
  (implies (and (not (specialp))
		(= (lsbis2) 1))
           (equal (fl (+ 2 (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2)))
	          (+ 2 (fl (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2)))))
  :hints (("Goal" :in-theory (e/d (lsbis2) (FL*1/INT-REWRITE-ALT FL/INT-REWRITE FL/INT-REWRITE-ALT fl+int-rewrite))
                  :use (fnum-vals
		        (:instance fl+int-rewrite (n 2) (x (fl (/ (fl (* (expt 2 (+ 2 (p)))(qsqrt (x) (1+ (* 2 (n)))))) 2))))))))

(local-defthmd qtrunc-18
  (implies (and (not (specialp))
		(= (lsbis2) 1))
           (equal (fl (/ (fl (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2))
	          (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))))
  :hints (("Goal" :in-theory (enable lsbis2)
                  :use (fnum-vals))))

(local-defthmd qtrunc-19
  (implies (and (not (specialp))
		(= (lsbis2) 1))
           (equal (qinc)
	          (mod (+ 2 (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory '(qtrunc-16)
                  :use (qtrunc-17 qtrunc-18))))

(local-defthmd qtrunc-20
  (implies (not (specialp))
           (equal (qtrunc)
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		       (expt 2 53))))
  :hints (("Goal" :use (qtrunc-13 qtrunc-15)
                  :in-theory (enable lsbis2))))

(local-defthmd qtrunc-21
  (implies (not (specialp))
           (equal (qinc)
	          (mod (+ 2 (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
		       (expt 2 53))))
  :hints (("Goal" :use (qtrunc-14 qtrunc-19)
                  :in-theory (enable lsbis2))))

(defthmd qtrunc-rewrite
  (implies (not (specialp))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (p)))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))))
                                                  (a 53) (b (p))))
                  :in-theory (enable lsbis2 qtrunc-20))))

(defthmd qinc-rewrite
  (implies (not (specialp))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2) (expt 2 (p)))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (+ 2 (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))))
                                                  (a 53) (b (p))))
                  :in-theory (enable lsbis2 qtrunc-21))))

(local-defthmd stk-1
  (implies (not (specialp))
           (equal (remzero)
	          (if (= (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n)))))
		         (* (expt 2 (* 2 (n))) (quotf)))
		      1 0)))
  :hints (("Goal" :in-theory (enable remzero-rewrite))))

(local-defthmd stk-2
  (implies (and (not (specialp))
                (= (remsgn) 0))
           (equal (remzero)
	          (if (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		      1 0)))
  :hints (("Goal" :in-theory (enable stk-1)
                  :use (fnum-vals qtrunc-4))))

(local-defthmd stk-3
  (implies (and (not (specialp))
                (= (remsgn) 1))
           (not (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))))
  :hints (("Goal" :use (qtrunc-3 qtrunc-7))))

(local-defthmd stk-4
  (implies (and (not (specialp))
                (= (remsgn) 1))
           (equal (remzero) 0))
  :hints (("Goal" :use (remsgn-rewrite remzero-rewrite))))

(local-defthmd stk-5
  (implies (not (specialp))
           (equal (remzero)
	          (if (integerp (* (expt 2 (* 2 (n))) (qsqrt (x) (1+ (* 2 (n))))))
		      1 0)))
  :hints (("Goal" :in-theory (enable remsgn-rewrite)
                  :use (stk-2 stk-3 stk-4))))

(local-defthmd stk-6
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (stk)
	          (if (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1)))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable stk* computeq-lemma stk-5))))

(local-defthmd stk-7
  (implies (and (not (specialp))
                (= (lsbis2) 1))
           (equal (stk)
	          (if (and (integerp (* (expt 2 (+ 2 (p))) (qsqrt (x) (1+ (* 2 (n))))))
		           (= (bitn (rootlo) 0) 0))
		      0 1)))
  :hints (("Goal" :use (fnum-vals) :in-theory (enable stk* computeq-lemma stk-5))))

(local-defthmd stk-8
  (implies (and (not (specialp))
                (= (lsbis2) 1))
           (equal (bitn (rootlo) 0)
	          (if (integerp (/ (rootlo) 2))
		      0 1)))
  :hints (("Goal" :use ((:instance bitn-rec-0 (x (rootlo)))
                        (:instance mod-def (x (rootlo)) (y 2))))))

(local-defthmd stk-9
  (implies (and (not (specialp))
                (= (lsbis2) 1))
           (equal (stk)
	          (if (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1)))
  :hints (("Goal" :in-theory (enable stk-7 qtrunc-11) :use (stk-8 fnum-vals))))

(defthmd stk-rewrite
  (implies (not (specialp))
           (equal (stk)
	          (if (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1)))
  :hints (("Goal" :in-theory (enable stk) :use (stk-6 stk-9))))
