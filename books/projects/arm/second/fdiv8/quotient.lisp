(in-package "RTL")

(include-book "induct")

(defthmd incquot-1
  (implies (not (specialp))
           (and (bvecp (quot (1- (* 2 (c)))) (* 3 (1- (* 2 (c)))))
                (bvecp (quotm1 (1- (* 2 (c)))) (* 3 (1- (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (1- (* 2 (c)))))))))

(defthmd incquot-2
  (implies (not (specialp))
           (equal (quot (1- (* 2 (c))))
	          (* (expt 8 (- (* 2 (c)) 2)) (quotient (1- (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (1- (* 2 (c)))))))))

(defthmd incquot-3
  (implies (not (specialp))
           (equal (quotm1 (1- (* 2 (c))))
	          (1- (quot (1- (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (1- (* 2 (c)))))))))

(defthmd incquot-4
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (>= (q (* 2 (c))) -1))
           (equal (quotpf)
                  (+ (* 64 (quot (1- (* 2 (c)))))
                     (* 8 (q (* 2 (c))))
                     8)))
  :hints (("Goal" :use (fnum-vals incquot-1
                        (:instance bits-shift-up-1 (x (quot (1- (* 2 (c))))) (k 6) (i 64) (j 6))
                        (:instance bits-shift-up-1 (x (quot (1- (* 2 (c))))) (k 6) (i 2) (j 0))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c bvecp cat quotpf-rewrite incquot))))

(defthmd incquot-5
  (implies (not (specialp))
           (equal (quot (1+ (* 2 (c))))
	          (* (expt 8 (* 2 (c))) (quotient (1+ (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (1+ (* 2 (c)))))))))

(defthmd incquot-6
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (>= (q (* 2 (c))) -1))
           (equal (quotpf)
                  (+ (quot (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-2 incquot-5
                        (:instance q-vals (j (1+ (* 2 (c)))))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c incquot-4 quotient))))

(defthmd incquot-7
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) -1))
           (equal (quotpf)
                  (+ (* 64 (quotm1 (1- (* 2 (c)))))
                     (* 8 (q (* 2 (c))))
                     72)))
  :hints (("Goal" :use (fnum-vals incquot-1
                        (:instance bits-shift-up-1 (x (quotm1 (1- (* 2 (c))))) (k 6) (i 64) (j 6))
                        (:instance bits-shift-up-1 (x (quotm1 (1- (* 2 (c))))) (k 6) (i 2) (j 0))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c bvecp cat quotpf-rewrite incquot))))

(defthmd incquot-8
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) -1))
           (equal (quotpf)
                  (+ (* 64 (quot (1- (* 2 (c)))))
                     (* 8 (q (* 2 (c))))
                     8)))
  :hints (("Goal" :use (fnum-vals incquot-3
                        (:instance bits-shift-up-1 (x (quotm1 (1- (* 2 (c))))) (k 6) (i 64) (j 6))
                        (:instance bits-shift-up-1 (x (quotm1 (1- (* 2 (c))))) (k 6) (i 2) (j 0))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable incquot-7 c bvecp))))

(defthmd incquot-9
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) -1))
           (equal (quotpf)
                  (+ (quot (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-2 incquot-5
                        (:instance q-vals (j (1+ (* 2 (c)))))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c incquot-8 quotient))))

(defthmd incquot-10
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4))
           (equal (quotpf)
                  (+ (quot (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (incquot-6 incquot-9))))
		  
(defthmd incquot-11
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (>= (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (* 64 (quot (1- (* 2 (c)))))
                     (* 8 (q (* 2 (c))))
                     7)))
  :hints (("Goal" :use (fnum-vals incquot-1
                        (:instance bits-shift-up-1 (x (+ (* 8 (quot (1- (* 2 (c))))) (q (* 2 (c))))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quot (1- (* 2 (c))))) (k 6) (i 64) (j 6))
                        (:instance bits-shift-up-1 (x (quot (1- (* 2 (c))))) (k 6) (i 2) (j 0))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c bvecp cat quotm1pf-rewrite incquot))))

(defthmd incquot-12
  (implies (not (specialp))
           (and (bvecp (quot (1+ (* 2 (c)))) (* 3 (1+ (* 2 (c)))))
                (bvecp (quotm1 (1+ (* 2 (c)))) (* 3 (1+ (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (1+ (* 2 (c)))))))))

(defthmd incquot-13
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (>= (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (1- (quotpf))))
  :hints (("Goal" :use (fnum-vals incquot-4 incquot-8
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c bvecp incquot-11))))

(defthmd incquot-14
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (>= (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (quot (1+ (* 2 (c)))) 3)))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable c bvecp incquot-10 incquot-13))))

(defthmd incquot-15
  (implies (not (specialp))
           (equal (quotm1 (1+ (* 2 (c))))
	          (1- (quot (1+ (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (1+ (* 2 (c)))))))))

(defthmd incquot-16
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (>= (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (quotm1 (1+ (* 2 (c)))) 4)))
  :hints (("Goal" :use (incquot-15 fnum-vals)
                  :in-theory (enable c bvecp incquot-14))))

(defthmd incquot-17
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (* 64 (quotm1 (1- (* 2 (c)))))
                     (* 8 (q (* 2 (c))))
                     71)))
  :hints (("Goal" :use (fnum-vals incquot-1
                        (:instance bits-shift-up-1 (x (+ (* 8 (quotm1 (1- (* 2 (c))))) 8 (q (* 2 (c))))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quotm1 (1- (* 2 (c))))) (k 6) (i 64) (j 6))
                        (:instance bits-shift-up-1 (x (quotm1 (1- (* 2 (c))))) (k 6) (i 2) (j 0))
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c bvecp cat quotm1pf-rewrite incquot))))

(defthmd incquot-18
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (* 64 (quot (1- (* 2 (c)))))
                     (* 8 (q (* 2 (c))))
                     7)))
  :hints (("Goal" :use (fnum-vals incquot-1 incquot-3)
                  :in-theory (enable c bvecp incquot-17))))

(defthmd incquot-19
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (1- (quotpf))))
  :hints (("Goal" :use (fnum-vals incquot-4 incquot-8
                        (:instance q-vals (j (* 2 (c)))))
                  :in-theory (enable c bvecp incquot-18))))

(defthmd incquot-20
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (quot (1+ (* 2 (c)))) 3)))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable c bvecp incquot-10 incquot-19))))

(defthmd incquot-21
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4)
                (< (q (* 2 (c))) 0))
           (equal (quotm1pf)
                  (+ (quotm1 (1+ (* 2 (c)))) 4)))
  :hints (("Goal" :use (incquot-15 fnum-vals)
                  :in-theory (enable c bvecp incquot-20))))

(defthmd incquot-22
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (= (q (1+ (* 2 (c)))) 4))
           (equal (quotm1pf)
                  (+ (quotm1 (1+ (* 2 (c)))) 4)))
  :hints (("Goal" :use (fnum-vals incquot-16 incquot-21
                        (:instance q-vals (j (* 2 (c)))))
	          :in-theory (enable c bvecp))))

(defthmd incquot-23
  (implies (not (specialp))
           (and (bvecp (quot (* 2 (c))) (* 3 (* 2 (c))))
                (bvecp (quotm1 (* 2 (c))) (* 3 (* 2 (c))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (* 2 (c))))))))

(defthmd incquot-24
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4))
           (equal (quotpf)
                  (+ (* 8 (quot (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 2) (j 0))
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat quotpf-rewrite incquot))))

(defthmd incquot-25
  (implies (not (specialp))
           (equal (quot (* 2 (c)))
	          (* (expt 8 (1- (* 2 (c)))) (quotient (* 2 (c))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (* 2 (c))))))))

(defthmd incquot-26
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4))
           (equal (quotpf)
                  (+ (* (expt 8 (* 2 (c)))
		        (quotient (1+ (* 2 (c)))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-23 incquot-25
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat incquot-24 quotient))))

(defthmd incquot-27
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4))
           (equal (quotpf)
                  (+ (quot (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-5)
                  :in-theory (enable c bvecp incquot-26))))

(defthmd incquot-28
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(> (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (* 8 (quot (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     3)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 2) (j 0))
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat quotm1pf-rewrite incquot))))

(defthmd incquot-29
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(> (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (* (expt 8 (* 2 (c)))
		        (quotient (1+ (* 2 (c)))))
                     3)))
  :hints (("Goal" :use (fnum-vals incquot-23 incquot-25
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat incquot-28 quotient))))

(defthmd incquot-30
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(> (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (quot (1+ (* 2 (c))))
                     3)))
  :hints (("Goal" :use (fnum-vals incquot-5)
                  :in-theory (enable c bvecp incquot-29))))
 
(defthmd incquot-31
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(> (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (quotm1 (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-5 incquot-15)
                  :in-theory (enable c bvecp incquot-30))))

(defthmd incquot-32
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(= (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (* 8 (quotm1 (* 2 (c))))
                     7)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quotm1 (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quotm1 (* 2 (c)))) (k 3) (i 2) (j 0)))
                  :in-theory (enable c bvecp cat quotm1pf-rewrite incquot))))

(defthmd incquot-33
  (implies (not (specialp))
           (equal (quotm1 (* 2 (c)))
	          (1- (quot (* 2 (c))))))
  :hints (("Goal" :in-theory (enable c)
                  :use (fnum-vals
                        (:instance induction-result (j (* 2 (c))))))))

(defthmd incquot-34
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(= (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (1- (* 8 (quot (* 2 (c)))))))
  :hints (("Goal" :use (fnum-vals incquot-33)
                  :in-theory (enable c bvecp cat incquot-32))))

(defthmd incquot-35
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(= (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (* (expt 8 (* 2 (c)))
		        (quotient (1+ (* 2 (c)))))
                     3)))
  :hints (("Goal" :use (fnum-vals incquot-23 incquot-25)
                  :in-theory (enable c bvecp cat incquot-34 quotient))))

(defthmd incquot-36
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(= (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (quot (1+ (* 2 (c))))
                     3)))
  :hints (("Goal" :use (fnum-vals incquot-5)
                  :in-theory (enable c bvecp incquot-35))))

(defthmd incquot-37
  (implies (and (not (specialp))
                (= (lsbis2) 1)
                (< (q (1+ (* 2 (c)))) 4)
		(= (q (1+ (* 2 (c)))) -4))
           (equal (quotm1pf)
                  (+ (quotm1 (1+ (* 2 (c))))
                     4)))
  :hints (("Goal" :use (fnum-vals incquot-5 incquot-15)
                  :in-theory (enable c bvecp incquot-36))))

(defthmd incquot-hp-dp
  (implies (and (not (specialp))
                (= (lsbis2) 1))
           (and (equal (quotpf) (+ (quotf) 4))
		(equal (quotm1pf)(+ (quotm1f) 4))))
  :hints (("Goal" :use (incquot-10 incquot-22 incquot-27 incquot-31 incquot-37
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory '(member-equal quotf-rewrite quotm1f-rewrite))))

(defthmd incquot-sp-1
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(>= (q (1+ (* 2 (c)))) -2))
           (equal (quotpf)
                  (+ (* 8 (quot (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     2)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 2) (j 0))
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat quotpf-rewrite incquot))))

(defthmd incquot-sp-2
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (1+ (* 2 (c)))) -2))
           (equal (quotpf)
                  (+ (* 8 (quotm1 (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     10)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quotm1 (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quotm1 (* 2 (c)))) (k 3) (i 2) (j 0))
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat quotpf-rewrite incquot))))

(defthmd incquot-sp-3
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotpf)
                  (+ (* 8 (quot (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     2)))
  :hints (("Goal" :use (fnum-vals incquot-23 incquot-33 incquot-sp-1
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp incquot-sp-2))))

(defthmd incquot-sp-4
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotpf)
                  (+ (* (expt 8 (* 2 (c))) (quotient (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     2)))
  :hints (("Goal" :use (fnum-vals incquot-25
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp incquot-sp-3))))

(defthmd incquot-sp-5
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotpf)
                  (+ (* (expt 8 (* 2 (c))) (quotient (1+ (* 2 (c)))))
                     2)))
  :hints (("Goal" :use (fnum-vals
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp quotient incquot-sp-4))))

(defthmd incquot-sp-6
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotpf)
                  (+ (quot (1+ (* 2 (c))))
                     2)))
  :hints (("Goal" :use (fnum-vals incquot-5
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp incquot-sp-5))))

(defthmd incquot-sp-7
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(>= (q (1+ (* 2 (c)))) -1))
           (equal (quotm1pf)
                  (+ (* 8 (quot (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     1)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quot (* 2 (c)))) (k 3) (i 2) (j 0))
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat quotm1pf-rewrite incquot))))

(defthmd incquot-sp-8
  (implies (and (not (specialp))
                (= (lsbis2) 0)
		(< (q (1+ (* 2 (c)))) -1))
           (equal (quotm1pf)
                  (+ (* 8 (quotm1 (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     9)))
  :hints (("Goal" :use (fnum-vals incquot-23
                        (:instance bits-shift-up-1 (x (quotm1 (* 2 (c)))) (k 3) (i 64) (j 3))
                        (:instance bits-shift-up-1 (x (quotm1 (* 2 (c)))) (k 3) (i 2) (j 0))
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp cat quotm1pf-rewrite incquot))))

(defthmd incquot-sp-9
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotm1pf)
                  (+ (* 8 (quot (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     1)))
  :hints (("Goal" :use (fnum-vals incquot-23 incquot-33 incquot-sp-7
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp incquot-sp-8))))

(defthmd incquot-sp-10
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotm1pf)
                  (+ (* (expt 8 (* 2 (c))) (quotient (* 2 (c))))
                     (q (1+ (* 2 (c))))
                     1)))
  :hints (("Goal" :use (fnum-vals incquot-25
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp incquot-sp-9))))

(defthmd incquot-sp-11
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotm1pf)
                  (+ (* (expt 8 (* 2 (c))) (quotient (1+ (* 2 (c)))))
                     1)))
  :hints (("Goal" :use (fnum-vals
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp quotient incquot-sp-10))))

(defthmd incquot-sp-12
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotm1pf)
                  (+ (quot (1+ (* 2 (c))))
                     1)))
  :hints (("Goal" :use (fnum-vals incquot-5
                        (:instance q-vals (j (1+ (* 2 (c))))))
                  :in-theory (enable c bvecp incquot-sp-11))))

(defthmd incquot-sp-13
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (equal (quotm1pf)
                  (+ (quotm1 (1+ (* 2 (c))))
                     2)))
  :hints (("Goal" :use (fnum-vals incquot-15)
                  :in-theory (enable c bvecp incquot-sp-12))))

(defthmd incquot-sp
  (implies (and (not (specialp))
                (= (lsbis2) 0))
           (and (equal (quotpf) (+ (quotf) 2))
		(equal (quotm1pf)(+ (quotm1f) 2))))
  :hints (("Goal" :use (incquot-sp-6 incquot-sp-13)
                  :in-theory '(member-equal quotf-rewrite quotm1f-rewrite))))

(defthmd incquot-lemma
  (implies (not (specialp))
           (let ((inc (if (= (lsbis2) 1) 4 2)))
             (and (equal (quotpf) (+ (quotf) inc))
                  (equal (quotm1pf)(+ (quotm1f) inc)))))
  :hints (("Goal" :use (incquot-hp-dp incquot-sp)
                  :in-theory (enable lsbis2))))

;;---------------------------------------------------------------------------------------

(local-defund remsgn ()
  (bitn (bits (+ (+ (rpf) (lognot (rnf))) 1) 70 0) 70))

(local-defund remzero () (log= (logxor (rpf) (rnf)) 0))

(local-defund quotlo () (bits (if1 (remsgn) (quotm1f) (quotf)) 64 0))

(local-defund quotlop () (bits (if1 (remsgn) (quotm1pf) (quotpf)) 64 0))

(local-defund qtrunc* ()
  (if1 (lsbis2)
       (bits (quotlo) 53 1)
     (bits (quotlo) 52 0)))
     
(local-defund qinc* ()
  (if1 (lsbis2)
       (bits (quotlop) 53 1)
     (bits (quotlop) 52 0)))
     
(local-defund stk* () 
  (if1 (lsbis2)
       (logior1 (bitn (quotlo) 0) (lognot1 (remzero)))
     (lognot1 (remzero))))
  
(local-defthmd computeq-lemma
  (and (equal (qtrunc)
              (if1 (divpow2)
                   (bits (ash (mana) 1) 52 0)
		   (qtrunc*)))
       (equal (qinc)
              (if1 (divpow2) 0 (qinc*)))
       (equal (stk)
              (if1 (divpow2) 0 (stk*))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(remsgn remzero quotlo quotlop qtrunc* qinc* stk* qtrunc qinc stk computeq))))

(local-in-theory (disable (remsgn) (remzero) (quotlo) (quotlop) (qtrunc*) (qinc*) (stk*) (qtrunc) (qinc) (stk) (computeq)))

(defthm integerp-qtrunc
  (integerp (qtrunc))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable qtrunc* computeq-lemma))))

(defthm integerp-qinc
  (integerp (qinc))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable qinc* computeq-lemma))))

(local-defthmd bvecp-qpf-qnf
  (implies (not (specialp))
           (and (bvecp (quotf) (+ 3 (* 6 (c))))
	        (bvecp (quotm1f) (+ 3 (* 6 (c))))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 2 (c))))))
                  :in-theory (enable c quotf-rewrite quotm1f-rewrite))))

(local-defthmd bvecp-rpf-rnf
  (implies (not (specialp))
           (and (bvecp (rpf) 71)
	        (bvecp (rnf) 71)))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 2 (c))))))
                  :in-theory (enable rpf-rewrite rnf-rewrite))))

(local-defthm integerp-quotf
  (implies (not (specialp))
	   (integerp (quotf)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable c) :use (fnum-vals bvecp-qpf-qnf))))

(local-defthm integerp-quotm1f
  (implies (not (specialp))
	   (integerp (quotm1f)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable c) :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd r-rp-rn
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (mod (* (expt 2 67) (rf)) (expt 2 71))
	          (mod (- (rpf) (rnf)) (expt 2 71))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 2 (c))))))
                  :in-theory (enable rf rpf-rewrite rnf-rewrite))))

(local-defthmd rf-bound
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (<= (abs (rf)) (* 4/7 (d))))
  :hints (("Goal" :use ((:instance induction-result (j (1+ (* 2 (c))))))
                  :in-theory (enable rf))))

(local-defthmd r-rp-rn-0
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (iff (= (rf) 0)
	        (= (rpf) (rnf))))
  :hints (("Goal" :use (r-rp-rn bvecp-rpf-rnf rf-bound d-bounds
                        (:instance mod-force-equal (a (* (expt 2 67) (rf))) (b 0) (n (expt 2 71)))
                        (:instance mod-force-equal (a (- (rpf) (rnf))) (b 0) (n (expt 2 71))))
		  :in-theory (enable bvecp))))

(local-defthmd remzero-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remzero)
	          (if (= (logxor (rpf) (rnf)) 0) 1 0)))
  :hints (("Goal" :in-theory (enable remzero rpf rnf))))

(local-defthm integerp-rpf
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (integerp (rpf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthm integerp-rnf
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (integerp (rnf)))
  :hints (("Goal" :use (bvecp-rpf-rnf)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd remzero-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (remzero)
	          (if (= (rf) 0) 1 0)))
  :hints (("Goal" :use (r-rp-rn-0
                        (:instance logxor-not-0 (x (rpf)) (y (rnf))))
		  :in-theory (enable remzero-rewrite-1))))
                        
(local-defthmd remsgn-rewrite-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsgn)
                  (bitn (bits (- (rpf) (rnf)) 70 0) 70)))
  :hints (("Goal" :use (bvecp-rpf-rnf) :in-theory (enable lognot rpf rnf remsgn))))

(local-defthmd remsgn-rewrite-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsgn)
                  (bitn (bits (* (expt 2 67) (rf)) 70 0) 70)))
  :hints (("Goal" :use (r-rp-rn) :in-theory (enable remsgn-rewrite-1 bits))))

(local-defthmd remsgn-rewrite-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsgn)
                  (if (< (si (bits (* (expt 2 67) (rf)) 70 0) 71) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable si remsgn-rewrite-2)
                  :use ((:instance bits-bounds (x (* (expt 2 67) (rf))) (i 70) (j 0))))))

(local-defthmd int-rf
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (integerp (* (expt 2 67) (rf))))
  :hints (("Goal" :in-theory (enable rf)
                  :use (p-vals (:instance int-r (j (1+ (* 2 (c)))))))))
		  
(local-defthmd remsgn-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (remsgn)
                  (if (< (rf) 0)
		      1 0)))
  :hints (("Goal" :in-theory (enable remsgn-rewrite-3)
                  :nonlinearp t
                  :use (rf-bound d-bounds int-rf (:instance si-bits (x (* (expt 2 67) (rf))) (n 71))))))

(local-defthmd qf-1
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (<= (abs (- (* (expt 2 (* 6 (c))) (/ (x) (d)))
	               (* (expt 2 (* 6 (c))) (qf))))
	       4/7))
  :hints (("Goal" :use (q-error) :nonlinearp t)))

(local-defthmd qf-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (iff (>= (* (expt 2 (* 6 (c))) (/ (x) (d)))
	            (* (expt 2 (* 6 (c))) (qf)))
		(>= (rf) 0)))
  :hints (("Goal" :use (d-bounds) :in-theory (enable rf qf r) :nonlinearp t)))

(local-defthmd qf-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (integerp (* (expt 2 (* 6 (c))) (qf))))
  :hints (("Goal" :use ((:instance int-quot (j (1+ (* 2 (c))))))
                  :in-theory (enable qf))))
		  
(local-defthmd qf-4
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
	   (equal (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))
	          (* (expt 2 (* 6 (c))) (qf))))	          
  :hints (("Goal" :use (qf-1 qf-2 qf-3
                        (:instance fl-unique (x (* (expt 2 (* 6 (c))) (/ (x) (d)))) (n (* (expt 2 (* 6 (c))) (qf))))))))

(local-defthmd qf-5
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (quotlo) (quotf)))
  :hints (("Goal" :in-theory (enable c bvecp remsgn-rewrite quotlo)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd qf-6
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (quotlo)
	          (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))))
  :hints (("Goal" :in-theory (enable c bvecp qf-5 quotf-rewrite qf)
                  :use (fnum-vals qf-4 incquot-5))))

(local-defthmd qf-7
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
           (equal (quotlop) (quotpf)))
  :hints (("Goal" :in-theory (enable c bvecp remsgn-rewrite quotlop incquot-lemma)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd qf-8
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(>= (rf) 0))
	   (let ((inc (if (= (lsbis2) 1) 4 2)))
             (equal (quotlop)
	            (+ inc (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))))))
  :hints (("Goal" :in-theory (enable c bvecp qf-7 incquot-lemma)
                  :use (fnum-vals qf-4 qf-5 qf-6))))

(local-defthmd qf-9
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
	   (equal (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))
	          (1- (* (expt 2 (* 6 (c))) (qf))))	          )
  :hints (("Goal" :use (qf-1 qf-2 qf-3
                        (:instance fl-unique (x (* (expt 2 (* 6 (c))) (/ (x) (d)))) (n (1- (* (expt 2 (* 6 (c))) (qf)))))))))

(local-defthmd qf-10
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (quotlo) (quotm1f)))
  :hints (("Goal" :in-theory (enable c bvecp remsgn-rewrite quotlo)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd qf-11
  (implies (not (specialp))
           (equal (quotm1f)
	          (1- (quot (1+ (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable c bvecp quotm1f-rewrite)
                  :use (fnum-vals (:instance induction-result (j (1+ (* 2 (c)))))))))

(local-defthmd qf-12
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (quotlo)
	          (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))))
  :hints (("Goal" :in-theory (enable c bvecp qf-10 qf-11 qf)
                  :use (fnum-vals qf-9 incquot-5))))

(local-defthmd qf-13
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
           (equal (quotlop) (quotm1pf)))
  :hints (("Goal" :in-theory (enable c bvecp remsgn-rewrite quotlop incquot-lemma)
                  :use (fnum-vals bvecp-qpf-qnf))))

(local-defthmd qf-14
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(< (rf) 0))
	   (let ((inc (if (= (lsbis2) 1) 4 2)))
             (equal (quotlop)
	            (+ inc (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))))))
  :hints (("Goal" :in-theory (enable c bvecp qf-13 incquot-lemma)
                  :use (fnum-vals qf-9 qf-10 qf-12))))

(local-defthmd qf-15
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (quotlo)
	          (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))))
  :hints (("Goal" :use (qf-6 qf-12))))

(local-defthmd qf-16
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (let ((inc (if (= (lsbis2) 1) 4 2)))
             (equal (quotlop)
	            (+ inc (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))))))
  :hints (("Goal" :use (qf-8 qf-14))))

(local-defthmd qf-17
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 0))
           (equal (qtrunc)
	          (mod (fl (* (expt 2 (p)) (/ (x) (d))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qtrunc* qf-15 bits lsbis2 c f sp p prec)
                  :use (fnum-vals))))

(local-defthmd qf-18
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 0))
           (equal (qinc)
	          (mod (+ 2 (fl (* (expt 2 (p)) (/ (x) (d)))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qinc* qf-16 bits lsbis2 c f sp p prec)
                  :use (fnum-vals))))

(local-defthmd qf-19
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
           (equal (qtrunc)
	          (mod (fl (* (expt 2 (p)) (/ (x) (d))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qtrunc* bits qf-15 lsbis2 c f sp hp dp p prec)
                  :use (fnum-vals (:instance bits-shift-down-1 (x (fl (* (expt 2 (* 6 (c))) (/ (x) (d))))) (k 1) (i 52) (j 0))))))

(local-defthmd qf-20
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
           (equal (qinc)
	          (mod (fl (+ 2 (/ (fl (* (expt 2 (1+ (p))) (/ (x) (d)))) 2)))
		       (expt 2 53))))
  :hints (("Goal" :in-theory (enable computeq-lemma qinc* bits qf-16 lsbis2 c f sp hp dp p prec)
                  :use (fnum-vals (:instance bits-shift-down-1 (x (+ 4 (fl (* (expt 2 (* 6 (c))) (/ (x) (d)))))) (k 1) (i 52) (j 0))))))

(local-defthmd qf-21
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
           (equal (fl (+ 2 (/ (fl (* (expt 2 (1+ (p))) (/ (x) (d)))) 2)))
	          (+ 2 (fl (/ (fl (* (expt 2 (1+ (p))) (/ (x) (d)))) 2)))))
  :hints (("Goal" :in-theory (e/d (lsbis2 c f sp hp dp p prec) (FL*1/INT-REWRITE-ALT FL/INT-REWRITE FL/INT-REWRITE-ALT fl+int-rewrite))
                  :use (fnum-vals
		        (:instance fl+int-rewrite (x (fl (/ (fl (* (expt 2 (1+ (p))) (/ (x) (d)))) 2))) (n 2))))))

(local-defthmd qf-22
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
           (equal (fl (/ (fl (* (expt 2 (1+ (p))) (/ (x) (d)))) 2))
	          (fl (* (expt 2 (p)) (/ (x) (d))))))
  :hints (("Goal" :in-theory (enable lsbis2 c f sp hp dp p prec)
                  :use (fnum-vals))))

(local-defthmd qf-23
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
           (equal (qinc)
	          (mod (+ 2 (fl (* (expt 2 (p)) (/ (x) (d)))))
		       (expt 2 53))))
  :hints (("Goal" :in-theory '(qf-20)
                  :use (qf-21 qf-22))))

(local-defthmd qf-24
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (qtrunc)
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 53))))
  :hints (("Goal" :use (qf-17 qf-19)
                  :in-theory (enable lsbis2))))

(local-defthmd qf-25
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (qinc)
	          (mod (+ 2 (fl (* (expt 2 (p)) (/ (x) (d)))))
		       (expt 2 53))))
  :hints (("Goal" :use (qf-18 qf-23)
                  :in-theory (enable lsbis2))))

(local-defthmd qtrunc-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p)))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (fl (* (expt 2 (p)) (/ (x) (d))))) (a 53) (b (p))))
                  :in-theory (enable lsbis2 c f sp hp dp p prec qf-24))))

(defthmd qinc-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (p)) (/ (x) (d)))) 2) (expt 2 (p)))))
  :hints (("Goal" :use ((:instance mod-of-mod-cor (x (+ 2 (fl (* (expt 2 (p)) (/ (x) (d)))))) (a 53) (b (p))))
                  :in-theory (enable lsbis2 c f sp hp dp p prec qf-25))))

(local-defthmd stk-1
  (implies (and (integerp n) (rationalp x) (< (abs (- x n)) 1))
           (iff (integerp x) (= x n))))

(local-defthmd stk-2
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (iff (= (* (expt 2 (* 6 (c))) (/ (x) (d)))
		   (* (expt 2 (* 6 (c))) (qf)))
	        (integerp (* (expt 2 (* 6 (c))) (/ (x) (d))))))
  :hints (("Goal" :use (d-bounds qf-1 qf-3
		        (:instance stk-1 (x (* (expt 2 (* 6 (c))) (/ (x) (d)))) (n (* (expt 2 (* 6 (c))) (qf))))))))

(local-defthmd stk-3
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (iff (= (remzero) 1)
	        (integerp (* (expt 2 (* 6 (c))) (/ (x) (d))))))
  :hints (("Goal" :use (stk-2 qf-2 qf-3 qf-4 qf-9)
                  :in-theory (enable rf qf r remzero-rewrite))))

(local-defthmd stk-4
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 0))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (stk-3 fnum-vals)
                  :in-theory (enable p sp prec f c lsbis2 computeq-lemma stk* remzero-rewrite))))

(local-defthmd stk-5
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
	   (equal (stk)
	          (if (and (integerp (* (expt 2 (1+ (p))) (/ (x) (d))))
		           (integerp (/ (quotlo) 2)))
		      0 1)))
  :hints (("Goal" :use (stk-3 fnum-vals)
                  :in-theory (enable bitn-rec-0 p sp hp dp prec f c lsbis2 computeq-lemma stk* remzero-rewrite))))

(local-defthmd stk-6
  (implies (and (not (specialp))
                (= (divpow2) 0)
		(= (lsbis2) 1))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (stk-3 fnum-vals)
                  :in-theory (enable p lsbis2 sp hp dp prec f c stk-5 qf-15))))

(local-defthmd stk-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (stk-6 stk-4)
                  :in-theory (enable lsbis2))))

(local-defthmd qtrunc-divpow2-1
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (equal (sig (a))
	          (1+ (/ (mana) (expt 2 (1- (p)))))))
  :hints (("Goal" :in-theory (enable divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (a-class fnum-vals spec-fields (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-2
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (equal (sig (b)) 1))
  :hints (("Goal" :in-theory (enable divpow2 encodingp normp denormp decode b f dp sp hp prec p)
                  :use (b-class fnum-vals spec-fields (:instance sig-ndecode (x (opbw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-3
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (>= (sig (a)) 1))
  :hints (("Goal" :in-theory (enable divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (a-class fnum-vals spec-fields (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-4
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (equal (sig (a))
	          (/ (x) (d))))
  :hints (("Goal" :in-theory (enable x d qtrunc-divpow2-1 qtrunc-divpow2-2)
                  :use (qtrunc-divpow2-3 (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(defthmd qtrunc-divpow2-5
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (and (integerp (qtrunc))
	        (equal (qtrunc) (* 2 (mana)))))
  :hints (("Goal" :in-theory (enable bvecp qtrunc divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (bvecp-mana a-class fnum-vals spec-fields (:instance sig-ndecode (x (opaw)) (f (f)))))))

(local-defthmd qtrunc-divpow2-6
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (and (integerp (qtrunc))
	        (integerp (* (expt 2 (p)) (/ (x) (d))))
	        (equal (* (expt 2 (p)) (/ (x) (d)))
	               (+ (expt 2 (p)) (qtrunc)))))
  :hints (("Goal" :use (p-vals bvecp-mana qtrunc-divpow2-4) :in-theory (enable qtrunc-divpow2-5 qtrunc-divpow2-1))))

(local-defthmd qtrunc-divpow2-7
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (+ (expt 2 (p)) (qtrunc)) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-divpow2-6 p-vals (:instance mod-mult (m (qtrunc)) (a 1) (n (expt 2 (p))))))))

(local-defthmd qtrunc-divpow2-8
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (fl (* (expt 2 (p)) (/ (x) (d))))
	          (* (expt 2 (p)) (/ (x) (d)))))
  :hints (("Goal" :use (qtrunc-divpow2-6 p-vals))))

(local-defthmd qtrunc-rewrite-divpow2
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-divpow2-6 qtrunc-divpow2-7 qtrunc-divpow2-8))))

(defthmd qtrunc-rewrite-gen
  (implies (not (specialp))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p)))))
  :hints (("Goal" :use (qtrunc-rewrite qtrunc-rewrite-divpow2))))

(defthmd stk-rewrite-divpow2
  (implies (and (not (specialp))
                (= (divpow2) 1))
	   (and (integerp (* (expt 2 (p)) (/ (x) (d))))
	        (equal (stk) 0)))
  :hints (("Goal" :use (qtrunc-divpow2-6) :in-theory (enable stk))))

(defthmd stk-rewrite-gen
  (implies (not (specialp))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (stk-rewrite stk-rewrite-divpow2))))

