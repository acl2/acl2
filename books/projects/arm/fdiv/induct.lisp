(in-package "RTL")

(include-book "prescale")

(local-defthmd mod-3-val2
  (implies (natp j)
           (member (mod j 3) '(0 1 2)))
  :hints (("Goal" :use ((:instance natp-mod (m j) (n 3))
                        (:instance mod-bnd-1 (m j) (n 3))
                        (:instance bvecp-member (x (mod j 3)) (n 2))))))

(defthmd q-vals
  (member (q j) '(-2 -1 0 1 2))
  :hints (("Goal" :in-theory (enable iter1 iter2 iter3 nextdigit)
                  :expand ((q j) (q 1))
                  :use (mod-3-val2 q1-vals))))

(defthm integerp-q
  (integerp (q j))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (q-vals))))

(defthmd bvecp-div
  (bvecp (div) 57)
  :hints (("Goal" :in-theory (enable div* prescale-lemma))))

(local-in-theory (enable quot))

(defthm rat-quot
  (implies (natp j)
           (rationalp (quot j)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd int-4*n
  (implies (integerp n)
           (integerp (* 4 n))))

(local-defthmd int-quot-1
  (implies (and (natp j) (natp n))
           (= (* (QUOT (+ -2 J)) (EXPT n (+ -1 J)))
              (* n (* (QUOT (+ -2 J)) (EXPT n (+ -2 J)))))))

(local-defthm int-quot-2
  (implies (and (natp j)
                (INTEGERP (* (QUOT (+ -2 J)) (EXPT 4 (+ -2 J)))))
           (INTEGERP (* (QUOT (+ -2 J)) (EXPT 4 (+ -1 J)))))
  :hints (("Goal" :use ((:instance int-quot-1 (n 4))
                        (:instance int-4*n (n (* (QUOT (+ -2 J)) (EXPT 4 (+ -2 J)))))))))

(defthmd int-quot
  (implies (natp j)
           (integerp (* (expt 4 (1- j)) (quot j))))
  :hints (("Goal" :induct (quot j))))

(local-defthmd bvecp-rp-1
  (bvecp (rp-1) 59)
  :hints (("Goal" :in-theory (enable rp-1* prescale-lemma))))

(local-defthmd bvecp-rn-1
  (bvecp (rn-1) 59)
  :hints (("Goal" :in-theory (enable rn-1* prescale-lemma))))

(local-in-theory (disable quot))

(defund rems6 (j)
  (case (mod j 3)
    (2 (bits (+ (+ (bits (rp (1- j)) 56 51) (lognot (bits (rn (1- j)) 56 51))) 1) 5 0))
    (0 (rs6 (1- j)))
    (1 (bits (rs7 (1- j)) 6 1))))

(defund approx (j)
  (if (or (zp j) (= j 1))
      (a-1)
    (/ (si (rems6 j) 6) 8)))

(defund hyp (j)
  (and (= (q j) (maxk (approx j)))
       (< (abs (- (approx j) (* 4 (r (1- j))))) 1/8)
       (<= (abs (r j)) (* 2/3 (d)))
       (bvecp (rp j) 59)
       (bvecp (rn j) 59)
       (= (mod (* (expt 2 56) (r j)) (expt 2 59)) (mod (- (rp j) (rn j)) (expt 2 59)))
       (= (bits (rp j) (- 52 (p)) 0) 0)
       (= (bits (rn j) (- 52 (p)) 0) 0)
       (bvecp (qp j) (- (* 2 j) 2))
       (bvecp (qn j) (- (* 2 j) 2))
       (= (* (expt 4 (1- j)) (- (quot j) (q 1))) (- (qp j) (qn j)))))

(in-theory (disable (rems6) (approx) (hyp)))

;; Objective:

;; (local-defthmd main-induction
;;   (implies (and (not (zp j)) (<= j (1+ (* 3 (n)))))
;;            (hyp j)))

(local-defthmd q-1-q-1
  (implies (not (specialp))
           (equal (q 1) (q1)))
  :hints (("goal" :in-theory (enable q prescale-lemma))))

(local-defthmd r-1-r-1
  (implies (not (specialp))
           (and (equal (rp 1) (rp-1))
	        (equal (rn 1) (rn-1))))
  :hints (("goal" :in-theory (enable rp rn prescale-lemma))))

(local-defthmd hyp-1
  (implies (not (specialp))
           (hyp 1))
  :hints (("Goal" :in-theory (enable q-1-q-1 r-1-r-1 bvecp-rp-1 bvecp-rn-1 hyp approx qp qn quot)
                  :use (a-1-error q1-maxk-a-1 r1-bound rp1-rn1 bits-rp-1-0 bits-rn-1-0))))

(local-defthmd nextdigit-maxk
  (implies (bvecp rems6 6)
           (equal (nextdigit rems6)
	          (maxk (/ (si rems6 6) 8))))
  :hints (("Goal" :in-theory (enable maxk nextdigit)
                  :use ((:instance sumbits-thm (x rems6) (n 6))
		        (:instance bitn-0-1 (x rems6) (n 0))
		        (:instance bitn-0-1 (x rems6) (n 1))
		        (:instance bitn-0-1 (x rems6) (n 2))
		        (:instance bitn-0-1 (x rems6) (n 3))
		        (:instance bitn-0-1 (x rems6) (n 4))
		        (:instance bitn-0-1 (x rems6) (n 5))))))

(local-defthmd q-nextdigit
  (implies (and (not (specialp))
                (integerp j)
		(> j 1))
	   (equal (q j) (nextdigit (rems6 j))))
  :hints (("Goal" :in-theory (enable rems6 q iter1 iter2 iter3)
                  :use (mod-3-val2))))

(local-defthm bvecp-rems6
  (implies (and (not (specialp))
                (integerp j)
		(> j 1))
           (bvecp (rems6 j) 6))
  :hints (("Goal" :in-theory (enable iter1 rems6)
                  :expand ((:free (j) (rs6 j)))
                  :use (mod-3-val2))))

(local-defthmd q-maxk
  (implies (and (not (specialp))
                (integerp j)
		(> j 1))
           (equal (q j) (maxk (approx j))))
  :hints (("Goal" :in-theory (enable approx nextdigit-maxk q-nextdigit))))

(local-defthmd approx-error-1
  (implies (and (not (specialp))
                (not (zp j))
		(= (mod (1+ j) 3) 2))
	   (equal (rems6 (+ 1 j))
	          (mod (- (bits (rp j) 56 51) (bits (rn j) 56 51)) 64)))
  :hints (("Goal" :in-theory (enable rems6 bits lognot))))

(local-defthmd approx-error-2
  (implies (and (not (specialp))
                (not (zp j))
		(= (mod j 3) 2))
	   (equal (rs6 j)
	          (bits (- (bits (rp j) 56 51) (bits (rn j) 56 51)) 5 0)))
  :hints (("Goal" :expand ((rs6 j) (rp j) (rn j)) :in-theory (enable lognot iter1))))

(local-defthmd approx-error-3
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod (1+ j) 3) 0))
	   (equal (rems6 (+ 1 j))
	          (mod (- (bits (rp j) 56 51) (bits (rn j) 56 51)) 64)))
  :hints (("Goal" :expand ((:free (x) (bits x 5 0))) :in-theory (enable hyp approx-error-2 rems6))))

(local-defun x* (j) (- (bits (rp j) 56 0) (bits (rn j) 56 0)))

(local-defun y* (j) (* (expt 2 51) (- (bits (rp j) 56 51) (bits (rn j) 56 51))))

(local-defthmd approx-error-4
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (<= (abs (* (expt 2 56) (r j)))
	       (* 3 (expt 2 54))))
  :hints (("Goal" :in-theory (enable hyp) :use (d-bounds))))

(local-defthmd approx-error-5
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (mod (* (expt 2 56) (r j)) (expt 2 59))
	          (mod (- (rp j) (rn j)) (expt 2 59))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd approx-error-6
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (and (bvecp (rp j) 59)
	        (bvecp (rn j) 59)))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd approx-error-7
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (mod (* (expt 2 56) (r j)) (expt 2 57))
	          (mod (- (rp j) (rn j)) (expt 2 57))))
  :hints (("Goal" :use (approx-error-5 approx-error-6
                        (:instance mod-of-mod-cor (a 59) (b 57) (x (* (expt 2 56) (r j))))
                        (:instance mod-of-mod-cor (a 59) (b 57) (x (- (rp j) (rn j))))))))

(local-defthmd approx-error-8
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (mod (- (rp j) (rn j)) (expt 2 57))
	          (mod (x* j) (expt 2 57))))
  :hints (("Goal" :use (approx-error-6
                        (:instance mod-sum (a (- (mod (rn j) (expt 2 57)))) (b (rp j)) (n (expt 2 57)))
                        (:instance mod-diff (a (rp j)) (b (rn j)) (n (expt 2 57))))
		  :expand ((:free (x) (bits x 56 0))))))

(local-defthmd approx-error-9
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (mod (x* j) (expt 2 57))
	          (mod (* (expt 2 56) (r j)) (expt 2 57))))
  :hints (("Goal" :use (approx-error-7 approx-error-8))))

(local-defthmd approx-error-10
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (si (mod (x* j) (expt 2 57)) 57)
	          (* (expt 2 56) (r j))))
  :hints (("Goal" :use (approx-error-4 approx-error-6 approx-error-9 (:instance si-bits (x (* (expt 2 56) (r j))) (n 57)))
		  :expand ((:free (x) (bits x 56 0))))))

(local-defthmd approx-error-11
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(or (= (mod (1+ j) 3) 2)
		    (= (mod (1+ j) 3) 0)))
	   (equal (mod (y* j) (expt 2 57))
	          (mod (* (expt 2 51) (rems6 (1+ j))) (expt 2 57))))
  :hints (("Goal" :use (approx-error-1 approx-error-3 approx-error-6
                        (:instance mod-prod (k (expt 2 51)) (m (- (bits (rp j) 56 51) (bits (rn j) 56 51))) (n 64))
                        (:instance mod-prod (k (expt 2 51)) (m (rems6 (1+ j))) (n 64))))))

(local-defthmd approx-error-12
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (< (abs (- (x* j) (y* j)))
	      (expt 2 51)))
  :hints (("Goal" :use (approx-error-6
                        (:instance bits-plus-bits (x (rp j)) (n 56) (p 51) (m 0))
                        (:instance bits-plus-bits (x (rn j)) (n 56) (p 51) (m 0))
                        (:instance bits-bounds (x (rp j)) (i 50) (j 0))
                        (:instance bits-bounds (x (rn j)) (i 50) (j 0))))))

(local-in-theory (disable bvecp-rems6))

(local-defthmd approx-error-13
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(or (= (mod (1+ j) 3) 2)
		    (= (mod (1+ j) 3) 0)))
	   (< (abs (- (* (expt 2 56) (r j))
	              (si (* (expt 2 51) (rems6 (1+ j))) 57)))
	      (expt 2 51)))
  :hints (("Goal" :use (approx-error-4 approx-error-12 approx-error-10 approx-error-11 approx-error-6
                        (:instance bvecp-rems6 (j (1+ j)))
                        (:instance si-approx (x (x* j)) (y (y* j)) (n 57))))))

(local-defthmd approx-error-14
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(or (= (mod (1+ j) 3) 2)
		    (= (mod (1+ j) 3) 0)))
	   (< (abs (- (* (expt 2 56) (r j))
	              (* (expt 2 51) (si (rems6 (1+ j)) 6))))
	      (expt 2 51)))
  :hints (("Goal" :use (approx-error-13
                        (:instance bvecp-rems6 (j (1+ j)))
			(:instance si-shift (r (rems6 (1+ j))) (k 51) (n 6))))))

(local-defthmd approx-error-15
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(or (= (mod (1+ j) 3) 2)
		    (= (mod (1+ j) 3) 0)))
	   (< (abs (- (* 4 (r j)) (approx (1+ j))))
	      1/8))
  :hints (("Goal" :use (approx-error-6 approx-error-14 (:instance bvecp-rems6 (j (1+ j))))
                  :in-theory (enable approx)
                  :nonlinearp t)))

(local-defund r* (j) (- (* 4 (rp j)) (* 4 (rn j))))

(local-defund rt* (j) (* (expt 2 50) (- (bits (rp j) 58 48) (bits (rn j) 58 48))))

(local-in-theory (disable (r*) (rt*)))

(local-defthmd approx-error-16
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j)))
	   (equal (mod (* (expt 2 56) (r (1- j))) (expt 2 59)) (mod (- (rp (1- j)) (rn (1- j))) (expt 2 59))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd approx-error-17
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j)))
	   (and (bvecp (rp (1- j)) 59)
	        (bvecp (rn (1- j)) 59)))
  :hints (("Goal" :in-theory (enable hyp))))

(in-theory (disable ACL2::MOD-THEOREM-ONE-B))

(local-defthm int-r-1
  (implies (and (not (specialp))
                (not (zp j)))
           (and (integerp (* (expt 2 56) (d)))
                (integerp (* (expt 4 (1- j)) (quot j)))))
  :hints (("Goal" :use (int-quot bvecp-div div-rewrite))))

(local-defthm int-r-2
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (* (* (expt 2 56) (d))
                     (* (expt 4 (1- j)) (quot j)))
                  (* (D) (QUOT J) (EXPT 2 (+ 54 (* 2 J))))))
  :hints (("Goal" :use (int-quot bvecp-div div-rewrite))))

(local-defthmd int-r-3
  (implies (and (integerp m) (integerp n))
           (integerp (* m n))))

(local-defthmd int-r-4
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (D) (QUOT J) (EXPT 2 (+ 54 (* 2 J))))))
  :hints (("Goal" :use (int-r-1 int-r-2 (:instance int-r-3 (m (* (expt 2 56))) (n (* (expt 4 (1- j)) (quot j)))))
                  :in-theory (theory 'minimal-theory))))

(local-defthmd int-r-5
  (implies (and (not (specialp))
                (not (zp j)))
           (and (integerp (expt 4 (1- j)))
	        (integerp (* (expt 2 56) (x)))))
  :hints (("Goal" :in-theory (enable bvecp rp-1-rewrite)
                  :use (int-r-4 bvecp-rp-1))))

(local-defthmd int-r-6
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (* (expt 4 (1- j)) (* (expt 2 56) (x)))
	          (* (X) (EXPT 2 (+ 54 (* 2 J)))))))

(local-defthmd int-r-7
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (X) (EXPT 2 (+ 54 (* 2 J))))))
  :hints (("Goal" :use (int-r-5 int-r-6 (:instance int-r-3 (m (expt 4 (1- j))) (n (* (expt 2 56) (x)))))
                  :in-theory (theory 'minimal-theory))))

(defthmd int-r
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (expt 2 56) (r j))))
  :hints (("Goal" :expand ((:free (j) (r j)))
                  :use (int-r-4 int-r-7))))

(local-defthmd approx-error-18
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(= (mod (1+ j) 3) 1))
	   (equal (mod (* (expt 2 58) (r (1- j))) (expt 2 59))
	          (mod (r* (1- j)) (expt 2 59))))
  :hints (("Goal" :in-theory (enable r*)
                  :use (approx-error-16  approx-error-17
		        (:instance int-r (j (1- j)))
		        (:instance mod-mod-times (a (* (expt 2 56) (r (1- j)))) (b 4) (n (expt 2 59)))
		        (:instance mod-mod-times (a (- (rp (1- j)) (rn (1- j)))) (b 4) (n (expt 2 59)))))))

(local-defthmd approx-error-19
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(= (mod (1+ j) 3) 1))
	   (equal (- (r* (1- j)) (rt* (1- j)))
	          (* 4 (- (bits (rp (1- j)) 47 0) (bits (rn (1- j)) 47 0)))))
  :hints (("Goal" :in-theory (enable r* rt*)
                  :use (approx-error-17
		        (:instance bits-plus-bits (x (rp (1- j))) (n 58) (p 48) (m 0))
		        (:instance bits-plus-bits (x (rn (1- j))) (n 58) (p 48) (m 0))))))

(local-defthmd approx-error-20
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(= (mod (1+ j) 3) 1))
	   (< (abs (- (r* (1- j)) (rt* (1- j))))
	      (expt 2 50)))
  :hints (("Goal" :use (approx-error-17 approx-error-19
                        (:instance bits-bounds (x (rp (1- j))) (i 47) (j 0))
                        (:instance bits-bounds (x (rn (1- j))) (i 47) (j 0))))))

(local-defund d* (j) (- (* (q j) (div))))

(local-defund dt* (j)
  (if (<= (q j) 0)
      (- (* (q j) (div)))
    (- (1+ (* (q j) (div))))))

(local-defthmd approx-error-21
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(= (q j) 0))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           1)
			6 0)))
  :hints (("Goal" :expand ((rs7 j) (q j))
                  :in-theory (enable iter2))))

(local-defthmd approx-error-22
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(= (q j) -1))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (bits (div) 56 50)
		           1)
			6 0)))
  :hints (("Goal" :expand ((rs7 j) (q j))
                  :in-theory (enable iter2))))

(local-defthmd approx-error-23
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(= (q j) -2))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (bits (div) 55 49)
		           1)
			6 0)))
  :hints (("Goal" :expand ((rs7 j) (q j))
                  :in-theory (enable iter2))))

(local-defthmd approx-error-24
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(= (q j) 1))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (1- (- (expt 2 7) (bits (div) 56 50)))
		           1)
			6 0)))
  :hints (("Goal" :expand ((rs7 j) (q j))
                  :in-theory (enable bits-lognot iter2))))

(local-defthmd approx-error-25
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(= (q j) 2))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (1- (- (expt 2 7) (bits (div) 55 49)))
		           1)
			6 0)))
  :hints (("Goal" :expand ((rs7 j) (q j))
                  :in-theory (enable bits-lognot iter2))))

(local-defthmd approx-error-26
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(<= (q j) 0))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (bits (dt* j) 56 50)
		           1)
			6 0)))
  :hints (("Goal" :use (q-vals bvecp-div (:instance bits-shift-up-1 (x (div)) (k 1) (i 56) (j 50)))
                  :in-theory (enable d* dt* approx-error-21 approx-error-22 approx-error-23))))

(local-defthmd approx-error-27
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(<= (q j) 0))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (mod (fl (/ (dt* j) (expt 2 50))) (expt 2 7))
		           1)
			6 0)))
  :hints (("Goal" :use (bvecp-div q-vals (:instance bits-mod-fl (x (dt* j)) (i 57) (j 50)))
                  :in-theory (enable dt* approx-error-26))))

(local-defthmd approx-error-28
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (1- (- (expt 2 7) (bits (* (q j) (div)) 56 50)))
		           1)
			6 0)))
  :hints (("Goal" :use (q-vals bvecp-div (:instance bits-shift-up-1 (x (div)) (k 1) (i 56) (j 50)))
                  :in-theory (enable d* dt* approx-error-24 approx-error-25))))

(local-defthmd approx-error-29
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (- (expt 2 7) (mod (fl (/ (- (1+ (dt* j))) (expt 2 50))) (expt 2 7))))
			6 0)))
  :hints (("Goal" :use (q-vals bvecp-div (:instance bits-mod-fl (x (* (q j) (div))) (i 57) (j 50)))
                  :in-theory (enable dt* approx-error-28))))

(local-defthmd approx-error-30
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (fl (/ (- (1+ (dt* j))) (expt 2 50)))
	          (- (1+ (fl (/ (dt* j) (expt 2 50)))))))
  :hints (("Goal" :use (bvecp-div (:instance fl-m-n (m (1+ (dt* j))) (n (expt 2 50))))
                  :in-theory (enable dt*))))

(local-defthmd approx-error-31
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (bits (+ (bits (rs9 (1- j)) 6 0)
		           (- (expt 2 7) (mod (- (1+ (fl (/ (dt* j) (expt 2 50))))) (expt 2 7))))
			6 0)))
  :hints (("Goal" :use (approx-error-29 approx-error-30)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd approx-error-32
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 2))
	   (equal (rs9 j)
	          (mod (- (BITS (rp j) 56 48) (BITS (rn j) 56 48))
		       (expt 2 9))))
  :hints (("Goal" :expand ((rs9 j) (:free (x) (bits x 8 0)))
                  :in-theory (enable iter1 rp rn lognot))))

(local-defthmd approx-error-33
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (BITS (rp j) 56 48)
	          (mod (BITS (rp j) 58 48) (expt 2 9))))
  :hints (("Goal" :use (approx-error-6
                        (:instance bits-bits (x (rp j)) (i 58) (j 48) (k 8) (l 0)))
		  :in-theory (disable bits-bits)
                  :expand ((:free (x) (bits x 8 0))))))

(local-defthmd approx-error-34
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (BITS (rn j) 56 48)
	          (mod (BITS (rn j) 58 48) (expt 2 9))))
  :hints (("Goal" :use (approx-error-6
                        (:instance bits-bits (x (rn j)) (i 58) (j 48) (k 8) (l 0)))
		  :in-theory (disable bits-bits)
                  :expand ((:free (x) (bits x 8 0))))))

(local-defthmd approx-error-35
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 2))
	   (equal (rs9 j)
	          (mod (- (mod (BITS (rp j) 58 48) (expt 2 9))
		          (mod (BITS (rn j) 58 48) (expt 2 9)))
		       (expt 2 9))))
  :hints (("Goal" :use (approx-error-32 approx-error-33 approx-error-34))))

(local-defthmd approx-error-36
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 2))
	   (equal (rs9 j)
	          (mod (* (expt 2 -50) (rt* j))
		       (expt 2 9))))
  :hints (("Goal" :use (approx-error-6
                        (:instance mod-sum (b (BITS (rp j) 58 48)) (a (- (mod (BITS (rn j) 58 48) (expt 2 9)))) (n (expt 2 9)))
			(:instance mod-diff (a (BITS (rp j) 58 48)) (b (BITS (rn j) 58 48)) (n (expt 2 9))))
		  :in-theory (enable rt* approx-error-35))))

(local-defthmd approx-error-37
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(= (mod j 3) 2))
	   (integerp (rs9 j)))
  :hints (("Goal" :in-theory (enable rt* approx-error-36))))

(local-defthmd approx-error-38
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(= (mod j 3) 0))
	   (integerp (rs9 (1- j))))
  :hints (("Goal" :use ((:instance approx-error-37 (j (1- j)))
                        (:instance mod-sum (b j) (a -1) (n 3))))))

(local-defthmd approx-error-39
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(<= (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (mod (rs9 (1- j)) (expt 2 7))
		          (mod (fl (/ (dt* j) (expt 2 50))) (expt 2 7))
		           1)
		       (expt 2 7))))
  :hints (("Goal" :expand ((:free (x) (bits x 6 0)))
                  :use (approx-error-38)
		  :in-theory (enable dt* approx-error-27))))

(local-defthmd approx-error-40
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(<= (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (rs9 (1- j))
		          (mod (fl (/ (dt* j) (expt 2 50))) (expt 2 7))
		           1)
		       (expt 2 7))))
  :hints (("Goal" :use (approx-error-38
                        (:instance mod-sum (b (rs9 (1- j))) (a (1+ (mod (fl (/ (dt* j) (expt 2 50))) (expt 2 7)))) (n (expt 2 7))))
		  :in-theory (enable dt* approx-error-39))))

(local-defthmd approx-error-41
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(<= (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (rs9 (1- j))
		          (fl (/ (dt* j) (expt 2 50)))
		           1)
		       (expt 2 7))))
  :hints (("Goal" :use (approx-error-38
                        (:instance mod-sum (b (fl (/ (dt* j) (expt 2 50)))) (a (1+ (rs9 (1- j)))) (n (expt 2 7))))
		  :in-theory (enable dt* approx-error-40))))

(local-defthmd approx-error-42
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (mod (rs9 (1- j)) 128)
		           (- (expt 2 7) (mod (- (1+ (fl (/ (dt* j) (expt 2 50))))) (expt 2 7))))
		       128)))
  :hints (("Goal" :use (approx-error-38)
                  :expand ((:free (x) (bits x 6 0)))
                  :in-theory (enable approx-error-31 dt*))))

(local-defthmd approx-error-43
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (rs9 (1- j))
		           (- (expt 2 7) (mod (- (1+ (fl (/ (dt* j) (expt 2 50))))) (expt 2 7))))
		       128)))
  :hints (("Goal" :use (approx-error-38
                        (:instance mod-sum (b (rs9 (1- j)))
			                   (a (- (expt 2 7) (mod (- (1+ (fl (/ (dt* j) (expt 2 50))))) (expt 2 7))))
					   (n (expt 2 7))))
                  :in-theory (enable approx-error-42 dt*))))

(local-defthmd approx-error-44
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (rs9 (1- j))
		          (expt 2 7)
			  (1+ (fl (/ (dt* j) (expt 2 50)))))
		       128)))
  :hints (("Goal" :use (approx-error-38
                        (:instance mod-diff (b (- (1+ (fl (/ (dt* j) (expt 2 50))))))
			                    (a (+ (expt 2 7) (rs9 (1- j))))
					    (n (expt 2 7))))
                  :in-theory (enable approx-error-43 dt*))))

(local-defthmd approx-error-45
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0)
		(> (q j) 0))
	   (equal (rs7 j)
	          (mod (+ (rs9 (1- j))
			  (1+ (fl (/ (dt* j) (expt 2 50)))))
		       128)))
  :hints (("Goal" :use (approx-error-38
                        (:instance mod-mult (m (+ (rs9 (1- j)) (1+ (fl (/ (dt* j) (expt 2 50))))))
			                    (a 1)
					    (n (expt 2 7))))
                  :in-theory (enable approx-error-44 dt*))))

(local-defthmd approx-error-46
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (rs7 j)
	          (mod (+ (rs9 (1- j))
		          (fl (/ (dt* j) (expt 2 50)))
		          1)
		       (expt 2 7))))
  :hints (("Goal" :use (approx-error-41 approx-error-45))))

(local-defthmd approx-error-47
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(= (mod j 3) 0))
	   (equal (rs9 (+ -1 j))
	          (mod (* (expt 2 -50) (rt* (1- j)))
		       (expt 2 9))))
  :hints (("Goal" :use ((:instance mod-sum (b j) (a -1) (n 3)))
		  :in-theory (enable rt* approx-error-36)))) 

(local-defthmd approx-error-48
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (rs7 j)
	          (mod (+ (mod (mod (* (expt 2 -50) (rt* (1- j)))
		                    (expt 2 9))
			       128)
		          (fl (/ (dt* j) (expt 2 50)))
		          1)
		       (expt 2 7))))
  :hints (("Goal" :in-theory (enable dt* approx-error-47 approx-error-46)
                  :use (bvecp-div
		        (:instance mod-sum (b (mod (* (expt 2 -50) (rt* (1- j))) (expt 2 9)))
		                           (a (1+ (fl (/ (dt* j) (expt 2 50)))))
					   (n 128))))))

(local-defthmd approx-error-49
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (rs7 j)
	          (mod (+ (mod (* (expt 2 -50) (rt* (1- j))) 128)
		          (fl (/ (dt* j) (expt 2 50)))
		          1)
		       (expt 2 7))))
  :hints (("Goal" :in-theory (enable dt* approx-error-48)
                  :use (bvecp-div
		        (:instance mod-of-mod-cor (x (* (expt 2 -50) (rt* (1- j)))) (a 9) (b 7))))))

(local-defthmd approx-error-50
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (rs7 j)
	          (mod (+ (* (expt 2 -50) (rt* (1- j)))
		          (fl (/ (dt* j) (expt 2 50)))
		          1)
		       (expt 2 7))))
  :hints (("Goal" :in-theory (enable dt* approx-error-49)
                  :use (bvecp-div
		        (:instance mod-sum (b (* (expt 2 -50) (rt* (1- j)))) (a (1+ (fl (/ (dt* j) (expt 2 50))))) (n 128))))))

(local-defthmd approx-error-51
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (integerp (* (expt 2 -50) (rt* (1- j)))))
  :hints (("Goal" :in-theory (enable rt*)
                  :use (approx-error-17))))

(local-defthmd approx-error-52
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (* (expt 2 -50) (rt* (1- j)))
	          (+ (* 2 (fl (* (expt 2 -51) (rt* (1- j)))))
		     (bitn (rt* (1- j)) 50))))
  :hints (("Goal" :use (approx-error-51 (:instance mod-def (x (* (expt 2 -50) (rt* (1- j)))) (y 2)))
                  :in-theory (enable bitn-def))))

(local-defthmd approx-error-53
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (fl (/ (dt* j) (expt 2 50)))
	          (+ (* 2 (fl (* (expt 2 -51) (dt* j))))
		     (bitn (dt* j) 50))))
  :hints (("Goal" :use (bvecp-div (:instance fl/int-rewrite (x (/ (dt* j) (expt 2 50))) (n 2))
                        (:instance mod-def (x (fl (/ (dt* j) (expt 2 50)))) (y 2)))
                  :in-theory (enable dt* bitn-def))))

(local-defthmd approx-error-54
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod j 3) 0))
	   (equal (rs7 j)
	          (mod (+ (* 2 (fl (* (expt 2 -51) (rt* (1- j)))))
		          (bitn (rt* (1- j)) 50)
		          (* 2 (fl (* (expt 2 -51) (dt* j))))
  		          (bitn (dt* j) 50)
		          1)
		       (expt 2 7))))
  :hints (("Goal" :in-theory (enable approx-error-50)
                  :use (approx-error-52 approx-error-53))))

(local-defthmd approx-error-55
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
	   (equal (rems6 (+ 1 j))
	          (mod (fl (+ (fl (* (expt 2 -51) (rt* (1- j))))
                              (fl (* (expt 2 -51) (dt* j)))
		              (/ (+ (bitn (rt* (1- j)) 50)
  		                    (bitn (dt* j) 50)
		                    1)
			         2)))
		       (expt 2 6))))
  :hints (("Goal" :in-theory (enable rems6 approx-error-54)
                  :use ((:instance mod-sum (b (1+ j)) (a -1) (n 3))
		        (:instance bits-mod-fl (x (mod (+ (* 2 (fl (* (expt 2 -51) (rt* (1- j)))))
		                                          (bitn (rt* (1- j)) 50)
		                                          (* 2 (fl (* (expt 2 -51) (dt* j))))
  		                                          (bitn (dt* j) 50)
		                                          1)
						       128))
					       (i 7)
					       (j 1))
			(:instance fl-mod (a (+ (* 2 (fl (* (expt 2 -51) (rt* (1- j)))))
		                                (bitn (rt* (1- j)) 50)
		                                (* 2 (fl (* (expt 2 -51) (dt* j))))
  		                                (bitn (dt* j) 50)
		                                1))
					  (m 64)
					  (n 2))))))

(local-defthmd approx-error-56
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
	   (equal (rems6 (+ 1 j))
	          (mod (+ (fl (* (expt 2 -51) (rt* (1- j))))
                          (fl (* (expt 2 -51) (dt* j)))
		          (fl (/ (+ (bitn (rt* (1- j)) 50)
  		                    (bitn (dt* j) 50)
		                    1)
			         2)))
		       (expt 2 6))))
  :hints (("Goal" :in-theory (enable approx-error-55)
                  :use ((:instance fl+int-rewrite (x (/ (+ (bitn (rt* (1- j)) 50) (bitn (dt* j) 50) 1) 2))
		                                  (n (+ (fl (* (expt 2 -51) (rt* (1- j)))) (fl (* (expt 2 -51) (dt* j))))))))))

(local-defund s* (j)
  (if (and (= (bitn (rt* (1- j)) 50) 0)
           (= (bitn (dt* j) 50) 0))
      (+ (fl (* (expt 2 -51) (rt* (1- j))))
         (fl (* (expt 2 -51) (dt* j))))
    (+ (fl (* (expt 2 -51) (rt* (1- j))))
       (fl (* (expt 2 -51) (dt* j)))
       1)))

(local-in-theory (disable (s*)))

(local-defthmd approx-error-57
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
	   (equal (rems6 (+ 1 j))
	          (mod (s* j) 64)))
  :hints (("Goal" :in-theory (enable approx-error-56 s*)
                  :use ((:instance bitn-0-1 (x (rt* (1- j))) (n 50))
		        (:instance bitn-0-1 (x (dt* j)) (n 50))))))

(local-defun x! (j) (+ (r* (1- j)) (d* j)))

(local-defun y! (j) (* (expt 2 51) (s* j)))

(local-defthmd approx-error-58
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (mod (x! j) (expt 2 59))
	          (mod (- (* (expt 2 58) (r (1- j))) (* (expt 2 56) (q j) (d))) (expt 2 59))))
  :hints (("Goal" :in-theory (e/d (x! d* div-rewrite) (ACL2::PREFER-POSITIVE-ADDENDS-<))
                  :use (q-vals approx-error-18
		        (:instance mod-sum (b (* (expt 2 58) (r (1- j)))) (a (- (* (q j) (div)))) (n (expt 2 59)))
			(:instance mod-sum (b (r* (1- j))) (a (- (* (q j) (div)))) (n (expt 2 59)))))))

(local-defthmd approx-error-59
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (- (* (expt 2 58) (r (1- j))) (* (expt 2 56) (q j) (d)))
	          (* (expt 2 56) (r j))))
  :hints (("Goal" :use (q-vals
		        (:instance r-recurrence (j (1- j)))))))

(local-defthmd approx-error-60
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (mod (x! j) (expt 2 59))
	          (mod (* (expt 2 56) (r j)) (expt 2 59))))
  :hints (("Goal" :use (approx-error-58 approx-error-59)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd approx-error-61
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (mod (x! j) (expt 2 57))
	          (mod (* (expt 2 56) (r j)) (expt 2 57))))
  :hints (("Goal" :use (approx-error-60
                        (:instance mod-of-mod-cor (x (x! j)) (a 59) (b 57))
			(:instance mod-of-mod-cor (x (* (expt 2 56) (r j))) (a 59) (b 57))))))

(local-defthmd approx-error-62
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (si (mod (x! j) (expt 2 57)) 57)
	          (* (expt 2 56) (r j))))
  :hints (("Goal" :in-theory (enable bits-mod)
	          :use (int-r approx-error-4 approx-error-61 (:instance si-bits (x (* (expt 2 56) (r j))) (n 57))))))

(local-defthmd approx-error-63
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (bvecp (mod (s* j) 64) 6))
  :hints (("Goal" :in-theory (enable bvecp s*))))

(local-defthmd approx-error-64
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (si (mod (y! j) (expt 2 57)) 57)
	          (* (expt 2 51) (si (rems6 (1+ j)) 6))))
  :hints (("Goal" :in-theory (enable approx-error-57 y!)
                  :use (approx-error-63
		        (:instance mod-prod (k (expt 2 51)) (m (s* j)) (n 64))
		        (:instance si-shift (r (rems6 (1+ j))) (k 51) (n 6))))))

(local-defthmd approx-error-65
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (- (+ (rt* (1- j)) (dt* j))
	             (* (expt 2 51) (s* j)))
		  (if (and (= (bitn (rt* (1- j)) 50) 0)
                           (= (bitn (dt* j) 50) 0))
		      (+ (mod (rt* (1- j)) (expt 2 51))
		         (mod (dt* j) (expt 2 51)))
                    (+ (mod (rt* (1- j)) (expt 2 51))
		       (mod (dt* j) (expt 2 51))
		       (- (expt 2 51))))))
  :hints (("Goal" :in-theory (enable s*)
                  :use ((:instance mod-def (x (rt* (1- j))) (y (expt 2 51)))
		        (:instance mod-def (x (dt* j)) (y (expt 2 51)))))))

(local-defthmd approx-error-66
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (- (+ (rt* (1- j)) (dt* j))
	             (* (expt 2 51) (s* j)))
		  (if (and (= (bitn (rt* (1- j)) 50) 0)
                           (= (bitn (dt* j) 50) 0))
		      (+ (bits (rt* (1- j)) 50 0)
		         (bits (dt* j) 50 0))
                    (+ (bits (rt* (1- j)) 50 0)
		       (bits (dt* j) 50 0)
		       (- (expt 2 51))))))
  :hints (("Goal" :in-theory (enable dt* bits-mod)
                  :use (bvecp-div q-vals approx-error-65))))

(local-defthmd approx-error-67
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (bits (rt* (1- j)) 49 0) 0))
  :hints (("Goal" :in-theory (enable bits rt*))))

(local-defthmd approx-error-68
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (and (< (- (+ (rt* (1- j)) (dt* j))
	              (* (expt 2 51) (s* j)))
	           (expt 2 50))
		(>= (- (+ (rt* (1- j)) (dt* j))
	               (* (expt 2 51) (s* j)))
		    (- (expt 2 50)))))
  :hints (("Goal" :use (approx-error-66 approx-error-67
                        (:instance bitn-0-1 (x (rt* (1- j))) (n 50))
                        (:instance bitn-0-1 (x (dt* j)) (n 50))
			(:instance bits-bounds (x (dt* j)) (i 49) (j 0))
			(:instance bitn-plus-bits (x (rt* (1- j))) (n 50) (m 0))
			(:instance bitn-plus-bits (x (dt* j)) (n 50) (m 0))))))

(local-defthmd approx-error-69
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (< (abs (- (x! j) (y! j)))
	      (expt 2 51)))
  :hints (("Goal" :use (bvecp-div q-vals approx-error-68 approx-error-20)
                  :in-theory (enable d* dt*))))

(local-defthmd approx-error-70
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (integerp (x! j)))
  :hints (("Goal" :in-theory (enable d* r*)
                  :use (approx-error-17 q-vals bvecp-div))))

(local-defthmd approx-error-71
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (integerp (y! j)))
  :hints (("Goal" :in-theory (enable s*))))

(local-defthmd approx-error-72
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (< (abs (si (mod (x! j) (expt 2 57)) 57))
	      (- (expt 2 56) (abs (- (x! j) (y! j))))))
  :hints (("Goal" :use (approx-error-4 approx-error-62 approx-error-64 approx-error-69 approx-error-70 approx-error-71))))

(local-defthmd approx-error-73
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (equal (- (* (expt 2 56) (r j))
	             (* (expt 2 51) (si (rems6 (1+ j)) 6)))
		  (- (x! j) (y! j))))
  :hints (("Goal" :use (approx-error-4 approx-error-62 approx-error-64 approx-error-70 approx-error-71 approx-error-72
                        (:instance si-approx (x (x! j)) (y (y! j)) (n 57))))))

(local-defthmd approx-error-74
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
           (< (abs (- (* (expt 2 56) (r j))
	              (* (expt 2 51) (si (rems6 (1+ j)) 6))))
	      (expt 2 51)))
  :hints (("Goal" :use (approx-error-69 approx-error-73))))

(local-defthmd approx-error-75
  (implies (and (not (specialp))
                (not (zp j))
		(hyp (1- j))
		(hyp j)
		(= (mod (1+ j) 3) 1))
	   (< (abs (- (* 4 (r j)) (approx (1+ j))))
	      1/8))
  :hints (("Goal" :use (approx-error-74 (:instance bvecp-rems6 (j (1+ j))))
                  :in-theory (enable approx)
                  :nonlinearp t)))

(local-defthmd approx-error
  (implies (and (not (specialp))
                (not (zp j))
		(or (= j 1) (hyp (1- j)))
		(hyp j))
	   (< (abs (- (* 4 (r j)) (approx (1+ j))))
	      1/8))
  :hints (("Goal" :use (approx-error-75 approx-error-15))))

(local-defthmd int-approx8
  (implies (and (not (specialp))
                (not (zp j))
		(or (= j 1) (hyp (1- j)))
		(hyp j))
	   (and (rationalp (approx (1+ j)))
	        (integerp (* 8 (approx (1+ j))))))
  :hints (("Goal" :in-theory (enable approx si rs6 iter1 rems6))))

(local-defthmd hyp-r-bound
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (<= (abs (r j)) (* 2/3 (d))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd r-bound-induct
  (implies (and (not (specialp))
                (not (zp j))
		(or (= j 1) (hyp (1- j)))
		(hyp j))
	   (<= (abs (r (1+ j)))
	       (* 2/3 (d))))
  :hints (("Goal" :use (approx-error int-approx8 hyp-r-bound
                        (:instance q-maxk (j (1+ j)))
			(:instance r-bound-inv (approx (approx (1+ j))))))))

(local-defthmd rp-rewrite-1
  (implies (and (natp j) (> j 1))
           (equal (rp j) (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (div) (q j) (fnum))))))
  :hints (("Goal" :in-theory (enable rp rn q iter1 iter2 iter3))))

(local-defthmd rn-rewrite-1
  (implies (and (natp j) (> j 1))
           (equal (rn j) (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (div) (q j) (fnum))))))
  :hints (("Goal" :in-theory (enable rp rn q iter1 iter2 iter3))))

(local-defund divmult (j)
  (case (q j)
    (2 (bits (lognot (bits (ash (div) 1) 58 0)) 58 0))
    (1 (bits (lognot (div)) 58 0))
    (0 (bits 0 58 0))
    (-1 (div))
    (-2 (bits (ash (div) 1) 58 0))
    (t (div))))

(local-defund rp4 (j) (bits (ash (rp (1- j)) 2) 58 0))

(local-defund rn4 (j) (bits (ash (rn (1- j)) 2) 58 0))

(local-defund sum (j)
  (logxor (logxor (rn4 j) (rp4 j)) (divmult j)))

(local-defund carry-0 (j)
  (logior (logand (bits (lognot (rn4 j)) 58 0) (rp4 j))
          (logand (logior (bits (lognot (rn4 j)) 58 0) (rp4 j))
                  (divmult j))))
		  
(local-defund carry (j) (bits (ash (carry-0 j) 1) 58 0))

(local-defund rp* (j)
  (case (fnum)
    (2 (setbitn (carry j) 59 0 (log> (q j) 0)))
    (1 (setbitn (setbits (rp (1- j)) 59 58 29 (bits (carry j) 58 29)) 59 29 (log> (q j) 0)))
    (0 (setbitn (setbits (rp (1- j)) 59 58 42 (bits (carry j) 58 42)) 59 42 (log> (q j) 0)))
    (t (rp (1- j)))))

(local-defund rn* (j)
  (case (fnum)
    (2 (sum j))
    (1 (setbits (rn (1- j)) 59 58 29 (bits (sum j) 58 29)))
    (0 (setbits (rn (1- j)) 59 58 42 (bits (sum j) 58 42)))
    (t (rn (1- j)))))

(local-in-theory (disable divmult rp4 rn4 sum carry-0 carry rp* rn*))

(local-defthmd nextrem-lemma
  (implies (and (natp j) (> j 1))
           (and (equal (rp j) (rp* j))
	        (equal (rn j) (rn* j))))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(divmult rp4 rn4 sum carry-0 carry rp* rn* rp-rewrite-1 rn-rewrite-1 nextrem))))

(local-defthmd bits-sigb-0
  (implies (not (specialp))
           (equal (bits (sigb) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bits)
                  :use (p-vals exactp-sigb
                        (:instance mod-def (x (sigb)) (y (expt 2 (- 53 (p)))))))))

(local-defthmd bits-div1-0
  (implies (not (specialp))
           (equal (bits (div1) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bvecp div1 ash)
                  :use (p-vals exactp-sigb bits-sigb-0
                        (:instance bits-shift-up-2 (x (sigb)) (k 1) (i (- 51 (p))))			
                        (:instance bits-shift-up-2 (x (sigb)) (k 2) (i (- 50 (p))))
			(:instance bitn-plus-bits (x (sigb)) (n (- 51 (p))) (m 0))
			(:instance bitn-plus-bits (x (sigb)) (n (- 52 (p))) (m 0))))))

(local-defthmd bits-div2-0
  (implies (not (specialp))
           (equal (bits (div2) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bvecp div2 ash)
                  :use (p-vals exactp-sigb bits-sigb-0
                        (:instance bits-shift-up-2 (x (sigb)) (k 1) (i (- 51 (p))))			
                        (:instance bits-shift-up-2 (x (sigb)) (k 2) (i (- 50 (p))))
			(:instance bitn-plus-bits (x (sigb)) (n (- 51 (p))) (m 0))
			(:instance bitn-plus-bits (x (sigb)) (n (- 52 (p))) (m 0))))))

(local-defthmd bits-div3-0
  (implies (not (specialp))
           (equal (bits (div3) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bvecp div3 ash)
                  :use (p-vals exactp-sigb bits-sigb-0
                        (:instance bits-shift-up-2 (x (sigb)) (k 3) (i (- 49 (p))))
			(:instance bitn-plus-bits (x (sigb)) (n (- 51 (p))) (m 0))
			(:instance bitn-plus-bits (x (sigb)) (n (- 52 (p))) (m 0))
			(:instance bitn-plus-bits (x (sigb)) (n (- 50 (p))) (m 0))))))

(local-defthmd bits-divsum-0
  (implies (not (specialp))
           (equal (bits (divsum) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable divsum bits-logxor)
                  :use (p-vals bits-div1-0 bits-div2-0 bits-div3-0))))

(local-defund divcar-0 ()
  (logior (logior (logand (div1) (div2))
                  (logand (div1) (div3)))
          (logand (div2) (div3))))

(local-in-theory (disable (divcar-0)))

(local-defthmd bits-divcar-1
  (implies (not (specialp))
           (equal (bits (divcar-0) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable ash divcar-0 bits-logior bits-logand)
                  :use (p-vals bits-div1-0 bits-div2-0 bits-div3-0))))

(local-defthmd bits-divcar-2
  (implies (not (specialp))
           (equal (divcar) (bits (* 2 (divcar-0)) 55 0)))
  :hints (("Goal" :in-theory (enable ash divcar divcar-0))))

(local-defthmd bits-divcar-3
  (implies (not (specialp))
           (equal (bits (divcar) (- 53 (p)) 0) (bits (* 2 (divcar-0)) (- 53 (p)) 0)))
  :hints (("Goal" :in-theory (enable bitn-bits bits-divcar-2) :use (p-vals))))

(local-defthmd bits-divcar-4
  (implies (not (specialp))
           (equal (bits (* 2 (divcar-0)) (- 53 (p)) 0) 0))
  :hints (("Goal" :use (p-vals bits-divcar-1
                        (:instance bits-shift-up-2 (x (divcar-0)) (k 1) (i (- 52 (p))))))))

(local-defthmd bits-divcar-5
  (implies (not (specialp))
           (equal (bits (divcar) (- 53 (p)) 0) 0))
  :hints (("Goal" :use (p-vals bits-divcar-3 bits-divcar-4))))

(local-defthmd bits-divcar-0
  (implies (not (specialp))
           (equal (bits (divcar) (- 52 (p)) 0) 0))
  :hints (("Goal" :use (p-vals bits-divcar-5
                        (:instance bitn-plus-bits (x (divcar)) (n (- 53 (p))) (m 0))))))

(local-defthmd bits-div-1
  (implies (not (specialp))
           (equal (bits (div) (- 52 (p)) 0)
	          (bits (+ (divsum) (divcar)) (- 52 (p)) 0)))
  :hints (("Goal" :use (p-vals) :in-theory (enable div* prescale-lemma))))

(local-defthmd bits-div-0
  (implies (not (specialp))
           (equal (bits (div) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bits bvecp)
                  :use (p-vals bits-divsum-0 bits-divcar-0 bvecp-div bits-div-1
                        (:instance mod-sum (a (mod (divsum) (expt 2 (- 53 (p))))) (b (divcar)) (n (expt 2 (- 53 (p)))))
			(:instance mod-sum (b (divsum)) (a (divcar)) (n (expt 2 (- 53 (p)))))))))

(local-defthmd div-int
  (implies (not (specialp))
           (integerp (/ (div) (expt 2 (- 53 (p))))))
  :hints (("Goal" :use (bvecp-div p-vals bits-div-0 (:instance bits-plus-bits (x (div)) (n 56) (p (- 53 (p))) (m 0))))))

(local-defthmd d-int
  (implies (not (specialp))
           (integerp (* (expt 2 (+ (p) 3)) (d))))
  :hints (("Goal" :use (p-vals div-int div-rewrite))))

(local-defthmd x-int
  (implies (not (specialp))
           (integerp (* (expt 2 (+ (p) 3)) (x))))
  :hints (("Goal" :use (p-vals exactp-a (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3)))
                  :in-theory (enable x mul))))





(local-defthmd int-rj-1
  (implies (and (not (specialp))
                (not (zp j)))
           (and (integerp (* (expt 2 (+ (p) 3)) (d)))
                (integerp (* (expt 4 (1- j)) (quot j)))))
  :hints (("Goal" :use (int-quot d-int))))

(local-defthmd int-rj-2
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (* (* (expt 2 (+ (p) 3)) (d))
                     (* (expt 4 (1- j)) (quot j)))
                  (* (D) (QUOT J) (EXPT 2 (+ (p) 1 (* 2 J))))))
  :hints (("Goal" :use (p-vals int-quot bvecp-div div-rewrite))))

(local-defthmd int-rj-3
  (implies (and (integerp m) (integerp n))
           (integerp (* m n))))

(local-defthmd int-rj-4
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (D) (QUOT J) (EXPT 2 (+ (p) 1 (* 2 J))))))
  :hints (("Goal" :use (int-rj-1 int-rj-2 (:instance int-rj-3 (m (* (expt 2 (+ (p) 3)))) (n (* (expt 4 (1- j)) (quot j)))))
                  :in-theory (theory 'minimal-theory))))

(local-defthmd int-rj-5
  (implies (and (not (specialp))
                (not (zp j)))
           (and (integerp (expt 4 (1- j)))
	        (integerp (* (expt 2 (+ (p) 3)) (x)))))
  :hints (("Goal" :in-theory (enable bvecp rp-1-rewrite)
                  :use (p-vals x-int))))

(local-defthmd int-rj-6
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (* (expt 4 (1- j)) (* (expt 2 (+ (p) 3)) (x)))
	          (* (X) (EXPT 2 (+ (p) 1 (* 2 J))))))
  :hints (("Goal" :use (p-vals))))

(local-defthmd int-rj-7
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (X) (EXPT 2 (+ (p) 1 (* 2 J))))))
  :hints (("Goal" :use (int-rj-5 int-rj-6 (:instance int-rj-3 (m (expt 4 (1- j))) (n (* (expt 2 (+ (p) 3)) (x)))))
                  :in-theory (theory 'minimal-theory))))
		  
(local-defthmd int-rj
  (implies (and (not (specialp))
                (not (zp j)))
           (integerp (* (expt 2 (+ (p) 3)) (r j))))
  :hints (("Goal" :expand ((:free (j) (r j)))
                  :use (int-rj-4 int-rj-7))))

(local-defthmd nextrem-1
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (mod (* (expt 2 56) (r j)) (expt 2 59))
	          (* (expt 2 (- 53 (p)))
		     (mod (* (expt 2 (+ (p) 3)) (r j)) (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (p-vals int-rj
                        (:instance mod-prod (k (expt 2 (- 53 (p)))) (m (* (expt 2 (+ (p) 3)) (r j))) (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-2
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (- (rp j) (rn j))
	          (* (expt 2 (- 53 (p)))
		     (- (bits (rp j) 58 (- 53 (p)))
		        (bits (rn j) 58 (- 53 (p)))))))
  :hints (("Goal" :use (p-vals 
                        (:instance bits-plus-bits (x (rp j)) (n 58) (p (- 53 (p))) (m 0))
                        (:instance bits-plus-bits (x (rn j)) (n 58) (p (- 53 (p))) (m 0)))
		  :in-theory (enable hyp))))

(local-defthmd nextrem-3
  (implies (hyp j)
           (and (bvecp (rp j) 59)
                (bvecp (rn j) 59)
                (= (bits (rp j) (- 52 (p)) 0) 0)
                (= (bits (rn j) (- 52 (p)) 0) 0)))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd nextrem-4
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (* (expt 2 (- 53 (p)))
		          (- (bits (rp j) 58 (- 53 (p)))
		             (bits (rn j) 58 (- 53 (p)))))
		       (expt 2 59))
	          (* (expt 2 (- 53 (p)))
		     (mod (- (bits (rp j) 58 (- 53 (p)))
		             (bits (rn j) 58 (- 53 (p))))
			  (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (p-vals nextrem-3
                        (:instance mod-prod (k (expt 2 (- 53 (p))))
			                    (m (- (bits (rp j) 58 (- 53 (p))) (bits (rn j) 58 (- 53 (p)))))
					    (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-5
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp j) (rn j)) (expt 2 59))
	          (* (expt 2 (- 53 (p)))
		     (mod (- (bits (rp j) 58 (- 53 (p)))
		             (bits (rn j) 58 (- 53 (p))))
			  (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (nextrem-2 nextrem-4)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-6
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 53 (p)))
		     (mod (* (expt 2 (+ (p) 3)) (r j)) (expt 2 (+ (p) 6))))
	          (* (expt 2 (- 53 (p)))
		     (mod (- (bits (rp j) 58 (- 53 (p)))
		             (bits (rn j) 58 (- 53 (p))))
			  (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (nextrem-1 nextrem-5 hyp)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-7
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (* (expt 2 (+ (p) 3)) (r j))
	               (expt 2 (+ (p) 6)))
	          (mod (- (bits (rp j) 58 (- 53 (p)))
		          (bits (rn j) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (nextrem-6 p-vals))))

(local-defthmd nextrem-8
  (implies (not (specialp))
           (equal (bits (div) 56 (- 53 (p)))
	          (* (expt 2 (+ (p) 3)) (d))))
  :hints (("Goal" :use (p-vals bvecp-div div-rewrite bits-div-0
                        (:instance bits-plus-bits (x (div)) (n 56) (p (- 53 (p))) (m 0))))))
					    
(local-defthmd nextrem-9
  (implies (not (specialp))
           (equal (bitn (div) (- 52 (p))) 0))
  :hints (("Goal" :use (bits-div-0 p-vals bvecp-div
                        (:instance bitn-plus-bits (x (div)) (n (- 52 (p))) (m 0))))))

(local-defthmd nextrem-10
  (implies (not (specialp))
           (equal (bitn (div) 57) 0))
  :hints (("Goal" :use (bvecp-div))))

(local-defthmd nextrem-11
  (implies (not (specialp))
           (equal (bitn (div) 58) 0))
  :hints (("Goal" :use (bvecp-div) :in-theory (enable bvecp))))

(local-defthm nextrem-12
  (implies (and (not (specialp))
                (not (zp j))
                (<= (q j) 0))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (- (* (expt 2 (+ (p) 3)) (q j) (d)))))
  :hints (("Goal" :in-theory (enable bvecp divmult lognot ash bvecp)
                  :use (p-vals q-vals bvecp-div nextrem-9 nextrem-10 nextrem-11 nextrem-8
		        (:instance bitn-plus-bits (x (div)) (n 58) (m (- 52 (p))))
		        (:instance bitn-plus-bits (x (div)) (n 57) (m (- 52 (p))))
		        (:instance bits-plus-bitn (x (div)) (n 58) (m (- 52 (p))))
		        (:instance bits-plus-bitn (x (div)) (n 57) (m (- 52 (p))))
		        (:instance bits-plus-bitn (x (div)) (n 56) (m (- 52 (p))))
		        (:instance bits-shift-up-1 (x (div)) (k 1) (i 58) (j (- 53 (p))))))))

(local-defthm nextrem-13
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 1))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (bits (lognot (div)) 58 (- 53 (p)))))
  :hints (("Goal" :in-theory (enable bvecp divmult ash bvecp)
                  :use (p-vals q-vals bvecp-div nextrem-9 nextrem-10 nextrem-11))))

(local-defthm nextrem-14
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 1))
           (equal (bits (lognot (div)) 58 (- 53 (p)))
	          (- (expt 2 (+ (p) 6)) (1+ (* (expt 2 (+ (p) 3)) (d))))))
  :hints (("Goal" :in-theory (enable bvecp divmult bits-lognot ash bvecp)
                  :use (p-vals q-vals bvecp-div nextrem-9 nextrem-10 nextrem-11	nextrem-8	  
		        (:instance bitn-plus-bits (x (div)) (n 58) (m (- 53 (p))))
		        (:instance bitn-plus-bits (x (div)) (n 57) (m (- 53 (p))))))))

(local-defthm nextrem-15
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 1))
           (equal (bits (divmult j) 58 (- 53 (p)))
	          (- (expt 2 (+ (p) 6)) (1+ (* (expt 2 (+ (p) 3)) (d))))))
  :hints (("Goal" :in-theory (enable bvecp divmult ash bvecp)
                  :use (nextrem-13 nextrem-14))))

(local-defthm nextrem-16
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 2))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (bits (lognot (bits (* 2 (div)) 58 0)) 58 (- 53 (p)))))
  :hints (("Goal" :in-theory (enable bvecp divmult ash bvecp)
                  :use (p-vals q-vals bvecp-div nextrem-9 nextrem-10 nextrem-11))))

(local-defthm nextrem-17
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 2))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (bits (lognot (* 2 (div))) 58 (- 53 (p)))))
  :hints (("Goal" :in-theory (enable bits-lognot-bits bvecp)
                  :use (p-vals bvecp-div nextrem-16 nextrem-9 nextrem-10 nextrem-11))))

(local-defthm nextrem-18
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 2))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (- (expt 2 (+ (p) 6)) (1+ (bits (* 2 (div)) 58 (- 53 (p)))))))
  :hints (("Goal" :in-theory (enable bits-lognot bvecp)
                  :use (p-vals bvecp-div nextrem-17
		        (:instance bits-lognot (x (* 2 (div))) (i 58) (j (- 53 (p))))))))

(local-defthm nextrem-19
  (implies (and (not (specialp))
                (not (zp j))
                (= (q j) 2))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (- (expt 2 (+ (p) 6)) (1+ (* (expt 2 (+ (p) 3)) 2 (d))))))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (p-vals bvecp-div nextrem-18 nextrem-9 nextrem-10 nextrem-11 nextrem-8
		        (:instance bitn-plus-bits (x (div)) (n 58) (m (- 52 (p))))
		        (:instance bitn-plus-bits (x (div)) (n 57) (m (- 52 (p))))
		        (:instance bits-plus-bitn (x (div)) (n 58) (m (- 52 (p))))
		        (:instance bits-plus-bitn (x (div)) (n 57) (m (- 52 (p))))
		        (:instance bits-plus-bitn (x (div)) (n 56) (m (- 52 (p))))
		        (:instance bits-shift-up-1 (x (div)) (k 1) (i 58) (j (- 53 (p))))))))

(local-defthm nextrem-20
  (implies (and (not (specialp))
                (not (zp j)))
           (equal (bits (divmult j) 58 (- 53 (p)))
                  (if (<= (q j) 0)
                      (- (* (expt 2 (+ (p) 3)) (q j) (d)))
		    (- (expt 2 (+ (p) 6)) (1+ (* (expt 2 (+ (p) 3)) (q j) (d)))))))
  :hints (("Goal" :use (q-vals nextrem-12 nextrem-15 nextrem-19))))

(local-defthm nextrem-21
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (and (bvecp (rp4 (1+ j)) 59)
	        (bvecp (rn4 (1+ j)) 59)))
  :hints (("Goal" :in-theory (enable rp4 rn4))))

(local-defthm nextrem-22
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (and (equal (bits (rp4 (1+ j)) (- 54 (p)) 0) 0)
	        (equal (bits (rn4 (1+ j)) (- 54 (p)) 0) 0)))
  :hints (("Goal" :in-theory (enable rp4 rn4 ash)
                  :use (p-vals nextrem-3 
		        (:instance bits-shift-up-2 (k 2) (x (rp j)) (i (- 52 (p))))
		        (:instance bits-shift-up-2 (k 2) (x (rn j)) (i (- 52 (p))))))))

(local-defthm nextrem-23
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (and (equal (bits (rp4 (1+ j)) (- 52 (p)) 0) 0)
	        (equal (bits (rn4 (1+ j)) (- 52 (p)) 0) 0)))
  :hints (("Goal" :use (p-vals nextrem-22
		        (:instance bits-plus-bits (x (rp4 (1+ j))) (n (- 54 (p))) (p (- 53 (p))) (m 0))
		        (:instance bits-plus-bits (x (rn4 (1+ j))) (n (- 54 (p))) (p (- 53 (p))) (m 0))))))

(local-defthm nextrem-24
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 53 (p)))
	             (mod (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p))))
			  (expt 2 (+ (p) 6))))
	          (mod (* (expt 2 (- 53 (p)))
		          (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p)))))
		       (expt 2 59))))
  :hints (("Goal" :use (p-vals nextrem-21
                        (:instance mod-prod (k (expt 2 (- 53 (p))))
			                    (m (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		                                  (bits (rn4 (1+ j)) 58 (- 53 (p)))))
				            (n (expt 2 (+ (p) 6))))))))

(local-defthm nextrem-25
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 53 (p)))
	             (mod (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p))))
			  (expt 2 (+ (p) 6))))
	          (mod (- (rp4 (1+ j)) (rn4 (1+ j)))
		       (expt 2 59))))
  :hints (("Goal" :use (p-vals nextrem-24 nextrem-23 nextrem-21
                        (:instance bits-plus-bits (x (rp4 (1+ j))) (n 58) (p (- 53 (p))) (m 0))
                        (:instance bits-plus-bits (x (rn4 (1+ j))) (n 58) (p (- 53 (p))) (m 0))))))

(local-defthm nextrem-26
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp4 (1+ j)) (rn4 (1+ j)))
		       (expt 2 59))
		  (mod (* 4 (- (rp j) (rn j)))
		       (expt 2 59))))
  :hints (("Goal" :use (p-vals nextrem-3
                        (:instance mod-sum (b (* 4 (rp j))) (a (- (mod (* 4 (rn j)) (expt 2 59)))) (n (expt 2 59)))
                        (:instance mod-diff (b (* 4 (rn j))) (a (* 4 (rp j))) (n (expt 2 59))))
                  :in-theory (enable ash bits rp4 rn4))))

(local-defthm nextrem-27
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (* (expt 2 56) (r j)) (expt 2 59)) (mod (- (rp j) (rn j)) (expt 2 59))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthm nextrem-28
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (* 4 (- (rp j) (rn j)))
		       (expt 2 59))
		  (mod (* (expt 2 58) (r j))
		       (expt 2 59))))
  :hints (("Goal" :use (nextrem-3 nextrem-27 int-r
                        (:instance mod-mod-times (a (- (rp j) (rn j))) (b 4) (n (expt 2 59)))
                        (:instance mod-mod-times (a (* (expt 2 56) (r j))) (b 4) (n (expt 2 59)))))))

(local-defthm nextrem-29
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (* 4 (- (rp j) (rn j)))
		       (expt 2 59))
		  (* (expt 2 (- 53 (p)))
		     (mod (* (expt 2 (+ (p) 5)) (r j))
		          (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (nextrem-28 p-vals
                        (:instance mod-prod (k (expt 2 (- 53 (p)))) (m (* (expt 2 (+ (p) 5)) (r j))) (n (expt 2 (+ (p) 6))))))))

(local-defthm nextrem-30
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (* (expt 2 (- 53 (p)))
	             (mod (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p))))
			  (expt 2 (+ (p) 6))))
	          (* (expt 2 (- 53 (p)))
		     (mod (* (expt 2 (+ (p) 5)) (r j))
		          (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (nextrem-29 nextrem-26 nextrem-25)
                  :in-theory (theory 'minimal-theory))))

(local-defthm nextrem-31
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		          (bits (rn4 (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
                  (mod (* (expt 2 (+ (p) 5)) (r j))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-30))))

(local-defthm nextrem-32
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (lognot (sum (1+ j)))
	          (logxor (logxor (lognot (rn4 (1+ j)))
		                  (rp4 (1+ j)))
		          (divmult (1+ j)))))
  :hints (("Goal" :in-theory (enable lognot-logxor sum))))

(local-defthm integerp-divmult
  (implies (not (specialp))
           (integerp (divmult j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable bvecp divmult) :use (bvecp-div))))

(local-defthm nextrem-33
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (lognot (sum (1+ j))) 58 (- 53 (p)))
	          (logxor (logxor (bits (lognot (rn4 (1+ j))) 58 (- 53 (p)))
		                  (bits (rp4 (1+ j)) 58 (- 53 (p))))
		          (bits (divmult (1+ j)) 58 (- 53 (p))))))
  :hints (("Goal" :use (p-vals nextrem-32)
                  :in-theory (enable bits-logxor))))

(local-defthm integerp-carry-0
  (implies (not (specialp))
           (integerp (carry-0 j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable bvecp carry-0))))

(local-defthm nextrem-34
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry-0 (1+ j)) 58 (- 53 (p)))
                  (logior (logand (bits (lognot (rn4 (1+ j))) 58 (- 53 (p))) (bits (rp4 (1+ j)) 58 (- 53 (p))))
                          (logand (logior (bits (lognot (rn4 (1+ j))) 58 (- 53 (p))) (bits (rp4 (1+ j)) 58 (- 53 (p))))
                                  (bits (divmult (1+ j)) 58 (- 53 (p)))))))
  :hints (("Goal" :use (p-vals nextrem-32 nextrem-3)
                  :in-theory (enable carry-0 bits-logior bits-logand))))

(local-defthm nextrem-35
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (lognot (sum (1+ j))) 58 (- 53 (p)))
	          (logxor (bits (rp4 (1+ j)) 58 (- 53 (p)))
		          (logxor (bits (lognot (rn4 (1+ j))) 58 (- 53 (p)))
			          (bits (divmult (1+ j)) 58 (- 53 (p)))))))
  :hints (("Goal" :use (p-vals nextrem-33))))

(local-defthm nextrem-36
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry-0 (1+ j)) 58 (- 53 (p)))
	          (logior (logand (bits (rp4 (1+ j)) 58 (- 53 (p))) (bits (lognot (rn4 (1+ j))) 58 (- 53 (p))))
                          (logior (logand (bits (rp4 (1+ j)) 58 (- 53 (p))) (bits (divmult (1+ j)) 58 (- 53 (p))))
			          (logand (bits (lognot (rn4 (1+ j))) 58 (- 53 (p))) (bits (divmult (1+ j)) 58 (- 53 (p))))))))
  :hints (("Goal" :use (p-vals nextrem-34
                        (:instance logand-logior (x (bits (divmult (1+ j)) 58 (- 53 (p))))
			                         (y (bits (lognot (rn4 (1+ j))) 58 (- 53 (p))))
						 (z (bits (rp4 (1+ j)) 58 (- 53 (p))))))))) 

(local-defthm nextrem-37
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))
	             (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))))
		  (+ (bits (rp4 (1+ j)) 58 (- 53 (p)))
		     (bits (lognot (rn4 (1+ j))) 58 (- 53 (p)))
		     (bits (divmult (1+ j)) 58 (- 53 (p))))))
  :hints (("Goal" :use (p-vals nextrem-35 nextrem-36
                        (:instance add-3 (x (bits (rp4 (1+ j)) 58 (- 53 (p))))
			                 (y (bits (lognot (rn4 (1+ j))) 58 (- 53 (p))))
			                 (z (bits (divmult (1+ j)) 58 (- 53 (p)))))))))

(local-defthm nextrem-38
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (bits (rp4 (1+ j)) 58 (- 53 (p)))
		          (bits (lognot (rn4 (1+ j))) 58 (- 53 (p)))
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p))))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals) :in-theory (enable bits-lognot))))

(local-defthm nextrem-39
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))
  	                  (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p))))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (nextrem-38 nextrem-37) :in-theory (theory 'minimal-theory))))

(local-defthm nextrem-40
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		             (bits (rn4 (1+ j)) 58 (- 53 (p))))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (nextrem-31 p-vals
                        (:instance mod-sum (a (1- (bits (divmult (1+ j)) 58 (- 53 (p)))))
			                   (b (- (bits (rp4 (1+ j)) 58 (- 53 (p)))
		                                 (bits (rn4 (1+ j)) 58 (- 53 (p)))))
				           (n (expt 2 (+ (p) 6))))
                        (:instance mod-sum (a (1- (bits (divmult (1+ j)) 58 (- 53 (p)))))
			                   (b (* (expt 2 (+ (p) 5)) (r j)))
				           (n (expt 2 (+ (p) 6))))))))

(local-defun pos (j) (if (> (q (1+ j)) 0) 1 0))

(local-defthm rat-r
  (implies (not (zp j))
           (rationalp (r j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable r))))

(local-defthm nextrem-41
  (implies (and (not (specialp))
                (not (zp j))
		(<= (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals
                        (:instance q-vals (j (1+ j)))
                        (:instance nextrem-20 (j (1+ j)))))))

(local-defthm nextrem-42
  (implies (and (not (specialp))
                (not (zp (1+ j)))
		(> (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
			  (- (expt 2 (+ (p) 6)) (1+ (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals
                        (:instance q-vals (j (1+ j)))
                        (:instance nextrem-20 (j (1+ j))))
	          :in-theory (theory 'minimal-theory))))	          

(local-defthm nextrem-43
  (implies (and (not (specialp))
                (not (zp j))
		(> (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (expt 2 (+ (p) 6))
			  (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable pos)
                  :use (p-vals nextrem-42
                        (:instance q-vals (j (1+ j)))))))

(local-defthm nextrem-44
  (implies (and (not (specialp))
                (not (zp j))
		(> (q (1+ j)) 0)
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
			  (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (enable pos)
                  :use (p-vals nextrem-43
		        (:instance mod-mult (a 1)
			                    (n (expt 2 (+ (p) 6)))
					    (m (+ (* (expt 2 (+ (p) 5)) (r j))
			                          -1
			                          (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			                          (- (pos j)))))
                        (:instance q-vals (j (1+ j)))))))

(local-defthm nextrem-45
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
			  (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
			  (- (pos j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (p-vals nextrem-41 nextrem-44))))

(local-defthm nextrem-46
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (+ (* (expt 2 (+ (p) 5)) (r j))
		     -1
		     (- (* (expt 2 (+ (p) 3)) (q (1+ j)) (d)))
		     (- (pos j)))
	          (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
	             -1
		     (- (pos j)))))
  :hints (("Goal" :in-theory (enable r-recurrence pos)
                  :use (p-vals (:instance q-vals (j (1+ j)))))))

(local-defthm nextrem-47
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (* (expt 2 (+ (p) 5)) (r j))
			  -1
		          (bits (divmult (1+ j)) 58 (- 53 (p))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
			  -1
			  (- (pos j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (nextrem-45 nextrem-46))))

(local-defthm nextrem-48
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))
  	                  (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))))
		       (expt 2 (+ (p) 6)))
		  (mod (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
			  -1
			  (- (pos j)))
		       (expt 2 (+ (p) 6)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (nextrem-39 nextrem-40 nextrem-47))))

(local-defthm nextrem-49
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry (1+ j)) 58 (- 54 (p)))
	          (bits (bits (carry-0 (1+ j)) 58 (- 53 (p))) (+ (p) 4) 0)))
  :hints (("Goal" :use (p-vals
                        (:instance bits-shift-up-1 (x (carry-0 (1+ j))) (k 1) (i 58) (j (- 54 (p)))))
		  :in-theory (enable ash carry))))

(local-defthmd nextrem-50
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (carry (1+ j)) 58 (- 54 (p)))
	          (mod (bits (carry-0 (1+ j)) 58 (- 53 (p))) (expt 2 (+ (p) 5)))))
  :hints (("Goal" :use (p-vals nextrem-49)
		  :in-theory (e/d (bits) (bits-bits)))))

(local-defthmd nextrem-51
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) 58 (- 54 (p)))
	          (mod (bits (carry-0 (1+ j)) 58 (- 53 (p))) (expt 2 (+ (p) 5)))))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals nextrem-50))))

(local-defthmd nextrem-52
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bitn (rp (1+ j)) (- 53 (p)))
	          (pos j)))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma f p prec dp sp hp pos) 
                  :use (fnum-vals (:instance q-vals (j (1+ j)))))))

(local-defthmd nextrem-53
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) 58 (- 53 (p)))
	          (+ (* 2 (mod (bits (carry-0 (1+ j)) 58 (- 53 (p))) (expt 2 (+ (p) 5))))
		     (pos j))))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals nextrem-51 nextrem-52
		        (:instance bits-plus-bitn (x (rp (1+ j))) (n 58) (m (- 53 (p))))))))

(local-defthmd nextrem-54
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) 58 (- 53 (p)))
	          (+ (mod (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))) (expt 2 (+ (p) 6)))
		     (pos j))))
  :hints (("Goal" :use (p-vals nextrem-53
                        (:instance mod-prod (k 2) (m (bits (carry-0 (1+ j)) 58 (- 53 (p)))) (n (expt 2 (+ (p) 5))))))))

(local-defthmd nextrem-55
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (rn (1+ j)) 58 (- 53 (p)))
	          (bits (sum (1+ j)) 58 (- 53 (p))))) 
  :hints (("Goal" :in-theory (enable rn* nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals))))

(local-in-theory (disable nextrem-32))

(local-defthmd nextrem-56
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (sum (1+ j)) 58 (- 53 (p)))) (expt 2 (+ (p) 6)))
	          (mod (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))) (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals) :in-theory (e/d (bits-lognot) (ACL2::|(mod (- x) y)| acl2::mod-zero)))))

(local-defthmd nextrem-57
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rn (1+ j)) 58 (- 53 (p)))) (expt 2 (+ (p) 6)))
	          (mod (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))) (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (nextrem-55 nextrem-56))))
                  
(local-defthmd nextrem-58
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (rp (1+ j)) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals nextrem-3))))

(local-defthmd nextrem-59
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (bvecp (rp (1+ j)) 59))
  :hints (("Goal" :in-theory (enable rp* nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals))))

(local-defthmd nextrem-60
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (bits (rn (1+ j)) (- 52 (p)) 0)
	          0))
  :hints (("Goal" :in-theory (enable rn* nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals nextrem-3))))

(local (in-theory (disable ash-rewrite)))

(local-defthmd nextrem-61
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (bvecp (rn (1+ j)) 59))
  :hints (("Goal" :in-theory (enable rn* sum divmult rp4 rn4 nextrem-lemma f p prec dp sp hp) 
                  :use (fnum-vals bvecp-div
		        (:instance bvecp-monotone (x (div)) (n 57) (m 59))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextrem-62
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 59))
		  (mod (* (expt 2 (- 53 (p)))
		          (- (bits (rp (1+ j)) 58 (- 53 (p)))
			     (bits (rn (1+ j)) 58 (- 53 (p)))))
	               (expt 2 59))))		
  :hints (("Goal" :use (p-vals nextrem-61 nextrem-60 nextrem-59 nextrem-58
                        (:instance bits-plus-bits (x (rp (1+ j))) (n 58) (p (- 53 (p))) (m 0))
			(:instance bits-plus-bits (x (rn (1+ j))) (n 58) (p (- 53 (p))) (m 0))))))

(local-defthmd nextrem-63
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 59))
		  (* (expt 2 (- 53 (p)))
		     (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			     (bits (rn (1+ j)) 58 (- 53 (p))))
	                  (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (p-vals nextrem-62
                        (:instance mod-prod (k (expt 2 (- 53 (p))))
			                    (m (- (bits (rp (1+ j)) 58 (- 53 (p))) (bits (rn (1+ j)) 58 (- 53 (p)))))
					    (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-64
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (bits (rp (1+ j)) 58 (- 53 (p)))
		          (mod (- (bits (rn (1+ j)) 58 (- 53 (p)))) (expt 2 (+ (p) 6))))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals
                        (:instance mod-sum (b (- (bits (rn (1+ j)) 58 (- 53 (p)))))
			                   (a (bits (rp (1+ j)) 58 (- 53 (p))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-65
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (bits (rp (1+ j)) 58 (- 53 (p)))
		          (mod (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))) (expt 2 (+ (p) 6))))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-64 nextrem-57)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-66
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (bits (rp (1+ j)) 58 (- 53 (p)))
		          (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-65
                        (:instance mod-sum (a (bits (rp (1+ j)) 58 (- 53 (p))))
			                   (b (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-67
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (+ (mod (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))) (expt 2 (+ (p) 6)))
		             (pos j))
		          (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-66 nextrem-54)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-68
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p))))
		          (pos j)
		          (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-67
                        (:instance mod-sum (a (+ (pos j) (1+ (bits (lognot (sum (1+ j))) 58 (- 53 (p))))))
			                   (b (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-69
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (mod (+ (bits (lognot (sum (1+ j))) 58 (- 53 (p)))
  	                          (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p)))))
		               (expt 2 (+ (p) 6)))
		          1 (pos j))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-68
                        (:instance mod-sum (a (1+ (pos j)))
			                   (b (+ (* 2 (bits (carry-0 (1+ j)) 58 (- 53 (p))))
		                                 (bits (lognot (sum (1+ j))) 58 (- 53 (p)))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-70
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (+ (mod (+ (* (expt 2 (+ (p) 3)) (r (1+ j)))
			          -1
			          (- (pos j)))
			       (expt 2 (+ (p) 6)))
		          1 (pos j))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-48 nextrem-69)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-71
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (bits (rp (1+ j)) 58 (- 53 (p)))
			  (bits (rn (1+ j)) 58 (- 53 (p))))
	               (expt 2 (+ (p) 6)))
		  (mod (* (expt 2 (+ (p) 3)) (r (1+ j)))
	               (expt 2 (+ (p) 6)))))
  :hints (("Goal" :use (p-vals nextrem-70
                        (:instance mod-sum (a (1+ (pos j)))
			                   (b (+ (* (expt 2 (+ (p) 3)) (r (1+ j))) -1 (- (pos j))))
					   (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextrem-72
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 59))
		  (* (expt 2 (- 53 (p)))
		     (mod (* (expt 2 (+ (p) 3)) (r (1+ j)))
	                  (expt 2 (+ (p) 6))))))
  :hints (("Goal" :use (p-vals nextrem-63 nextrem-71)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd nextrem-73
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
           (equal (mod (- (rp (1+ j)) (rn (1+ j)))
	               (expt 2 59))
                  (mod (* (expt 2 56) (r (1+ j)))
	               (expt 2 59))))
  :hints (("Goal" :use (p-vals nextrem-72 nextrem-59 nextrem-61
                        (:instance mod-prod (k (expt 2 (- 53 (p))))
			                    (m (* (expt 2 (+ (p) 3)) (r (1+ j))))
					    (n (expt 2 (+ (p) 6))))))))

(local-defthmd nextquot-1
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (and (bvecp (qp j) (- (* 2 j) 2))
	        (bvecp (qn j) (- (* 2 j) 2))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd nextquot-2
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n))))
	   (<= j 27))
  :hints (("Goal" :in-theory (enable n))))

(local-defthmd nextquot-3
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n)))
		(>= (q (1+ j)) 0))
	   (and (equal (qp (+ 1 j)) (+ (* 4 (qp j)) (q (1+ j))))
	        (equal (qn (+ 1 j)) (* 4 (qn j)))))
  :hints (("Goal" :in-theory (enable bvecp nextquot qp qn cat ash)
                  :nonlinearp t
                  :use (nextquot-1 nextquot-2
		        (:instance bits-shift-up-1 (x (qp j)) (k 2) (i 53) (j 2))
		        (:instance bits-shift-up-1 (x (qn j)) (k 2) (i 53) (j 2))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-4
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n)))
		(< (q (1+ j)) 0))
	   (and (equal (qn (+ 1 j)) (- (* 4 (qn j)) (q (1+ j))))
	        (equal (qp (+ 1 j)) (* 4 (qp j)))))
  :hints (("Goal" :in-theory (enable bvecp nextquot qp qn cat ash)
                  :nonlinearp t
                  :use (nextquot-1 nextquot-2
		        (:instance bits-shift-up-1 (x (qp j)) (k 2) (i 53) (j 2))
		        (:instance bits-shift-up-1 (x (qn j)) (k 2) (i 53) (j 2))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-5
  (implies (and (natp q)
                (natp j)
		(< q (expt 2 j)))
	   (<= (* 4 q) (- (expt 2 (+ 2 j)) 4)))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd nextquot-6
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n))))
	   (and (bvecp (qp (1+ j)) (* 2 j))
	        (bvecp (qn (1+ j)) (* 2 j))))
  :hints (("Goal" :in-theory (enable nextquot-3 nextquot-4 bvecp)
                  :nonlinearp t
                  :use (nextquot-1 nextquot-2
		        (:instance nextquot-5 (q (qp j)) (j (- (* 2 j) 2)))
		        (:instance nextquot-5 (q (qn j)) (j (- (* 2 j) 2)))
		        (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-7
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j))
	   (equal (- (qp j) (qn j))
	          (* (expt 4 (1- j)) (- (quot j) (q 1)))))
  :hints (("Goal" :in-theory (enable hyp))))

(local-defthmd nextquot-8
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n))))
	   (equal (- (qp (1+ j)) (qn (1+ j)))
	          (+ (* 4 (- (qp j) (qn j))) (q (1+ j)))))
  :hints (("Goal" :in-theory (enable nextquot-3 nextquot-4 bvecp)
                  :use (nextquot-1 (:instance q-vals (j (1+ j)))))))

(local-defthmd nextquot-9
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n))))
	   (equal (- (qp (1+ j)) (qn (1+ j)))
	          (+ (* 4 (* (expt 4 (1- j)) (- (quot j) (q 1)))) (q (1+ j)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (nextquot-7 nextquot-8))))

(local-defthmd nextquot-10
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n))))
	   (equal (- (qp (1+ j)) (qn (1+ j)))
	          (+ (* (expt 4 j) (- (quot j) (q 1))) (q (1+ j)))))
  :hints (("Goal" :use (nextquot-9))))

(local-defthmd nextquot-11
  (implies (and (not (specialp))
                (not (zp j))
		(hyp j)
		(<= j (* 3 (n))))
	   (equal (- (qp (1+ j)) (qn (1+ j)))
	          (* (expt 4 j) (- (quot (1+ j)) (q 1)))))
  :hints (("Goal" :use (nextquot-10) :in-theory (enable quot))))

(local-defthmd nextquot-12
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(or (= j 1) (hyp (1- j)))
		(hyp j))
	   (hyp (1+ j)))
  :hints (("Goal" :expand ((hyp 2) (hyp (+ 1 j)))
                  :use (p-vals approx-error r-bound-induct nextrem-59 nextrem-61 nextrem-73 nextrem-58 nextrem-60 nextquot-6 nextquot-11
		        (:instance q-maxk (j (1+ j)))))))

(local-defund hyp2 (j)
  (and (hyp j)
       (or (= j 1)
           (hyp (1- j)))))

(local-in-theory (disable (hyp2)))

(local-defthmd hyp2-1
  (implies (not (specialp))
           (hyp2 1))
  :hints (("Goal" :in-theory (enable hyp2) :use (hyp-1))))

(local-defthmd nextquot-13
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (* 3 (n)))
		(hyp2 j))
	   (hyp2 (1+ j)))
  :hints (("Goal" :in-theory (enable hyp2)
                  :use (nextquot-12))))

(local-defthmd induct-step
  (implies (and (not (specialp))
                (not (zp j))
		(not (= j 1))
		(<= j (1+ (* 3 (n))))
		(hyp2 (1- j)))
	   (hyp2 j))
  :hints (("Goal" :use ((:instance nextquot-13 (j (1- j)))))))

(local-in-theory (enable quot))

(local-defthmd main-induction
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (1+ (* 3 (n)))))
           (hyp2 j))
  :hints (("Goal" :induct (quot j))  
          ("Subgoal *1/2" :use (hyp2-1))
          ("Subgoal *1/1" :use (hyp2-1 induct-step))))

(defthmd induction-result
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (1+ (* 3 (n)))))
           (and (= (q j) (maxk (approx j)))
                (< (abs (- (approx j) (* 4 (r (1- j))))) 1/8)
                (<= (abs (r j)) (* 2/3 (d)))
                (bvecp (rp j) 59)
                (bvecp (rn j) 59)
                (= (mod (* (expt 2 56) (r j)) (expt 2 59)) (mod (- (rp j) (rn j)) (expt 2 59)))
                (= (bits (rp j) (- 52 (p)) 0) 0)
                (= (bits (rn j) (- 52 (p)) 0) 0)
                (bvecp (qp j) (- (* 2 j) 2))
                (bvecp (qn j) (- (* 2 j) 2))
                (= (* (expt 4 (1- j)) (- (quot j) (q 1))) (- (qp j) (qn j)))))
  :hints (("Goal" :use (main-induction)
                  :in-theory '(hyp2 hyp))))

(local-defthmd q-error-1
  (implies (and (not (specialp))
                (natp j))
           (equal (- (/ (x) (d)) (quot j))
	          (/ (* (expt 4 (- 1 j)) (r j))
		     (d))))
  :hints (("Goal" :in-theory (enable r) :use (d-bounds))))

(defund quotf () (quot (1+ (* 3 (n)))))

(defund rf () (r (1+ (* 3 (n)))))

(in-theory (disable (quotf) (rf)))

(local-defthmd q-error-2
  (implies (not (specialp))
           (equal (- (/ (x) (d)) (quotf))
	          (/ (* (expt 4 (- (* 3 (n)))) (rf))
		     (d))))
  :hints (("Goal" :in-theory (enable rf quotf) :use ((:instance q-error-1 (j (1+ (* 3 (n)))))))))

(local-defthmd q-error-3
  (implies (not (specialp))
           (<= (abs (rf)) (* 2/3 (d))))
  :hints (("Goal" :in-theory (enable rf) :use ((:instance induction-result (j (1+ (* 3 (n)))))))))

(local-defthmd q-error-4
  (implies (not (specialp))
           (<= (abs (/ (* (expt 4 (- (* 3 (n)))) (rf)) (d)))
	       (* 2/3 (expt 2 (- (* 6 (n)))))))
  :hints (("Goal" :use (d-bounds q-error-3) :nonlinearp t)))

(defthmd q-error
  (implies (not (specialp))
           (<= (abs (- (/ (x) (d)) (quotf)))
	       (* 2/3 (expt 2 (- (* 6 (n)))))))
  :hints (("Goal" :use (d-bounds q-error-2 q-error-4))))
