(in-package "RTL")

(include-book "quotient")

(local-defund lsb () (bitn (qtrunc) 1))

(local-defund grd () (bitn (qtrunc) 0))

(local-defund qrnd* ()
  (if1 (logior1 (logior1 (logand1 (logand1 (log= (rmode) 0) (grd))
                                  (logior1 (lsb) (stk)))
                         (logand1 (logand1 (log= (rmode) 1)
                                           (lognot1 (sign)))
                                  (logior1 (grd) (stk))))
                (logand1 (logand1 (log= (rmode) 2) (sign))
                         (logior1 (grd) (stk))))
       (bits (qinc) 53 1)
       (bits (qtrunc) 53 1)))


(local-defund inx* () (logior1 (grd) (stk)))

(local-defund qden ()
  (let ((qden (bits 0 63 0)))
    (case (fnum)
      (2 (let ((qden (setbitn qden 64 53 1)))
           (setbits qden 64 52 0 (bits (qtrunc) 52 0))))
      (1 (let ((qden (setbitn qden 64 24 1)))
           (setbits qden 64 23 0 (bits (qtrunc) 23 0))))
      (0 (let ((qden (setbitn qden 64 11 1)))
           (setbits qden 64 10 0 (bits (qtrunc) 10 0))))
      (t qden))))

(local-defund shft12 ()
  (bits (- 1 (si (expq) 13)) 11 0))

(local-defund shft ()
  (bits (if1 (log>= (shft12) 64) 63 (shft12)) 5 0))

(local-defund qshft () (mv-nth 0 (mv-list 2 (rshft64 (qden) (shft)))))

(local-defund stkden-0 () (mv-nth 1 (mv-list 2 (rshft64 (qden) (shft)))))

(local-defund lsbden () (bitn (qshft) 1))

(local-defund grdden () (bitn (qshft) 0))

(local-defund stkden () (logior1 (stkden-0) (stk)))

(local-defund qrndden* ()
  (bits (if1 (logior1 (logior1 (logand1 (logand1 (log= (rmode) 0)
                                                 (grdden))
                                        (logior1 (lsbden) (stkden)))
                               (logand1 (logand1 (log= (rmode) 1)
                                                 (lognot1 (sign)))
                                        (logior1 (grdden) (stkden))))
                      (logand1 (logand1 (log= (rmode) 2) (sign))
                               (logior1 (grdden) (stkden))))
             (bits (+ (bits (qshft) 53 1) 1) 53 0)
             (bits (qshft) 53 1))
        52 0))

(local-defund inxden* () (logior1 (grdden) (stkden)))

(local (in-theory (disable (lsb) (grd) (qrnd*) (inx*) (qden) (shft12) (shft) (qshft) (stkden-0) (lsbden) (grdden)
                           (stkden) (qrndden*) (inxden*))))

(local-defthmd rounder-lemma
  (and (equal (qrnd) (qrnd*))
       (equal (inx) (inx*))
       (equal (qrndden) (qrndden*))
       (equal (inxden) (inxden*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(lsb grd qrnd* inx* qden shft12 shft qshft stkden-0 lsbden grdden stkden qrndden* inxden*
		               qrnd inx qrndden inxden rounder))))

(defund mode ()
  (case (rmode)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

(defund modep ()
  (if (< (/ (a) (b)) 0)
      (flip-mode (mode))
    (mode)))

(in-theory (disable (mode) (modep)))

(local-defund z* () (* (expt 2 (p)) (/ (x) (d))))

(local (in-theory (disable (z*))))

(local-defthmd qrnd-1
  (implies (not (specialp))
           (equal (expo (z*)) (p)))
  :hints (("Goal" :in-theory (enable z*)
                  :nonlinearp t
                  :use (p-vals x-bounds
		        (:instance expo-shift (n (p)) (x (/ (x) (d))))
			(:instance expo-unique (n 0) (x (/ (x) (d))))))))

(local-defthmd qrnd-2
  (implies (not (specialp))
           (and (rationalp (z*))
	        (> (z*) 0)))
  :hints (("Goal" :in-theory (enable z*)
                  :nonlinearp t
                  :use (p-vals x-bounds
		        (:instance expo-shift (n (p)) (x (/ (x) (d))))
			(:instance expo-unique (n 0) (x (/ (x) (d))))))))

(local-defthmd qrnd-3
  (implies (not (specialp))
           (<= (expt 2 (p)) (z*)))
  :hints (("Goal" :in-theory (enable z*)
                  :nonlinearp t
                  :use (p-vals x-bounds
		        (:instance expo-shift (n (p)) (x (/ (x) (d))))
			(:instance expo-unique (n 0) (x (/ (x) (d))))))))

(defthmd qrnd-4
  (implies (not (specialp))
           (common-mode-p (modep)))
  :hints (("Goal" :in-theory (enable rmode mode modep common-mode-p flip-mode)
                  :use ((:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd qrnd-5
  (implies (not (specialp))
           (equal (bits (fl (z*)) (1- (p)) 0)
	          (bits (qtrunc) (1- (p)) 0)))
  :hints (("Goal" :in-theory (enable bits z*)
                  :use (qtrunc-rewrite-gen))))

(local-defthmd qrnd-6
  (implies (not (specialp))
           (equal (stk)
	          (if (integerp (z*)) 0 1)))
  :hints (("Goal" :in-theory (enable z*)
                  :use (stk-rewrite-gen))))

(local-defthmd qrnd-7
  (implies (not (specialp))
           (equal (expo (fl (z*))) (p)))
  :hints (("Goal" :use (p-vals qrnd-1 qrnd-2
                        (:instance expo-lower-bound (x (z*)))
                        (:instance expo-upper-bound (x (z*)))
                        (:instance expo-unique (x (fl (z*))) (n (p)))))))

(local-defthmd qrnd-8
  (implies (not (specialp))
           (iff (exactp (z*) (p))
	        (and (= (stk) 0)
		     (= (bitn (fl (z*)) 0) 0))))
  :hints (("Goal" :use (p-vals qrnd-2 qrnd-3 qrnd-4 qrnd-6 qrnd-7
                        (:instance roundup-pos-thm (mode (modep)) (z (z*)) (n (p)))))))

(local-defthmd qrnd-9
  (implies (not (specialp))
           (iff (exactp (/ (x) (d)) (p))
	        (and (= (stk) 0)
		     (= (bitn (fl (z*)) 0) 0))))
  :hints (("Goal" :use (p-vals qrnd-8
                        (:instance exactp-shift (k (p)) (n (p)) (x (/ (x) (d)))))
		  :in-theory (enable z*))))

(local-defthmd inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (exactp (/ (x) (d)) (p))
		      0 1)))
  :hints (("Goal" :use (p-vals qrnd-5 qrnd-9
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 0))
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 0)))
		  :in-theory (enable rounder-lemma inx* grd))))

(local-defthmd qrnd-10
  (implies (not (specialp))
           (equal (rnd (z*) (modep) (p))
	          (if (roundup-pos (fl (z*)) (p) (stk) (modep) (p))
		      (fp+ (rtz (fl (z*)) (p)) (p))
		    (rtz (fl (z*)) (p)))))
  :hints (("Goal" :use (p-vals qrnd-2 qrnd-3 qrnd-4 qrnd-6 qrnd-7
                        (:instance roundup-pos-thm (mode (modep)) (z (z*)) (n (p)))))))

(in-theory (disable sgn-ddecode))

(local-defthmd signa-rewrite
  (implies (not (specialp))
           (equal (signa)
	          (if (> (a) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable sgn specialp divpow2 encodingp normp denormp decode a f dp sp hp prec p)
                  :use (sign-0-1 a-fields member-classa a-class fnum-vals a-fields
		        (:instance sgn-ndecode (x (opaw)) (f (f)))
		        (:instance sgn-ddecode (x (opaw)) (f (f)))))))

(local-defthmd signb-rewrite
  (implies (not (specialp))
           (equal (signb)
	          (if (> (b) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable sgn specialp divpow2 encodingp normp denormp decode b f dp sp hp prec p)
                  :use (sign-0-1 b-fields member-classb b-class fnum-vals
		        (:instance sgn-ndecode (x (opbw)) (f (f)))
		        (:instance sgn-ddecode (x (opbw)) (f (f)))))))

(defthmd sign-rewrite
  (implies (not (specialp))
           (equal (sign)
	          (if (> (/ (a) (b)) 0)
		      0 1)))
  :hints (("Goal" :in-theory (enable z* sign signa-rewrite signb-rewrite)
                  :use (qrnd-2))))

(local-defthmd qrnd-11
  (implies (not (specialp))
           (equal (qrnd)
	          (if (roundup-pos (fl (z*)) (p) (stk) (modep) (p))
		      (bits (qinc) 53 1)
		    (bits (qtrunc) 53 1))))
  :hints (("Goal" :in-theory (enable stk-rewrite-gen sign-rewrite roundup-pos qrnd* rounder-lemma lsb grd modep
                                     mode rmode)
                  :use (qrnd-5 p-vals
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 0))
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 0))
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 1))
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 1))))))

(local-defthmd qrnd-12
  (implies (and (not (specialp)) (eql (p) k))
           (equal (rtz (fl (z*)) k)
	          (* 2 (bits (fl (z*)) (p) 1))))
  :hints (("Goal" :use (qrnd-2 qrnd-7 (:instance bits-rtz (x (fl (z*))) (n (1+ (p))) (k (p)))))))

(local-defthmd qrnd-13
  (implies (not (specialp))
           (equal (mod (rtz (fl (z*)) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (fl (z*)) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :in-theory (e/d (qrnd-12) (ACL2::|(equal (mod a n) (mod b n))|))
                  :use (p-vals
		        (:instance mod-mult (m (* 2 (bits (fl (z*)) (1- (p)) 1))) (a (bitn (fl (z*)) (p))) (n (expt 2 (p))))
		        (:instance bitn-plus-bits (x (fl (z*))) (n (p)) (m 1))))))

(local-defthmd qrnd-14
  (implies (not (specialp))
           (equal (mod (rtz (fl (z*)) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qtrunc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-13 qrnd-5 p-vals
                        (:instance bits-bits (x (fl (z*))) (i (1- (p))) (j 0) (k (1- (p))) (l 1))
                        (:instance bits-bits (x (qtrunc)) (i (1- (p))) (j 0) (k (1- (p))) (l 1))))))

(local-defthmd qrnd-15
  (implies (and (not (specialp))
                (not (roundup-pos (fl (z*)) (p) (stk) (modep) (p))))
           (equal (mod (rnd (z*) (modep) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qtrunc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-14 qrnd-10))))

(local-defthmd qrnd-16
  (implies (and (not (specialp))
                (not (roundup-pos (fl (z*)) (p) (stk) (modep) (p))))
           (equal (mod (rnd (z*) (modep) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-15 qrnd-11 p-vals
                        (:instance bits-bits (x (qtrunc)) (i 53) (j 1) (k (- (p) 2)) (l 0))))))

(local-defthmd qrnd-17
  (implies (not (specialp))
           (equal (fp+ (rtz (fl (z*)) (p)) (p))
	          (+ (rtz (fl (z*)) (p)) 2)))
  :hints (("Goal" :in-theory (enable fp+)
                  :use (p-vals qrnd-7))))

(local-defthmd qrnd-18
  (implies (not (specialp))
           (equal (fp+ (rtz (fl (z*)) (p)) (p))
	          (+ (* 2 (bits (fl (z*)) (p) 1)) 2)))
  :hints (("Goal" :in-theory (enable qrnd-12) :use (qrnd-17 p-vals))))

(local-defthmd qrnd-19
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (bits (fl (z*)) (p) 0) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals (:instance bits-plus-bitn (x (fl (z*))) (n (p)) (m 0))))))

(local-defthmd qrnd-20
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (bits (fl (z*)) (1- (p)) 0) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-19
                        (:instance bitn-plus-bits (x (fl (z*))) (n (p)) (m 0))
			(:instance mod-mult (m (+ (- (bits (fl (z*)) (1- (p)) 0) (bitn (fl (z*)) 0)) 2))
			                    (a (bitn (fl (z*)) (p)))
					    (n (expt 2 (p))))))))

(local-defthmd qrnd-21
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (mod (fl (z*)) (expt 2 (p))) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-20) :in-theory (enable bits))))

(local-defthmd qrnd-22
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (+ (- (fl (z*)) (bitn (fl (z*)) 0)) 2) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-21
                        (:instance mod-sum (a (- 2 (bitn (fl (z*)) 0))) (b (fl (z*))) (n (expt 2 (p))))))))

(local-defthmd qrnd-23
  (implies (not (specialp))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (mod (+ (fl (z*)) 2) (expt 2 (p))) (bitn (fl (z*)) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (p-vals qrnd-22
                        (:instance mod-sum (a (- (bitn (fl (z*)) 0))) (b (+ 2 (fl (z*)))) (n (expt 2 (p))))))))

(local-defthm qrnd-24
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (or (= (stk) 1)
	       (= (bitn (qtrunc) 0) 1)))
  :rule-classes ()
  :hints (("Goal" :use (p-vals qrnd-5
                        (:instance bitn-bits (x (fl (z*))) (i (1- (p))) (j 0) (k 0)) 
                        (:instance bitn-bits (x (qtrunc)) (i (1- (p))) (j 0) (k 0)))
		  :in-theory (enable roundup-pos))))

(local-defthm qrnd-25
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (divpow2) 0))
  :rule-classes ()
  :hints (("Goal" :use (bvecp-mana p-vals qrnd-24 qtrunc-divpow2-5 stk-rewrite-divpow2
                        (:instance bitn-shift-up (x (mana)) (n -1) (k 1))))))

(local-defthmd qrnd-26
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (+ (fl (z*)) 2) (expt 2 (p)))
	          (mod (qinc) (expt 2 (p)))))
  :hints (("Goal" :in-theory (enable z*) :use (p-vals qrnd-25 qinc-rewrite))))

(local-defthmd qrnd-27
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (mod (qinc) (expt 2 (p))) (bitn (fl (z*)) 0)) (expt 2 (p)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (qrnd-23 qrnd-26))))

(local-defthm qrnd-28
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (and (integerp (p))
	        (integerp 0)
		(< 0 (p))))
  :rule-classes ()
  :hints (("Goal" :use (p-vals))))

(local-defthmd qrnd-29
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (bitn (qinc) 0)
                  (bitn (+ (fl (z*)) 2) 0)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (qrnd-26 qrnd-28 p-vals
		        (:instance bitn-mod (x (qinc)) (n (p)) (k 0))
			(:instance bitn-mod (x (+ (fl (z*)) 2)) (n (p)) (k 0))))))

(local-defthmd qrnd-30
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (bitn (qinc) 0)
                  (bitn (fl (z*)) 0)))
  :hints (("Goal" :use (qrnd-29
		        (:instance bitn-plus-mult (x (fl (z*))) (m 1) (k 1) (n 0))))))

(local-defthmd qrnd-31
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (mod (qinc) (expt 2 (p))) (bitn (qinc) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-27 qrnd-30 p-vals))))

(local-defthmd qrnd-32
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (- (bits (qinc) (1- (p)) 0) (bitn (qinc) 0)) (expt 2 (p)))))
  :hints (("Goal" :in-theory (enable bits) :use (qrnd-31 p-vals))))

(local-defthmd qrnd-33
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (+ (* 2 (bits (fl (z*)) (p) 1)) 2) (expt 2 (p)))
	          (mod (* 2 (bits (qinc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-32 p-vals (:instance bits-plus-bitn (x (qinc)) (n (1- (p))) (m 0))))))

(local-defthmd qrnd-34
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (rnd (z*) (modep) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qinc) (1- (p)) 1)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-10 qrnd-18 qrnd-33))))

(local-defthmd qrnd-35
  (implies (and (not (specialp))
                (roundup-pos (fl (z*)) (p) (stk) (modep) (p)))
           (equal (mod (rnd (z*) (modep) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-34 qrnd-11 p-vals
                        (:instance bits-bits (x (qinc)) (i 53) (j 1) (k (- (p) 2)) (l 0))))))

(local-defthmd rnd-x/d-qrnd
  (implies (not (specialp))
           (equal (mod (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p)) (expt 2 (p)))
	          (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p)))))
  :hints (("Goal" :use (qrnd-35 qrnd-16 p-vals)
                  :in-theory '(z*))))

(local-defthm rnd-bound-1
  (implies (not (specialp))
           (and (<= 1 (sig (a)))
	        (< (sig (a)) 2)
                (<= 1 (sig (b)))
	        (< (sig (b)) 2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sig-lower-bound (x (a)))
                        (:instance sig-upper-bound (x (a)))
			(:instance sig-lower-bound (x (b)))
                        (:instance sig-upper-bound (x (b)))))))

(defthm rnd-bound-2
  (implies (not (specialp))
           (and (equal (expo (sig (a))) 0)
	        (equal (expo (sig (b))) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sig-lower-bound (x (a)))
                        (:instance sig-upper-bound (x (a)))
			(:instance sig-lower-bound (x (b)))
                        (:instance sig-upper-bound (x (b)))
			(:instance expo-unique (x (sig (a))) (n 0))
			(:instance expo-unique (x (sig (b))) (n 0))))))

(defthm rnd-bound-3
  (implies (not (specialp))
           (and (exactp (sig (a)) (p))
	        (exactp (sig (b)) (p))))
  :rule-classes ()
  :hints (("Goal" :use (exactp-a exactp-b rnd-bound-2 p-vals)
                  :in-theory (enable exactp))))

(local-defthm rnd-bound-4
  (implies (not (specialp))
           (<= (sig (a)) (- 2 (expt 2 (- 1 (p))))))
  :rule-classes ()
  :hints (("Goal" :use (rnd-bound-3 p-vals
                        (:instance fp-2 (x 2) (y (sig (a))) (n (p)))))))

(local-defthm rnd-bound-5
  (implies (and (not (specialp))
                (< (sig (a)) (sig (b))))
           (<= (sig (a)) (- (sig (b)) (expt 2 (- 1 (p))))))
  :rule-classes ()
  :hints (("Goal" :use (rnd-bound-1 rnd-bound-2 rnd-bound-3 p-vals
                        (:instance fp-2 (x (sig (b))) (y (sig (a))) (n (p)))))))

(local-defthm rnd-bound-6
  (implies (and (not (specialp))
                (>= (sig (a)) (sig (b))))
           (equal (/ (x) (d)) (/ (sig (a)) (sig (b)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable x d)
                  :use ((:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(local-defthm rnd-bound-7
  (implies (and (not (specialp))
                (< (sig (a)) (sig (b))))
           (equal (/ (x) (d)) (/ (* 2 (sig (a))) (sig (b)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable x d)
                  :use ((:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(local-defthm rnd-bound-8
  (implies (and (not (specialp))
                (>= (sig (a)) (sig (b))))
           (<= (/ (x) (d)) (- 2 (expt 2 (- 1 (p))))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  :use (rnd-bound-6 rnd-bound-4 rnd-bound-1 p-vals))))

(local-defthm rnd-bound-9
  (implies (and (not (specialp))
                (< (sig (a)) (sig (b))))
           (<= (/ (x) (d)) (- 2 (expt 2 (- 1 (p))))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  :use (rnd-bound-7 rnd-bound-5 rnd-bound-1 p-vals))))

(local-defthm rnd-bound-10
  (implies (not (specialp))
           (<= (* (expt 2 (p)) (/ (x) (d))) (- (expt 2 (1+ (p))) 2)))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  :use (rnd-bound-8 rnd-bound-9 p-vals))))

(local-defthm rnd-quot-bound
  (implies (not (specialp))
           (<= (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))
	       (- (expt 2 (1+ (p))) 2)))
  :rule-classes ()
  :hints (("Goal" :use (qrnd-4 rnd-bound-10 p-vals
                        (:instance rnd-exactp-b (x (- (expt 2 (1+ (p))) 2)) (n (p)) (mode (modep)))
                        (:instance rnd-monotone (x (* (expt 2 (p)) (/ (x) (d))))
			                        (y (- (expt 2 (1+ (p))) 2))
						(mode (modep))
						(n (p)))))))

(defthmd rnd-inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (= (rnd (abs (/ (a) (b))) (modep) (p))
		         (abs (/ (a) (b))))
		      0 1)))
  :hints (("Goal" :use (qrnd-4 p-vals quotient-expq
                        (:instance exactp-shift (k (- (si (expq) 13) (bias (f)))) (x (/ (x) (d))) (n (p)))
                        (:instance rnd-exactp-b (x (abs (/ (a) (b)))) (mode (modep)) (n (p))))
		  :in-theory (enable inx-rewrite))))

(local-defthmd rnd-a/b-1
  (implies (not (specialp))
           (equal (expo (* (expt 2 (p)) (/ (x) (d)))) (p)))
  :hints (("Goal" :nonlinearp t
                  :use (p-vals x-bounds d-bounds
                        (:instance expo-unique (x (* (expt 2 (p)) (/ (x) (d)))) (n (p)))))))

(local-defthmd rnd-a/b-2
  (implies (not (specialp))
           (equal (expo (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p)))
	          (p)))
  :hints (("Goal" :use (p-vals qrnd-4 rnd-quot-bound rnd-a/b-1
                        (:instance expo-rnd (x (* (expt 2 (p)) (/ (x) (d)))) (mode (modep)) (n (p)))))))

(local-defthmd rnd-a/b-3
  (implies (not (specialp))
           (equal (fl (/ (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))
	                 (expt 2 (p))))
	          1))
  :hints (("Goal" :use (p-vals rnd-a/b-2
                        (:instance expo-upper-bound (x (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))))
                        (:instance expo-lower-bound (x (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))))))))

(local-defthmd rnd-a/b-4
  (implies (not (specialp))
           (equal (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))
	          (+ (expt 2 (p))
		     (mod (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p)) (expt 2 (p))))))
  :hints (("Goal" :use (p-vals rnd-a/b-3
                        (:instance mod-def (x (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))) (y (expt 2 (p))))))))

(local-defthmd rnd-a/b-4
  (implies (not (specialp))
           (equal (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))
	          (+ (expt 2 (p))
		     (mod (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p)) (expt 2 (p))))))
  :hints (("Goal" :use (p-vals rnd-a/b-3
                        (:instance mod-def (x (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))) (y (expt 2 (p))))))))

(local-defthmd rnd-a/b-5
  (implies (not (specialp))
           (equal (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))
	          (+ (expt 2 (p))
		     (mod (* 2 (bits (qrnd) (- (p) 2) 0)) (expt 2 (p))))))
  :hints (("Goal" :use (p-vals rnd-a/b-4 rnd-x/d-qrnd))))

(local-defthmd rnd-a/b-6
  (implies (not (specialp))
           (equal (rnd (* (expt 2 (p)) (/ (x) (d))) (modep) (p))
	          (+ (expt 2 (p))
		     (* 2 (bits (qrnd) (- (p) 2) 0)))))
  :hints (("Goal" :use (p-vals rnd-a/b-5
                        (:instance bits-bounds (x (qrnd)) (i (- (p) 2)) (j 0))))))

(defthmd rnd-a/b-qrnd
  (implies (not (specialp))
           (equal (rnd (abs (/ (a) (b))) (modep) (p))
	          (* (expt 2 (+ (si (expq) 13) (- (bias (f))) (- (1- (p)))))
		     (+ (expt 2 (1- (p)))
		        (bits (qrnd) (- (p) 2) 0)))))
  :hints (("Goal" :in-theory (enable si bias f sp dp hp prec p)
                  :use (fnum-vals rnd-a/b-6 quotient-expq qrnd-4
                        (:instance rnd-shift (x (* (expt 2 (p)) (/ (x) (d))))
			                     (n (p))
					     (mode (modep))
					     (k (+ (si (expq) 13) (- (bias (f))) (- (p)))))))))

(local-defthmd drnd-1
  (implies (not (specialp))
           (equal (qden)
	          (+ (expt 2 (p))
		     (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p))))))
  :hints (("Goal" :in-theory (enable bits cat si bias f sp dp hp prec p qden)
                  :use (fnum-vals qtrunc-rewrite-gen))))

(local-defthmd drnd-2
  (implies (not (specialp))
           (equal (fl (/ (fl (* (expt 2 (p)) (/ (x) (d))))
	                 (expt 2 (p))))
	          1))
  :hints (("Goal" :use (p-vals rnd-a/b-1
                        (:instance expo-upper-bound (x (* (expt 2 (p)) (/ (x) (d)))))
                        (:instance expo-lower-bound (x (* (expt 2 (p)) (/ (x) (d)))))))))

(local-defthmd drnd-3
  (implies (not (specialp))
           (equal (qden)
	          (fl (* (expt 2 (p)) (/ (x) (d))))))
  :hints (("Goal" :use (p-vals drnd-1 drnd-2 (:instance mod-def (x (fl (* (expt 2 (p)) (/ (x) (d))))) (y (expt 2 (p))))))))

(local-defthmd ash-rewrite
  (equal (ash i c)
         (fl (* (IFIX I) (EXPT 2 C))))
  :hints (("Goal" :in-theory (enable floor fl ash))))

(local-defthmd drnd-4
  (implies (not (specialp))
           (bvecp (fl (* (expt 2 (- (p) (shft))) (/ (x) (d)))) 64))
  :hints (("Goal" :in-theory (enable bvecp ash-rewrite drnd-3 shft rshft64 qshft)
                  :nonlinearp t
                  :use (p-vals rnd-a/b-1
		        (:instance expo-upper-bound (x (* (expt 2 (p)) (/ (x) (d)))))
		        (:instance expo-lower-bound (x (* (expt 2 (p)) (/ (x) (d)))))))))
			
(local-defthmd drnd-5
  (implies (not (specialp))
           (equal (qshft)
	          (fl (* (expt 2 (- (p) (shft))) (/ (x) (d))))))
  :hints (("Goal" :in-theory (e/d (bvecp ash-rewrite drnd-3 qshft rshft64) (fl/int-rewrite))
                  :use (p-vals rnd-a/b-1 drnd-4
		        (:instance expo-upper-bound (x (* (expt 2 (p)) (/ (x) (d)))))
		        (:instance expo-lower-bound (x (* (expt 2 (p)) (/ (x) (d)))))
			(:instance fl/int-rewrite (x (* (expt 2 (p)) (/ (x) (d)))) (n (expt 2 (shft))))))))

(local-defthmd drnd-6
  (implies (not (specialp))
           (and (integerp (qshft))
	        (<= (qshft) (* (expt 2 (- (shft))) (qden)))
                (equal (stkden-0)
	               (if (= (qshft) (* (expt 2 (- (shft))) (qden)))
		           0 1))))
  :hints (("Goal" :use (p-vals drnd-4
		        (:instance expo-upper-bound (x (* (expt 2 (p)) (/ (x) (d)))))
		        (:instance expo-lower-bound (x (* (expt 2 (p)) (/ (x) (d)))))
			(:instance fl/int-rewrite (x (* (expt 2 (p)) (/ (x) (d)))) (n (expt 2 (shft)))))
                  :in-theory (e/d (drnd-3 drnd-5 ash-rewrite rshft64 stkden-0) (FL*1/INT-REWRITE-ALT)))))

(local-defthmd drnd-7
  (implies (not (specialp))
           (and (<= (qden) (* (expt 2 (p)) (/ (x) (d))))
                (equal (stk)
	               (if (= (qden) (* (expt 2 (p)) (/ (x) (d))))
		           0 1))))
  :hints (("Goal" :use (p-vals)
                  :in-theory (enable drnd-3 stk-rewrite-gen))))

(local-defthmd drnd-8
  (implies (and (not (specialp))
                (equal (stkden) 0))
           (equal (qshft) (* (expt 2 (- (p) (shft))) (/ (x) (d)))))
  :hints (("Goal" :use (p-vals drnd-7 drnd-6)
                  :nonlinearp t
                  :in-theory (enable stkden))))

(local-defthmd drnd-9
  (implies (and (not (specialp))
                (equal (stkden) 1))
           (< (qshft) (* (expt 2 (- (p) (shft))) (/ (x) (d)))))
  :hints (("Goal" :use (p-vals drnd-7 drnd-6)
                  :nonlinearp t
                  :in-theory (enable stkden))))

(local-defthmd drnd-10
  (implies (not (specialp))
           (equal (stkden)
                  (if (= (qshft) (* (expt 2 (- (p) (shft))) (/ (x) (d))))
                      0 1)))
  :hints (("Goal" :use (p-vals drnd-8 drnd-9))))

(local-defthmd drnd-11
  (implies (not (specialp))
           (equal (expo (abs (/ (a) (b))))
	          (- (si (expq) 13) (bias (f)))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable si bias prec p f sp dp hp)
                  :use (fnum-vals x-bounds d-bounds quotient-expq
                        (:instance expo-unique (x (* (expt 2 (- (si (expq) 13) (bias (f)))) (/ (x) (d))))
			                       (n (- (si (expq) 13) (bias (f)))))))))

(defthmd drnd-12
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f)))))
           (<= (si (expq) 13) 0))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable si bias prec p f sp dp hp)
                  :use (fnum-vals drnd-11))))

(local-defthm drnd-13
  (implies (not (specialp))
           (integerp (si (expq) 13)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable si))))

(local-defthmd drnd-14
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
	   (equal (shft) (- 1 (si (expq) 13))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable shft shft12 bvecp)
                  :use (p-vals drnd-12))))

(local-defund n@ () (- (p) (shft)))

(local-defund z@ () (* (expt 2 (- (p) (shft))) (/ (x) (d))))

(local (in-theory (disable (n@) (z@))))

(local-defthm integerp-n@
  (integerp (n@))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable n@ shft shft12) :use (p-vals))))

(local-defthmd n@>0
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (> (n@) 0))
  :hints (("Goal" :in-theory (enable n@ drnd-14) :use (p-vals))))

(local-defthmd z@-rewrite
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (z@) (* (expt 2 (n@)) (/ (x) (d)))))
  :hints (("Goal" :in-theory (enable z@ n@ drnd-14) :use (p-vals))))

(local-defthmd drnd-15
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (qshft) (fl (z@))))
  :hints (("Goal" :in-theory (enable z@ drnd-5))))

(local-defthmd drnd-16
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (drnd (abs (/ (a) (b))) (modep) (f))
	          (rnd (abs (/ (a) (b))) (modep) (n@))))
  :hints (("Goal" :in-theory (enable drnd-14 drnd sp dp hp f bias spn n@ p prec)
                  :use (drnd-11))))

(local-defthmd drnd-17
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (iff (= (drnd (abs (/ (a) (b))) (modep) (f))
	           (abs (/ (a) (b))))
		(exactp (/ (x) (d)) (n@))))
  :hints (("Goal" :in-theory (enable bias p prec dp sp hp f)
                  :use (fnum-vals drnd-16 qrnd-4 n@>0 quotient-expq
                        (:instance exactp-shift (x (/ (x) (d))) (k (- (si (expq) 13) (bias (f)))) (n (n@)))
                        (:instance rnd-exactp-b (x (abs (/ (a) (b)))) (mode (modep)) (n (n@)))))))

(local-defthmd drnd-18
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (iff (exactp (/ (x) (d)) (n@))
	        (integerp (* (expt 2 (1- (n@))) (/ (x) (d))))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable exactp2)
                  :use (n@>0 x-bounds d-bounds (:instance expo-unique (x (/ (x) (d))) (n 0))))))

(local-defthmd drnd-19
  (implies (integerp x)
           (integerp (* 2 x))))

(local-defthmd drnd-20
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p)))
	        (integerp (* (expt 2 (1- (n@))) (/ (x) (d)))))
	   (integerp (* (expt 2 (n@)) (/ (x) (d)))))
  :hints (("Goal" :use ((:instance drnd-19 (x (* (expt 2 (1- (n@))) (/ (x) (d)))))))))

(local-defthmd drnd-21
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (iff (exactp (/ (x) (d)) (n@))
	        (and (integerp (* (expt 2 (n@)) (/ (x) (d))))
		     (= (bitn (* (expt 2 (n@)) (/ (x) (d))) 0) 0))))
  :hints (("Goal" :nonlinearp t :use (drnd-20 n@>0 drnd-18 (:instance mod-def (x (* (expt 2 (n@)) (/ (x) (d)))) (y 2)))
                  :in-theory (enable bitn-rec-0))))

(local-defthmd drnd-22
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (iff (exactp (/ (x) (d)) (n@))
	        (= (inxden) 0)))
  :hints (("Goal" :use (drnd-21 p-vals)
                  :in-theory (enable inxden* rounder-lemma grdden drnd-10 n@ drnd-15 z@))))

(local-defthmd drnd-23
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (iff (= (drnd (abs (/ (a) (b))) (modep) (f))
	           (abs (/ (a) (b))))
	        (= (inxden) 0)))
  :hints (("Goal" :use (drnd-17 drnd-22))))

(local-defthmd z@>0
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
	   (> (z@) 0))
  :hints (("Goal" :in-theory (enable z@-rewrite) :use (x-bounds d-bounds))))

(local-defthmd expo-z@
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
	   (equal (expo (z@)) (n@)))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable z@-rewrite)
                  :use (x-bounds d-bounds (:instance expo-unique (x (z@)) (n (n@)))))))

(local-defthmd expo-fl-z@
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
	   (equal (expo (fl (z@))) (n@)))
  :hints (("Goal" :use (z@>0 n@>0 expo-z@
                        (:instance expo-lower-bound (x (z@)))
                        (:instance expo-upper-bound (x (z@)))
		        (:instance expo-unique (x (fl (z@))) (n (n@)))))))

(local-defthmd drnd-24
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
	   (<= (expt 2 (n@)) (z@)))
  :hints (("Goal" :use (z@>0 n@>0 expo-z@
                        (:instance expo-lower-bound (x (z@)))))))

(local-defthmd drnd-25
  (implies (not (specialp))
           (equal (stkden)
                  (if (integerp (z@))
                      0 1)))
  :hints (("Goal" :in-theory (enable z@ drnd-5 drnd-10))))

(local-defthmd drnd-26
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (rnd (z@) (modep) (n@))
	          (if (roundup-pos (fl (z@)) (n@) (stkden) (modep) (n@))
		      (fp+ (rtz (fl (z@)) (n@)) (n@))
		    (rtz (fl (z@)) (n@)))))
  :hints (("Goal" :use (expo-fl-z@ qrnd-4 z@>0 n@>0 drnd-24 drnd-25
                        (:instance roundup-pos-thm (mode (modep)) (z (z@)) (n (n@)))))))

(local-defthmd drnd-27
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (<= (n@) (1- (p))))
  :hints (("Goal" :use (drnd-12) :in-theory (enable n@ drnd-14))))

(local-defthmd drnd-28
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (< (bits (fl (z@)) 53 1) (expt 2 (1- (p)))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable bvecp expo-fl-z@)
                  :use (drnd-27 p-vals z@>0
		        (:instance bits-plus-bitn (x (fl (z@))) (n 53) (m 0))
		        (:instance expo-upper-bound (x (fl (z@))))))))

(local-defthmd drnd-29
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (qrndden)
	          (if (roundup-pos (fl (z@)) (n@) (stkden) (modep) (n@))
		      (1+ (bits (qshft) 53 1))
		    (bits (qshft) 53 1))))
  :hints (("Goal" :in-theory (enable drnd-15 drnd-25 sign-rewrite roundup-pos qrndden* rounder-lemma lsbden grdden modep
                                     bvecp mode rmode)
                  :use (n@>0 z@>0 drnd-28 p-vals
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd drnd-30
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (bits (qshft) (n@) 1)
	          (bits (qshft) (p) 1)))
  :hints (("Goal" :in-theory (enable bits drnd-15 expo-fl-z@)
                  :nonlinearp t
                  :use (p-vals drnd-27 (:instance expo-upper-bound (x (fl (z@))))))))

(local-defthmd drnd-31
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p)))
		(not (roundup-pos (fl (z@)) (n@) (stkden) (modep) (n@))))
           (equal (rtz (fl (z@)) (n@))
	          (* 2 (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :in-theory (e/d (drnd-15 drnd-29) (bits-bits))
                  :use (drnd-30 z@>0 n@>0 p-vals expo-fl-z@
		        (:instance bits-bits (x (qshft)) (i 53) (j 1) (k (1- (p))) (l 0))
		        (:instance bits-rtz (x (qshft)) (k (n@)) (n (1+ (n@))))))))

(local-defthmd drnd-32
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p)))
		(roundup-pos (fl (z@)) (n@) (stkden) (modep) (n@)))
           (equal (fp+ (rtz (fl (z@)) (n@)) (n@))
	          (* 2 (1+ (bits (qshft) (n@) 1)))))
  :hints (("Goal" :in-theory (enable drnd-15)
                  :use (z@>0 n@>0 p-vals expo-fl-z@ drnd-28
		        (:instance bits-rtz (x (qshft)) (k (n@)) (n (1+ (n@))))))))

(local-defthmd drnd-33
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (bits (qshft) (n@) 1)
	          (bits (qshft) 53 1)))
  :hints (("Goal" :in-theory (enable bits drnd-15 expo-fl-z@)
                  :nonlinearp t
                  :use (p-vals drnd-27 (:instance expo-upper-bound (x (fl (z@))))))))

(local-defthmd drnd-34
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p)))
		(roundup-pos (fl (z@)) (n@) (stkden) (modep) (n@)))
           (equal (fp+ (rtz (fl (z@)) (n@)) (n@))
	          (* 2 (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :in-theory (enable bvecp drnd-15 drnd-29)
                  :use (p-vals drnd-28 drnd-32 drnd-33))))

(local-defthmd drnd-35
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (rnd (z@) (modep) (n@))
	          (* 2 (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :in-theory (enable drnd-26)
                  :use (drnd-34 drnd-31))))

(local-defthmd drnd-36
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(> (si (expq) 13) (- 1 (p))))
           (equal (drnd (abs (/ (a) (b))) (modep) (f))
	          (* (expt 2 (+ 1 (- (bias (f))) (- (1- (p)))))
		     (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :in-theory (enable n@ drnd-14 z@-rewrite si bias f sp dp hp prec p)
                  :use (fnum-vals drnd-35 quotient-expq qrnd-4 drnd-16
                        (:instance rnd-shift (x (* (expt 2 (n@)) (/ (x) (d))))
			                     (n (n@))
					     (mode (modep))
					     (k (+ (si (expq) 13) (- (bias (f))) (- (n@)))))))))

(defthmd si-expq-bounds
  (implies (not (specialp))
           (and (< (si (expq) 13) (expt 2 12))
	        (> (si (expq) 13) (- 1 (expt 2 12)))))
  :hints (("Goal" :use (si-expdiff-bounds expq-expdiff))))

(local-defthmd drnd-37
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (>= (shft) (p)))
  :hints (("Goal" :use (p-vals si-expq-bounds) :in-theory (enable bvecp shft shft12))))

(local-defthmd drnd-38
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(rationalp x)
		(> x 0)
		(< x 2))
           (< (* (expt 2 (- (p) (shft))) x) 2))
  :hints (("Goal" :use (p-vals drnd-37) :nonlinearp t)))

(local-defthmd drnd-39
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (and (rationalp (/ (x) (d)))
	        (> (/ (x) (d)) 0)
		(< (/ (x) (d)) 2)))
  :hints (("Goal" :use (x-bounds d-bounds) :nonlinearp t)))

(local-defthmd drnd-40
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (< (qshft) 2))
  :hints (("Goal" :use (p-vals x-bounds d-bounds drnd-39
                        (:instance drnd-38 (x (/ (x) (d)))))
	          :in-theory (enable drnd-5))))

(local-defthmd drnd-41
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (< (abs (/ (a) (b)))
	      (spd (f))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable bias f sp dp hp p prec)
                  :use (fnum-vals quotient-expq x-bounds d-bounds))))

(local-defthm drnd-42
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (or (= (drnd (abs (/ (a) (b))) (modep) (f)) 0)
	       (= (drnd (abs (/ (a) (b))) (modep) (f)) (spd (f)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bias f sp dp hp p prec)
                  :use (fnum-vals drnd-41 qrnd-4
		        (:instance drnd-tiny-a (x (abs (/ (a) (b)))) (mode (modep)) (f (f)))
		        (:instance drnd-tiny-b (mode (modep)) (f (f)))
		        (:instance drnd-tiny-c (x (abs (/ (a) (b)))) (mode (modep)) (f (f)))))))

(local-defthm drnd-43
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (not (= (drnd (abs (/ (a) (b))) (modep) (f))
	           (abs (/ (a) (b))))))  
  :rule-classes ()
  :hints (("Goal" :use (drnd-41 drnd-42))))

(local-defthm drnd-44
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (and (member (qshft) '(0 1))
                (equal (inxden) 1)))
  :rule-classes ()
  :hints (("Goal" :use (drnd-40 drnd-8 drnd-5 d-bounds x-bounds) :in-theory (enable grdden inxden* rounder-lemma))))

(local-defthmd drnd-45
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f)))))
           (iff (= (drnd (abs (/ (a) (b))) (modep) (f))
	           (abs (/ (a) (b))))
	        (= (inxden) 0)))
  :hints (("Goal" :use (drnd-23 drnd-43 drnd-44))))

(local-defthmd drnd-46
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (lsbden) 0))
  :hints (("Goal" :use (drnd-44) :in-theory (enable lsbden))))

(local-defthmd drnd-47
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (iff (= (grdden) 1)
	        (>= (* (expt 2 (- (p) (shft))) (/ (x) (d)))
		    1)))
  :hints (("Goal" :use (drnd-44) :in-theory (enable drnd-5 grdden))))

(local-defthmd drnd-48
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (iff (>= (* (expt 2 (- (p) (shft))) (/ (x) (d))) 1)
	        (>= (- (p) (shft)) 0)))
  :hints (("Goal" :use (p-vals drnd-47 x-bounds d-bounds) :nonlinearp t)))

(local-defthmd drnd-49
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (iff (>= (- (p) (shft)) 0)
	        (>= (si (expq) 13) (- 1 (p)))))
  :hints (("Goal" :use (p-vals si-expq-bounds) :in-theory (enable bvecp shft shft12))))

(local-defthmd drnd-50
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (iff (= (grdden) 1)
	        (>= (expo (abs (/ (a) (b)))) (- 1 (+ (bias (f)) (p))))))
  :hints (("Goal" :use (fnum-vals drnd-11 drnd-47 drnd-48 drnd-49)
                  :in-theory (enable bias f sp dp hp p prec))))

(local-defthmd drnd-51
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (grdden)
	          (if (>= (abs (/ (a) (b))) (/ (spd (f)) 2))
		      1 0)))
  :hints (("Goal" :nonlinearp t
                  :use (fnum-vals drnd-50
                        (:instance expo-upper-bound (x (abs (/ (a) (b)))))
                        (:instance expo-lower-bound (x (abs (/ (a) (b))))))
                  :in-theory (enable grdden bias f sp dp hp p prec))))

(local-defthmd drnd-52
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (stkden)
	          (if (integerp (* (expt 2 (- (p) (shft))) (/ (x) (d))))
		      0 1)))
  :hints (("Goal" :use (p-vals)
                  :in-theory (enable drnd-10 drnd-5))))

(local-defthm drnd-53
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (and (<= (expt 2 (- (p) (shft))) 1)
	        (> (expt 2 (- (p) (shft))) 0)
	        (rationalp (expt 2 (- (p) (shft))))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :use (drnd-37 p-vals))))

(local-defthmd drnd-54
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (and (< (/ (x) (d)) 2)
	        (>= (/ (x) (d)) 1)
	        (rationalp (/ (x) (d)))))
  :hints (("Goal" :nonlinearp t :use (x-bounds d-bounds))))

(local-defthm drnd-55
  (implies (and (integerp a) (<= a 0))
           (or (= (expt 2 a) 1) (<= (expt 2 a) 1/2)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes ())
  
(local-defthm drnd-56
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (or (= (expt 2 (- (p) (shft))) 1)
	       (<= (expt 2 (- (p) (shft))) 1/2)))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :use (drnd-37 p-vals (:instance drnd-55 (a (- (p) (shft))))))))

(local-defthm drnd-57
  (implies (and (rationalp a) (<= a 1) (> a 0) (or (= a 1) (<= a 1/2))
                (rationalp b) (< b 2) (>= b 1))
	   (iff (= (* a b) 1)
	        (and (= a 1) (= b 1))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes ())

(local-defthm drnd-58
  (implies (and (rationalp a) (<= a 1) (> a 0) (or (= a 1) (<= a 1/2))
                (rationalp b) (< b 2) (>= b 1))
	   (iff (integerp (* a b))
	        (= (* a b) 1)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes ())

(local-defthm drnd-59
  (implies (and (rationalp a) (<= a 1) (> a 0) (or (= a 1) (<= a 1/2))
                (rationalp b) (< b 2) (>= b 1))
	   (iff (integerp (* a b))
	        (and (= a 1) (= b 1))))
  :hints (("Goal" :use (drnd-57 drnd-58)))
  :rule-classes ())

(local-defthmd drnd-60
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (iff (integerp (* (expt 2 (- (p) (shft))) (/ (x) (d))))
		(and (= (expt 2 (- (p) (shft))) 1)
		     (= (/ (x) (d)) 1))))
  :hints (("Goal" :use (drnd-53 drnd-54 drnd-56
                        (:instance drnd-59 (a (expt 2 (- (p) (shft)))) (b (/ (x) (d)))))
                  :in-theory (enable drnd-10 drnd-5))))

(local-defthmd drnd-61
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (stkden)
	          (if (and (= (expt 2 (- (p) (shft))) 1)
   		           (= (/ (x) (d)) 1))
		      0 1)))
  :hints (("Goal" :use (drnd-60 drnd-52))))

(local-defthmd drnd-62
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (stkden)
	          (if (and (= (p) (shft)) (= (x) (d)))
		      0 1)))
  :hints (("Goal" :use (drnd-61 p-vals d-bounds x-bounds))))

(local-defthmd drnd-63
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(= (shft) (p)))
	   (equal (si (expq) 13) (- 1 (p))))
  :hints (("Goal" :use (p-vals si-expq-bounds) :in-theory (enable bvecp shft shft12))))

(local-defthmd drnd-64
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(= (stkden) 0))
	   (equal (abs (/ (a) (b))) (/ (spd (f)) 2)))
  :hints (("Goal" :use (fnum-vals drnd-63 quotient-expq) :in-theory (enable drnd-62 bias f sp dp hp p prec))))

(local-defthmd drnd-65
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(= (stkden) 0))
	   (equal (abs (/ (a) (b))) (/ (spd (f)) 2)))
  :hints (("Goal" :use (fnum-vals drnd-63 quotient-expq) :in-theory (enable drnd-62 bias f sp dp hp p prec))))

(local-defthmd drnd-66
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(= (abs (/ (a) (b))) (/ (spd (f)) 2)))
	   (equal (* (expt 2 (1- (+ (p) (si (expq) 13)))) (/ (x) (d)))
	          1))
  :hints (("Goal" :nonlinearp t :use (fnum-vals quotient-expq) :in-theory (enable bias f sp dp hp p prec))))

(local-defthmd drnd-67
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (and (integerp (1- (+ (p) (si (expq) 13))))
		(rationalp (/ (x) (d)))
		(< (/ (x) (d)) 2)
		(>= (/ (x) (d)) 1)))
  :hints (("Goal" :nonlinearp t :use (p-vals x-bounds d-bounds))))

(local-defthm drnd-68
  (implies (and (integerp a) (< a 0) (rationalp x) (>= x 1) (< x 2))
           (< (* (expt 2 a) x) 1))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t)))

(local-defthm drnd-69
  (implies (and (integerp a) (> a 0) (rationalp x) (>= x 1) (< x 2))
           (>= (* (expt 2 a) x) 2))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t)))

(local-defthm drnd-70
  (implies (and (integerp a) (rationalp x) (>= x 1) (< x 2)
                (= (* (expt 2 a) x) 1))
	   (and (= a 0) (= x 1)))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :use (drnd-68 drnd-69))))

(local-defthmd drnd-71
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(= (abs (/ (a) (b))) (/ (spd (f)) 2)))
	   (and (equal (si (expq) 13) (- 1 (p)))
	        (equal (/ (x) (d)) 1)))
  :hints (("Goal" :use (drnd-66 drnd-67 (:instance drnd-70 (a (1- (+ (p) (si (expq) 13)))) (x (/ (x) (d))))))))

(local-defthmd drnd-72
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p)))
		(= (abs (/ (a) (b))) (/ (spd (f)) 2)))
	   (equal (stkden) 0))
  :hints (("Goal" :use (drnd-71 p-vals) :in-theory (enable drnd-61 shft shft12 bvecp))))

(local-defthmd drnd-73
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (stkden)
	          (if (= (abs (/ (a) (b))) (/ (spd (f)) 2))
		      0 1)))
  :hints (("Goal" :use (drnd-64 drnd-61 drnd-72))))

(local-defthmd drnd-73
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
	   (equal (stkden)
	          (if (= (abs (/ (a) (b))) (/ (spd (f)) 2))
		      0 1)))
  :hints (("Goal" :use (drnd-64 drnd-61 drnd-72))))

(local-defthmd drnd-74
  (implies (not (specialp))
           (iff (<= (si (expq) 13) (- 1 (p)))
	        (< (abs (/ (a) (b))) (spd (f)))))
  :hints (("Goal" :in-theory (enable bias f sp dp hp prec p)
                  :use (fnum-vals drnd-11
		        (:instance expo>= (x (abs (/ (a) (b)))) (n (+ 2 (- (bias (f))) (- (p)))))
			(:instance expo<= (x (abs (/ (a) (b)))) (n (+ 1 (- (bias (f))) (- (p)))))))))

(local-defthmd drnd-75
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f))))
		(<= (si (expq) 13) (- 1 (p))))
           (equal (drnd (abs (/ (a) (b))) (modep) (f))
	          (* (expt 2 (+ 1 (- (bias (f))) (- (1- (p)))))
		     (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :in-theory (enable drnd-46 drnd-51 drnd-73 qrndden* rounder-lemma bias f sp dp hp prec p
                                     sign-rewrite bvecp modep mode rmode)
                  :use (fnum-vals drnd-44 qrnd-4 drnd-74
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
			(:instance drnd-tiny-a (f (f)) (mode (modep)) (x (abs (/ (a) (b)))))
			(:instance drnd-tiny-b (f (f)) (mode (modep)))
			(:instance drnd-tiny-c (f (f)) (mode (modep)) (x (abs (/ (a) (b)))))))))

(local-defthmd drnd-76
  (implies (and (not (specialp))
                (< (expo (abs (/ (a) (b)))) (- 1 (bias (f)))))
           (equal (drnd (abs (/ (a) (b))) (modep) (f))
	          (* (expt 2 (+ 1 (- (bias (f))) (- (1- (p)))))
		     (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :use (drnd-36 drnd-75))))

(defthmd drnd-77
  (implies (and (not (specialp))
                (< (abs (/ (a) (b))) (spn (f))))
           (< (expo (abs (/ (a) (b)))) (- 1 (bias (f)))))
  :hints (("Goal" :in-theory (enable bias f sp dp hp prec p)
                  :use (fnum-vals
                        (:instance expo<= (x (abs (/ (a) (b)))) (n (- (bias (f)))))))))

(defthmd drnd-inxden-rewrite
  (implies (and (not (specialp))
                (< (abs (/ (a) (b))) (spn (f))))
           (equal (inxden)
	          (if (= (drnd (abs (/ (a) (b))) (modep) (f))
	                 (abs (/ (a) (b))))
	              0 1)))
  :hints (("Goal" :use (drnd-45 drnd-77) :in-theory (enable rounder-lemma))))

(defthmd drnd-a/b-qrndden
  (implies (and (not (specialp))
                (< (abs (/ (a) (b))) (spn (f))))
           (equal (drnd (abs (/ (a) (b))) (modep) (f))
	          (* (expt 2 (+ 1 (- (bias (f))) (- (1- (p)))))
		     (bits (qrndden) (1- (p)) 0))))
  :hints (("Goal" :use (drnd-76 drnd-77))))
