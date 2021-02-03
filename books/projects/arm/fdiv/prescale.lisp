(in-package "RTL")

(include-book "normalize")

(defund mul ()
  (case (bits (sigb) 51 49)
    (0 2)
    (1 7/4)
    (2 13/8)
    (3 3/2)
    (4 11/8)
    (5 5/4)
    (6 9/8)
    (7 9/8)))

(defund d () (* (mul) (sig (b)) 1/2))

(defund x ()
  (if (>= (sig (a)) (sig (b)))
      (* (mul) (sig (a)) 1/2)
    (* (mul) (sig (a)))))

(in-theory (disable (mul) (x) (d)))

(defthm sigb-bounds
  (implies (not (specialp))
           (and (< (sigb) (expt 2 53))
                (>= (sigb) (expt 2 52))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigb-rewrite)
                  :use (a-b-not-zero
                        (:instance sig-lower-bound (x (b)))
                        (:instance sig-upper-bound (x (b))))
                  :nonlinearp t)))

(local-defthmd mod-sigb
  (implies (not (specialp))
           (equal (mod (sigb) (expt 2 52))
                  (- (sigb) (expt 2 52))))
  :hints (("Goal" :use (sigb-bounds (:instance mod-force (m (sigb)) (n (expt 2 52)) (a 1))))))

(local-defthmd bits-sigb
  (implies (not (specialp))
           (equal (bits (sigb) 51 49)
                  (fl (* 8 (1- (sig (b)))))))
  :hints (("Goal" :use (mod-sigb) :in-theory (enable sigb-rewrite bits))))

(local-defthmd bits-sigb-bounds
  (implies (not (specialp))
           (and (<= (/ (+ (bits (sigb) 51 49) 8) 8) (sig (b)))
	        (< (sig (b)) (/ (+ (bits (sigb) 51 49) 9) 8))))
  :hints (("Goal" :in-theory (enable bits-sigb) :nonlinearp t)))

(defthmd d-bounds
  (implies (not (specialp))
           (and (<= 63/64 (d))
	        (<= (d) 9/8)))
  :hints (("Goal" :in-theory (enable d mul)
                  :use (bits-sigb-bounds
		        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(defthmd x-bounds
  (implies (not (specialp))
           (and (<= (d) (x))
	        (< (x) (* 2 (d)))))
  :hints (("Goal" :in-theory (enable d x mul)
                  :use (a-b-not-zero
		        (:instance sig-upper-bound (x (a)))
		        (:instance sig-lower-bound (x (a)))
		        (:instance sig-upper-bound (x (b)))
		        (:instance sig-lower-bound (x (b)))
		        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(defund div1 ()
  (if1 (logand1 (lognot1 (bitn (sigb) 51))
                (logior1 (bitn (sigb) 50)
                         (lognot1 (bitn (sigb) 49))))
       (bits (ash (sigb) 2) 55 0)
       (if1 (logand1 (lognot1 (bitn (sigb) 50))
                     (logior1 (bitn (sigb) 51) (bitn (sigb) 49)))
            (bits (ash (sigb) 1) 55 0)
            (bits 0 55 0))))

(defund div2 ()
  (if1 (logand1 (lognot1 (bitn (sigb) 51))
                (lognot1 (bitn (sigb) 50)))
       (bits (ash (sigb) 2) 55 0)
       (if1 (logior1 (logand1 (logior1 (bitn (sigb) 51) (bitn (sigb) 50))
                              (lognot1 (bitn (sigb) 49)))
                     (logand1 (bitn (sigb) 51) (bitn (sigb) 50)))
            (sigb)
            (bits 0 55 0))))

(defund div3 () (bits (ash (sigb) 3) 55 0))

(defund divsum () (logxor (logxor (div1) (div2)) (div3)))

(defund divcar ()
  (bits (ash (logior (logior (logand (div1) (div2))
                             (logand (div1) (div3)))
                     (logand (div2) (div3)))
             1)
        55 0))

(defund div* () (bits (+ (divsum) (divcar)) 56 0))

(defund rem1 ()
  (if1 (logand1 (lognot1 (bitn (sigb) 51))
                (logior1 (bitn (sigb) 50)
                         (lognot1 (bitn (sigb) 49))))
       (bits (ash (siga) 2) 55 0)
       (if1 (logand1 (lognot1 (bitn (sigb) 50))
                     (logior1 (bitn (sigb) 51) (bitn (sigb) 49)))
            (bits (ash (siga) 1) 55 0)
            (bits 0 55 0))))

(defund rem2 ()
  (if1 (logand1 (lognot1 (bitn (sigb) 51))
                (lognot1 (bitn (sigb) 50)))
       (bits (ash (siga) 2) 55 0)
       (if1 (logior1 (logand1 (logior1 (bitn (sigb) 51) (bitn (sigb) 50))
                              (lognot1 (bitn (sigb) 49)))
                     (logand1 (bitn (sigb) 51) (bitn (sigb) 50)))
            (siga)
            (bits 0 55 0))))

(defund rem3 () (bits (ash (siga) 3) 55 0))

(defund remsum () (logxor (logxor (rem1) (rem2)) (rem3)))

(defund remcar ()
  (bits (ash (logior (logior (logand (rem1) (rem2))
                             (logand (rem1) (rem3)))
                     (logand (rem2) (rem3)))
             1)
        55 0))


(defund sigabar () (bits (lognot (siga)) 52 0))

(defund sigcmp () (bits (+ (sigb) (sigabar)) 53 0))

(defund sigaltsigb () (bitn (sigcmp) 53))

(defund remcarbits ()
  (if1 (sigaltsigb)
       (bits (remcar) 55 52)
       (bits (remcar) 55 53)))

(defund remsumbits ()
  (if1 (sigaltsigb)
       (bits (remsum) 55 52)
       (bits (remsum) 55 53)))

(defund remcin ()
  (if1 (sigaltsigb)
       (logior1 (bitn (remcar) 51) (bitn (remsum) 51))
       (logior1 (bitn (remcar) 52) (bitn (remsum) 52))))

(defund rembits () (bits (+ (+ (remcarbits) (remsumbits)) (remcin)) 4 0))

(defund q1 ()
  (if1 (logior1 (bitn (rembits) 4)
                (logand1 (bitn (rembits) 3)
                         (logand (bitn (rembits) 2)
                                 (logior1 (bitn (rembits) 1)
                                          (bitn (rembits) 0)))))
       2 1))


(defund rp-1* ()
  (if1 (sigaltsigb)
       (bits (ash (bits (+ (remsum) (remcar)) 58 0) 1) 58 0)
       (bits (+ (remsum) (remcar)) 58 0)))

(defund expq* ()
  (if1 (sigaltsigb)
       (bits (- (si (expdiff) 13) 1) 12 0)
       (expdiff)))

(defund rn-1* ()
  (if1 (log= (q1) 2)
       (setbits (bits 0 58 0) 59 57 1 (div*))
       (setbits (bits 0 58 0) 59 56 0 (div*))))

(in-theory (disable (div1) (div2) (div3) (divsum) (divcar) (div*) (rem1) (rem2) (rem3) (remsum) (remcar) (sigabar)
                    (sigcmp) (sigaltsigb) (remcarbits) (remsumbits) (remcin) (rembits) (q1) (rp-1*) (rn-1*) (expq*)))

(defthmd prescale-lemma
  (and (equal (div) (div*))
       (equal (rp-1) (rp-1*))
       (equal (rn-1) (rn-1*))
       (equal (q-1) (q1))
       (equal (expq) (expq*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(prescale div1 div2 div3 divsum divcar div* rem1 rem2 rem3 remsum remcar sigabar sigcmp
		               sigaltsigb remcarbits remsumbits remcin rembits q1 rp-1* rn-1* expq* div rp-1 rn-1 expq q-1))))

(defthm q1-vals
  (member (q 1) '(1 2))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q1 prescale-lemma q))))

(defund quot (j)
  (if (zp j)
      0
    (+ (quot (1- j))
       (* (expt 4 (- 1 j)) (q j)))))

(defund r (j)
  (* (expt 4 (1- j))
     (- (x) (* (d) (quot j)))))

(in-theory (disable (quot) (r)))

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

(defthmd r0-rewrite
  (implies (not (specialp))
           (equal (r 0) (/ (x) 4)))
  :hints (("Goal" :use ((:functional-instance
                         rem0-div-rewrite
                         (e$ (lambda () 2))
			 (r$ (lambda () 4))
                         (a$ (lambda () 2))
			 (rho$ (lambda () 2/3))
			 (q$ (lambda (j) (if (specialp) 0 (q j))))
			 (quot$ (lambda (j) (if (specialp) 0 (quot j))))
			 (rem$ (lambda (j) (if (specialp) (expt 4 (1- j)) (r j))))
			 (d$ (lambda () (if (specialp) 1 (d))))
			 (x$ (lambda () (if (specialp) 1 (x)))))))
          ("Subgoal 8" :use (q-vals))
          ("Subgoal 7" :use (q-vals))
          ("Subgoal 6" :use (q-vals))
          ("Subgoal 5" :use (x-bounds))
          ("Subgoal 4" :use (x-bounds))
          ("Subgoal 3" :use (d-bounds))
          ("Subgoal 2" :in-theory (enable r quot))
          ("Subgoal 1" :in-theory (enable r quot))))

(defthmd r-recurrence
  (implies (and (not (specialp)) (natp j))
           (equal (r (+ 1 j))
                  (- (* 4 (r j))
                     (* (q (1+ j)) (d)))))
  :hints (("Goal" :use ((:functional-instance
                         rem-div-recurrence
                         (e$ (lambda () 2))
			 (r$ (lambda () 4))
                         (a$ (lambda () 2))
			 (rho$ (lambda () 2/3))
			 (q$ (lambda (j) (if (specialp) 0 (q j))))
			 (quot$ (lambda (j) (if (specialp) 0 (quot j))))
			 (rem$ (lambda (j) (if (specialp) (expt 4 (1- j)) (r j))))
			 (d$ (lambda () (if (specialp) 1 (d))))
			 (x$ (lambda () (if (specialp) 1 (x)))))))
          ("Subgoal 6" :use (q-vals))
          ("Subgoal 5" :use (x-bounds))
          ("Subgoal 4" :use (x-bounds))
          ("Subgoal 3" :use (d-bounds))
          ("Subgoal 2" :in-theory (enable r quot))
          ("Subgoal 1" :in-theory (enable r quot))))

(defthmd r0-bound
  (implies (not (specialp))
           (< (abs (r 0)) (* 2/3 (d))))
  :hints (("Goal" :use ((:functional-instance
                         rem0-div-bound
                         (e$ (lambda () 2))
			 (r$ (lambda () 4))
                         (a$ (lambda () 2))
			 (rho$ (lambda () 2/3))
			 (q$ (lambda (j) (if (specialp) 0 (q j))))
			 (quot$ (lambda (j) (if (specialp) 0 (quot j))))
			 (rem$ (lambda (j) (if (specialp) (expt 4 (1- j)) (r j))))
			 (d$ (lambda () (if (specialp) 1 (d))))
			 (x$ (lambda () (if (specialp) 1 (x)))))))
          ("Subgoal 6" :use (q-vals))
          ("Subgoal 5" :use (x-bounds))
          ("Subgoal 4" :use (x-bounds))
          ("Subgoal 3" :use (d-bounds))
          ("Subgoal 2" :in-theory (enable r quot))
          ("Subgoal 1" :in-theory (enable r quot))))

(defun m (k)
  (case k (2 13/8) (1 4/8) (0 -3/8) (-1 -12/8)))

(defund maxk (a)
  (cond ((<= (m 2) a) 2)
        ((<= (m 1) a) 1)
        ((<= (m 0) a) 0)
        ((<= (m -1) a) -1)
        (t -2)))

(local-defthm maxk-select-digit-d4
  (equal (maxk a)
         (select-digit-d4 a))
  :hints (("Goal" :in-theory (enable maxk select-digit-d4))))

(defthmd r-bound-inv
  (implies (and (not (specialp))
                (natp j)
                (<= (abs (r j)) (* 2/3 (d)))
                (rationalp approx)
                (integerp (* 8 approx))
                (< (abs (- approx (* 4 (r j)))) 1/8)
                (= (q (1+ j)) (maxk approx)))
	   (<= (abs (r (1+ j))) (* 2/3 (d))))
  :hints (("Goal" :use ((:functional-instance
                         srt-div-rad-4
                         (e$ (lambda () 2))
			 (r$ (lambda () 4))
                         (a$ (lambda () 2))
			 (rho$ (lambda () 2/3))
			 (q$ (lambda (j) (if (specialp) 0 (q j))))
			 (quot$ (lambda (j) (if (specialp) 0 (quot j))))
			 (rem$ (lambda (j) (if (specialp) (expt 4 (1- j)) (r j))))
			 (d$ (lambda () (if (specialp) 1 (d))))
			 (x$ (lambda () (if (specialp) 1 (x)))))))
          ("Subgoal 6" :use (q-vals))
          ("Subgoal 5" :use (x-bounds))
          ("Subgoal 4" :use (x-bounds))
          ("Subgoal 3" :use (d-bounds))
          ("Subgoal 2" :in-theory (enable r quot))
          ("Subgoal 1" :in-theory (enable r quot))))

(local-in-theory (disable maxk-select-digit-d4))

(local-defthmd div123
  (implies (not (specialp))
           (equal (+ (div1) (div2) (div3))
	          (* 8 (mul) (sigb))))
  :hints (("Goal" :in-theory (enable ash div1 div2 div3 bvecp mul)
                  :use (sigb-bounds
		        (:instance bitn-plus-bits (x (sigb)) (n 51) (m 49))
		        (:instance bitn-plus-bits (x (sigb)) (n 50) (m 49))
		        (:instance bitn-0-1 (x (sigb)) (n 51))
		        (:instance bitn-0-1 (x (sigb)) (n 50))
                        (:instance bitn-0-1 (x (sigb)) (n 49))
		        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(local-defthmd div123-d
  (implies (not (specialp))
           (equal (+ (div1) (div2) (div3))
	          (* (expt 2 56) (d))))
  :hints (("Goal" :in-theory (enable d sigb-rewrite div123))))

(local-defthmd bvecp-div1
  (implies (not (specialp))
           (bvecp (div1) 55))
  :hints (("Goal" :in-theory (enable div1 ash bvecp)
                  :use (sigb-bounds))))

(local-defthmd bvecp-div2
  (implies (not (specialp))
           (bvecp (div2) 55))
  :hints (("Goal" :in-theory (enable div2 ash bvecp)
                  :use (sigb-bounds))))

(local-defthmd divcar-rewrite-1
  (implies (not (specialp))
           (bvecp (logior (logior (logand (div1) (div2))
                                  (logand (div1) (div3)))
                          (logand (div2) (div3)))
	 55))
  :hints (("Goal" :use (bvecp-div2 bvecp-div1))))

(local-defthmd divcar-rewrite
  (implies (not (specialp))
           (equal (divcar)
                  (* 2
		     (logior (logior (logand (div1) (div2))
                                     (logand (div1) (div3)))
                             (logand (div2) (div3))))))
  :hints (("Goal" :use (divcar divcar-rewrite-1)
                  :in-theory (enable bvecp ash))))

(local-defthm natp-div123
  (implies (not (specialp))
           (and (natp (div1))
	        (natp (div2))
	        (natp (div3))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable div1 div2 div3) :use (sigb-bounds))))

(local-defthmd div-rewrite-1
  (implies (not (specialp))
           (equal (+ (divsum) (divcar))
	          (* (expt 2 56) (d))))
  :hints (("Goal" :in-theory (enable divsum divcar-rewrite div123-d)
                  :use (natp-div123 (:instance add-3 (x (div1)) (y (div2)) (z (div3)))))))

(local-defthm bvecp-sigb-56
  (implies (not (specialp))
           (bvecp (sigb) 56))
  :hints (("Goal" :in-theory (enable bvecp) :use (sigb-bounds))))

(local-defthm bvecp-div123
  (implies (not (specialp))
           (and (bvecp (div1) 56)
	        (bvecp (div2) 56)
	        (bvecp (div3) 56)))
  :hints (("Goal" :in-theory (enable div1 div2 div3))))

(local-defthmd bvecp-divsumcar
  (implies (not (specialp))
           (and (bvecp (divsum) 56)
	        (bvecp (divcar) 56)))
  :hints (("Goal" :in-theory (enable divsum divcar))))

(local-defthmd div-rewrite-2
  (implies (not (specialp))
           (equal (div*)
	          (+ (divsum) (divcar))))
  :hints (("Goal" :in-theory (enable bvecp div*)
                  :use (bvecp-divsumcar))))

(defthmd div-rewrite
  (implies (not (specialp))
           (equal (div)
	          (* (expt 2 56) (d))))
  :hints (("Goal" :in-theory (enable prescale-lemma)
                  :use (div-rewrite-1 div-rewrite-2))))

(defthm siga-bounds
  (implies (not (specialp))
           (and (< (siga) (expt 2 53))
                (>= (siga) (expt 2 52))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable siga-rewrite)
                  :use (a-b-not-zero
                        (:instance sig-lower-bound (x (a)))
                        (:instance sig-upper-bound (x (a))))
                  :nonlinearp t)))

(local-defthmd rem123
  (implies (not (specialp))
           (equal (+ (rem1) (rem2) (rem3))
	          (* 8 (mul) (siga))))
  :hints (("Goal" :in-theory (enable ash rem1 rem2 rem3 bvecp mul)
                  :use (siga-bounds
		        (:instance bitn-plus-bits (x (sigb)) (n 51) (m 49))
		        (:instance bitn-plus-bits (x (sigb)) (n 50) (m 49))
		        (:instance bitn-0-1 (x (sigb)) (n 51))
		        (:instance bitn-0-1 (x (sigb)) (n 50))
                        (:instance bitn-0-1 (x (sigb)) (n 49))
		        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(local-defthmd rem123-x
  (implies (not (specialp))
           (equal (+ (rem1) (rem2) (rem3))
	          (if (>= (sig (a)) (sig (b)))
		      (* (expt 2 56) (x))
		    (* (expt 2 55) (x)))))
  :hints (("Goal" :in-theory (enable x siga-rewrite rem123))))

(local-defthmd bvecp-rem1
  (implies (not (specialp))
           (bvecp (rem1) 55))
  :hints (("Goal" :in-theory (enable rem1 ash bvecp)
                  :use (siga-bounds))))

(local-defthmd bvecp-rem2
  (implies (not (specialp))
           (bvecp (rem2) 55))
  :hints (("Goal" :in-theory (enable rem2 ash bvecp)
                  :use (siga-bounds))))

(local-defthmd remcar-rewrite-1
  (implies (not (specialp))
           (bvecp (logior (logior (logand (rem1) (rem2))
                                  (logand (rem1) (rem3)))
                          (logand (rem2) (rem3)))
	 55))
  :hints (("Goal" :use (bvecp-rem2 bvecp-rem1))))

(local-defthmd remcar-rewrite
  (implies (not (specialp))
           (equal (remcar)
                  (* 2
		     (logior (logior (logand (rem1) (rem2))
                                     (logand (rem1) (rem3)))
                             (logand (rem2) (rem3))))))
  :hints (("Goal" :use (remcar remcar-rewrite-1)
                  :in-theory (enable bvecp ash))))

(local-defthm natp-rem123
  (implies (not (specialp))
           (and (natp (rem1))
	        (natp (rem2))
	        (natp (rem3))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rem1 rem2 rem3) :use (siga-bounds))))

(local-defthmd rem-rewrite-1
  (implies (not (specialp))
           (equal (+ (remsum) (remcar))
	          (if (>= (sig (a)) (sig (b)))
		      (* (expt 2 56) (x))
		    (* (expt 2 55) (x)))))
  :hints (("Goal" :in-theory (enable remsum remcar-rewrite rem123-x)
                  :use (natp-rem123 (:instance add-3 (x (rem1)) (y (rem2)) (z (rem3)))))))

(local-defthm bvecp-siga-56
  (implies (not (specialp))
           (bvecp (siga) 56))
  :hints (("Goal" :in-theory (enable bvecp) :use (siga-bounds))))

(local-defthm bvecp-rem123
  (implies (not (specialp))
           (and (bvecp (rem1) 56)
	        (bvecp (rem2) 56)
	        (bvecp (rem3) 56)))
  :hints (("Goal" :in-theory (enable rem1 rem2 rem3))))

(local-defthmd bvecp-remsumcar
  (implies (not (specialp))
           (and (bvecp (remsum) 56)
	        (bvecp (remcar) 56)))
  :hints (("Goal" :in-theory (enable remsum remcar))))

(local-defthm sigaltsigb-rewrite
  (implies (not (specialp))
           (equal (sigaltsigb)
	          (if (< (siga) (sigb)) 1 0)))
  :hints (("Goal" :in-theory (enable bitn-bits lognot sigabar sigaltsigb bvecp sigcmp)
                  :use (siga-bounds sigb-bounds
		        (:instance bitn-plus-bits (x (+ (1- (expt 2 53)) (- (sigb) (siga)))) (n 53) (m 0))
			(:instance bits-bounds (x (+ (1- (expt 2 53)) (- (sigb) (siga)))) (i 52) (j 0))))))

(defthmd rp-1-rewrite
  (implies (not (specialp))
           (equal (rp-1)
	          (* (expt 2 56) (x))))
  :hints (("Goal" :in-theory (enable siga-rewrite sigb-rewrite ash rp-1* bvecp prescale-lemma)
                  :use (rem-rewrite-1 bvecp-remsumcar))))

(defund a-1 () (/ (rembits) 8))

(in-theory (disable (a-1)))

(defthmd integerp-8*a-1
  (implies (not (specialp))
           (integerp (* 8 (a-1))))
  :hints (("Goal" :in-theory (enable a-1))))

(local-defthmd a-1-1
  (implies (and (not (specialp))
                (< (siga) (sigb)))
	   (< (abs (- (* (expt 2 52) (rembits)) (+ (remsum) (remcar))))
	      (expt 2 52)))
  :hints (("Goal" :in-theory (enable bvecp rembits remsumbits remcarbits remcin)
                  :use (bvecp-remsumcar
		        (:instance bitn-0-1 (x (remsum)) (n 51))
		        (:instance bitn-0-1 (x (remcar)) (n 51))
		        (:instance bits-bounds (x (remsum)) (i 50) (j 0))
		        (:instance bits-bounds (x (remcar)) (i 50) (j 0))
		        (:instance bits-bounds (x (remsum)) (i 55) (j 52))
		        (:instance bits-bounds (x (remcar)) (i 55) (j 52))
		        (:instance bits-plus-bits (x (remsum)) (n 55) (p 52) (m 0))
		        (:instance bits-plus-bits (x (remcar)) (n 55) (p 52) (m 0))
		        (:instance bitn-plus-bits (x (remsum)) (n 51) (m 0))
		        (:instance bitn-plus-bits (x (remcar)) (n 51) (m 0))))))

(local-defthmd a-1-2
  (implies (and (not (specialp))
                (< (siga) (sigb)))
	   (< (abs (- (* (expt 2 52) (rembits)) (* (expt 2 55) (x))))
	      (expt 2 52)))
  :hints (("Goal" :in-theory (enable sigb-rewrite siga-rewrite)
                  :use (a-1-1 rem-rewrite-1))))

(local-defthmd a-1-3
  (implies (and (not (specialp))
                (< (siga) (sigb)))
	   (< (abs (- (a-1) (* 4 (r 0))))
	      1/8))
  :hints (("Goal" :in-theory (enable a-1 r0-rewrite)
                  :use (a-1-2)
		  :nonlinearp t)))

(local-defthmd a-1-4
  (implies (and (not (specialp))
                (>= (siga) (sigb)))
	   (< (abs (- (* (expt 2 53) (rembits)) (+ (remsum) (remcar))))
	      (expt 2 53)))
  :hints (("Goal" :in-theory (enable bvecp rembits remsumbits remcarbits remcin)
                  :use (bvecp-remsumcar
		        (:instance bitn-0-1 (x (remsum)) (n 52))
		        (:instance bitn-0-1 (x (remcar)) (n 52))
		        (:instance bits-bounds (x (remsum)) (i 51) (j 0))
		        (:instance bits-bounds (x (remcar)) (i 51) (j 0))
		        (:instance bits-bounds (x (remsum)) (i 55) (j 53))
		        (:instance bits-bounds (x (remcar)) (i 55) (j 53))
		        (:instance bits-plus-bits (x (remsum)) (n 55) (p 53) (m 0))
		        (:instance bits-plus-bits (x (remcar)) (n 55) (p 53) (m 0))
		        (:instance bitn-plus-bits (x (remsum)) (n 52) (m 0))
		        (:instance bitn-plus-bits (x (remcar)) (n 52) (m 0))))))

(local-defthmd a-1-5
  (implies (and (not (specialp))
                (>= (siga) (sigb)))
	   (< (abs (- (* (expt 2 53) (rembits)) (* (expt 2 56) (x))))
	      (expt 2 53)))
  :hints (("Goal" :in-theory (enable sigb-rewrite siga-rewrite)
                  :use (a-1-4 rem-rewrite-1))))

(local-defthmd a-1-6
  (implies (and (not (specialp))
                (>= (siga) (sigb)))
	   (< (abs (- (a-1) (* 4 (r 0))))
	      1/8))
  :hints (("Goal" :in-theory (enable a-1 r0-rewrite)
                  :use (a-1-5)
		  :nonlinearp t)))

(defthmd a-1-error
  (implies (not (specialp))
	   (< (abs (- (a-1) (* 4 (r 0))))
	      1/8))
  :hints (("Goal" :use (a-1-3 a-1-6))))

(local-defthm bvecp-rembits
  (bvecp (rembits) 5)
  :hints (("Goal" :in-theory (enable rembits))))

(defthm q1-rewrite
  (implies (not (specialp))
           (equal (q1)
	          (if (<= (m 2) (a-1))
		      2 1)))
  :hints (("Goal" :in-theory (enable q1 a-1)
                  :use ((:instance sumbits-thm (x (rembits)) (n 5))
		        (:instance bitn-0-1 (x (rembits)) (n 0))
		        (:instance bitn-0-1 (x (rembits)) (n 1))
		        (:instance bitn-0-1 (x (rembits)) (n 2))
		        (:instance bitn-0-1 (x (rembits)) (n 3))
		        (:instance bitn-0-1 (x (rembits)) (n 4))))))

(local-defthmd a-1-lower
  (implies (not (specialp))
           (> (a-1) (m 1)))
  :hints (("Goal" :in-theory (enable m r0-rewrite)
                  :use (a-1-error d-bounds x-bounds))))

(defthmd q1-maxk-a-1
  (implies (not (specialp))
           (equal (q1) (maxk (a-1))))
  :hints (("Goal" :in-theory (enable maxk q1-rewrite) :use (a-1-lower))))

(local-in-theory (disable q1-rewrite))
(in-theory (disable m (m)))

(defthmd r1-bound
  (implies (not (specialp))
           (<= (abs (r 1)) (* 2/3 (d))))
  :hints (("Goal" :in-theory (enable prescale-lemma q)
                  :use (r0-bound q1-maxk-a-1 a-1-error integerp-8*a-1
                        (:instance r-bound-inv (j 0) (approx (a-1)))))))

(local-defthmd bvecp-div*
  (bvecp (div*) 57)
  :hints (("Goal" :in-theory (enable div*))))

(local-defthmd rn-1-rewrite-1
  (implies (not (specialp))
           (equal (rn-1*) (* (q1) (div*))))
  :hints (("Goal" :use (bvecp-div*) :in-theory (enable q1 cat rn-1* bvecp))))

(defthmd rn-1-rewrite
  (implies (not (specialp))
           (equal (rn-1) (* (expt 2 56) (q 1) (d))))
  :hints (("Goal" :use (rn-1-rewrite-1 div-rewrite) :in-theory (enable prescale-lemma q bvecp))))

(defthmd rp1-rn1
  (implies (not (specialp))
           (equal (- (rp 1) (rn 1))
	          (* (expt 2 56) (r 1))))
  :hints (("Goal" :in-theory (enable rp rn r0-rewrite rp-1-rewrite rn-1-rewrite r)
                  :use ((:instance r-recurrence (j 0))))))

(defthm p-vals
  (member (p) '(53 24 11))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p prec dp sp hp f)
                  :use (fnum-vals))))

(local-defthmd int-rn-1
  (implies (not (specialp))
           (integerp (* (expt 2 (- (p) 53)) (rn-1))))
  :hints (("Goal" :in-theory (enable mul d rn-1-rewrite)
                  :use (exactp-b q1-vals p-vals
                        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(local-defthmd int-rp-1
  (implies (not (specialp))
           (integerp (* (expt 2 (- (p) 53)) (rp-1))))
  :hints (("Goal" :in-theory (enable mul x rp-1-rewrite)
                  :use (exactp-a p-vals
                        (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3))))))

(defthmd bits-rp-1-0
  (implies (not (specialp))
           (equal (bits (rp-1) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bits)
                  :use (p-vals int-rp-1
                        (:instance mod-def (x (rp-1)) (y (expt 2 (- 53 (p)))))))))

(defthmd bits-rn-1-0
  (implies (not (specialp))
           (equal (bits (rn-1) (- 52 (p)) 0) 0))
  :hints (("Goal" :in-theory (enable bits)
                  :use (p-vals int-rn-1
                        (:instance mod-def (x (rn-1)) (y (expt 2 (- 53 (p)))))))))

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
  :hints (("Goal" :in-theory (enable si sigaltsigb-rewrite expq* prescale-lemma)
                  :use (si-expdiff-bounds (:instance si-bits (n 13) (x (1- (si (expdiff) 13))))))))

(defthm integerp-expq
  (implies (not (specialp))
           (integerp (expq)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable expq* prescale-lemma))))


(defthmd quotient-expq
  (implies (not (specialp))
           (equal (abs (/ (a) (b)))
	          (* (expt 2 (- (si (expq) 13) (bias (f))))
		     (/ (x) (d)))))
  :hints (("Goal" :use (fnum-vals quotient-formula (:instance bvecp-member (x (bits (sigb) 51 49)) (n 3)))
                  :in-theory (enable f dp sp hp expw si bias siga-rewrite sigb-rewrite mul expq-expdiff x d))))
