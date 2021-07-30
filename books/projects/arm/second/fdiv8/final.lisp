(in-package "RTL")

(include-book "rounder")


(local-defthmd final-1
  (implies (not (specialp))
           (equal (arm-binary-pre-comp-val 'div (opaz) (opbz) (rz) (f))
                  ()))
  :hints (("Goal" :in-theory (enable specialp binary-undefined-p)
                  :use (a-class b-class))))

(local-defthmd final-2
  (implies (not (specialp))
           (equal (arm-binary-pre-comp-excp 'div (opaz) (opbz) (rz) (f))
                  (rz)))
  :hints (("Goal" :in-theory (enable specialp binary-undefined-p)
                  :use (a-class b-class))))

(local-defthmd final-3
  (implies (not (specialp))
           (equal (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
                  (arm-binary-comp 'div (opaz) (opbz) (rz) (f))))
  :hints (("Goal" :in-theory (enable arm-binary-spec-rewrite)
                  :use (final-1 final-2))))

(in-theory (disable arm-post-comp (arm-post-comp) arm-binary-spec (arm-binary-spec)))

(local-defthmd final-4
  (implies (not (specialp))
           (and (equal (decode (opaz) (f)) (a))
	        (equal (decode (opbz) (f)) (b))))
  :hints (("Goal" :in-theory (enable a b specialp))))

(local-defthmd final-5
  (implies (not (specialp))
           (and (not (equal (a) 0))
	        (not (equal (b) 0)))))

(local-defthmd final-6
  (implies (not (specialp))
           (equal (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
                  (arm-post-comp (/ (a) (b)) (rz) (f))))
  :hints (("Goal" :in-theory (enable binary-eval specialp final-3)
                  :use (final-4 final-5 b-class a-class))))

(local-defund selmaxnorm ()
  (logior1 (logior1 (logand1 (log= (rmode) 2)
                             (lognot1 (sign)))
                    (logand1 (log= (rmode) 1) (sign)))
           (log= (rmode) 3)))

(local-defund ovf-dp () (log>= (si (expq) 13) 2047))

(local-defund ovf-d-dp ()
  (if1 (selmaxnorm)
       (setbits (setbits (setbitn (bits 0 63 0) 64 63 (sign)) 64 62 52 2046) 64 51 0 4503599627370495)
       (setbits (setbits (setbitn (bits 0 63 0) 64 63 (sign)) 64 62 52 2047) 64 51 0 0)))

(local-defund unf-dp () (log<= (si (expq) 13) 0))

(local-defund unf-d-dp ()
  (if1 (fzp)
       (setbitn (bits 0 63 0) 64 63 (sign))
       (let* ((exp (bitn (qrndden) 52))
              (d (setbits (setbitn (bits 0 63 0) 64 63 (sign)) 64 62 52 exp)))
         (setbits d 64 51 0 (bits (qrndden) 51 0)))))

(local-defund norm-d-dp ()
  (setbits (setbits (setbitn (bits 0 63 0) 64 63 (sign)) 64 62 52 (si (expq) 13)) 64 51 0 (bits (qrnd) 51 0)))

(local-defund ovf-sp () (log>= (si (expq) 13) 255))

(local-defund ovf-d-sp ()
  (if1 (selmaxnorm)
       (setbits (setbits (setbitn (bits 0 63 0) 64 31 (sign)) 64 30 23 254) 64 22 0 8388607)
       (setbits (setbits (setbitn (bits 0 63 0) 64 31 (sign)) 64 30 23 255) 64 22 0 0)))

(local-defund unf-sp () (log<= (si (expq) 13) 0))

(local-defund unf-d-sp ()
  (if1 (fzp)
       (setbitn (bits 0 63 0) 64 31 (sign))
       (let* ((exp (bitn (qrndden) 23))
              (d (setbits (setbitn (bits 0 63 0) 64 31 (sign)) 64 30 23 exp)))
         (setbits d 64 22 0 (bits (qrndden) 22 0)))))

(local-defund norm-d-sp ()
  (setbits (setbits (setbitn (bits 0 63 0) 64 31 (sign)) 64 30 23 (si (expq) 13)) 64 22 0 (bits (qrnd) 22 0)))

(local-defund ovf-hp () (log>= (si (expq) 13) 31))

(local-defund ovf-d-hp ()
  (if1 (selmaxnorm)
       (setbits (setbits (setbitn (bits 0 63 0) 64 15 (sign)) 64 14 10 30) 64 9 0 1023)
       (setbits (setbits (setbitn (bits 0 63 0) 64 15 (sign)) 64 14 10 31) 64 9 0 0)))

(local-defund unf-hp () (log<= (si (expq) 13) 0))

(local-defund unf-d-hp ()
  (if1 (fzp)
       (setbitn (bits 0 63 0) 64 15 (sign))
       (let* ((exp (bitn (qrndden) 10))
              (d (setbits (setbitn (bits 0 63 0) 64 15 (sign)) 64 14 10 exp)))
         (setbits d 64 9 0 (bits (qrndden) 9 0)))))

(local-defund norm-d-hp ()
  (setbits (setbits (setbitn (bits 0 63 0) 64 15 (sign)) 64 14 10 (si (expq) 13)) 64 9 0 (bits (qrnd) 9 0)))

(local-defund ovf-flags ()
  (setbitn (setbitn (flags-b) 8 2 1) 8 4 1))

(local-defund unf-flags ()
  (if1 (fzp)
       (setbitn (flags-b) 8 3 1)
       (let ((flags (setbitn (flags-b) 8 4 (logior1 (bitn (flags-b) 4) (inxden)))))
         (setbitn flags 8 3 (logior1 (bitn flags 3) (inxden))))))

(local-defund norm-flags ()
  (setbitn (flags-b) 8 4 (logior1 (bitn (flags-b) 4) (inx))))

(local-defund data* ()
  (case (fnum)
    (2 (if1 (ovf-dp)
            (ovf-d-dp)
	    (if1 (unf-dp)
	         (unf-d-dp)
		 (norm-d-dp))))
    (1 (if1 (ovf-sp)
            (ovf-d-sp)
	    (if1 (unf-sp)
	         (unf-d-sp)
		 (norm-d-sp))))
    (0 (if1 (ovf-hp)
            (ovf-d-hp)
	    (if1 (unf-hp)
	         (unf-d-hp)
		 (norm-d-hp))))
    (t (bits 0 63 0))))

(local-defund flags* ()
  (case (fnum)
    (2 (if1 (ovf-dp)
            (ovf-flags)
	    (if1 (unf-dp)
	         (unf-flags)
		 (norm-flags))))
    (1 (if1 (ovf-sp)
            (ovf-flags)
	    (if1 (unf-sp)
	         (unf-flags)
		 (norm-flags))))
    (0 (if1 (ovf-hp)
            (ovf-flags)
	    (if1 (unf-hp)
	         (unf-flags)
		 (norm-flags))))
    (t (flags-b))))

(local (in-theory (disable (ovf-dp) (ovf-d-dp) (unf-dp) (unf-d-dp) (norm-d-dp) (ovf-sp) (ovf-d-sp) (unf-sp) (unf-d-sp) (norm-d-sp)
                    (selmaxnorm) (ovf-hp) (ovf-d-hp) (unf-hp) (unf-d-hp) (norm-d-hp) (ovf-flags) (unf-flags) (norm-flags)
		    (data*) (flags*))))

(local-defthmd final-lemma
  (and (equal (data-final) (data*))
       (equal (flags-final) (flags*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
                  :in-theory '(ovf-dp ovf-d-dp unf-dp unf-d-dp norm-d-dp ovf-sp ovf-d-sp unf-sp unf-d-sp norm-d-sp ovf-hp
		               ovf-d-hp unf-hp unf-d-hp norm-d-hp ovf-flags unf-flags norm-flags data* flags* data-final
			       selmaxnorm flags-final final))))

(defthmd rnd-modep-mode
  (implies (not (specialp))
           (equal (rnd (/ (a) (b)) (mode) (p))
	          (if (< (/ (a) (b)) 0)
		      (- (rnd (abs (/ (a) (b))) (modep) (p)))
		    (rnd (abs (/ (a) (b))) (modep) (p)))))
  :hints (("Goal" :in-theory (enable rnd modep mode flip-mode rmode common-mode-p)
                  :use (p-vals
		        (:instance rnd-minus (mode (modep)) (x (abs (/ (a) (b)))))
		        (:instance rne-minus (x (/ (a) (b))) (n (p)))
		        (:instance rtz-minus (x (/ (a) (b))) (n (p)))
		        (:instance raz-minus (x (/ (a) (b))) (n (p)))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd final-7
  (implies (and (not (specialp))
                (< (abs (/ (a) (b))) (spn (f))))
	   (< (rnd (abs (/ (a) (b))) (modep) (p))
	      (lpn (f))))
  :hints (("Goal" :in-theory (enable dp sp hp f p prec bias)
                  :use (fnum-vals qrnd-4
		        (:instance expo<= (x (abs (/ (a) (b)))) (n (- (bias (f)))))
			(:instance expo>= (x (rnd (abs (/ (a) (b))) (modep) (p))) (n (- 2 (bias (f)))))
			(:instance expo-rnd (x (abs (/ (a) (b)))) (mode (modep)) (n (p)))))))

(local-defthmd final-8
  (implies (and (not (specialp))
                (>= (abs (/ (a) (b))) (spn (f))))
	   (equal (expo (rnd (abs (/ (a) (b))) (modep) (p)))
	          (- (si (expq) 13) (bias (f)))))
  :hints (("Goal" :in-theory (enable si dp sp hp f p prec bias)
                  :use (fnum-vals rnd-a/b-qrnd
		        (:instance expo-shift (x (+ (expt 2 (1- (p))) (bits (qrnd) (- (p) 2) 0)))
			                      (n (+ (si (expq) 13) (- (bias (f))) (- (1- (p))))))
			(:instance expo-unique (x (+ (expt 2 (1- (p))) (bits (qrnd) (- (p) 2) 0)))
			                       (n (1- (p))))
			(:instance bits-bounds (x (qrnd)) (i (- (p) 2)) (j 0))))))

(local-defthmd final-9
  (implies (and (not (specialp))
                (>= (abs (/ (a) (b))) (spn (f))))
           (iff (> (rnd (abs (/ (a) (b))) (modep) (p))
	           (lpn (f)))
		(>= (rnd (abs (/ (a) (b))) (modep) (p))
		    (expt 2 (- (expt 2 (expw (f))) (1+ (bias (f))))))))
  :hints (("Goal" :in-theory (enable expw si dp sp hp f p prec bias)
                  :use (fnum-vals qrnd-4
		        (:instance rnd-exactp-a (x (abs (/ (a) (b)))) (mode (modep)) (n (p)))
			(:instance fp+2 (x (lpn (f))) (n (p)) (y (rnd (abs (/ (a) (b))) (modep) (p))))))))

(local-defthmd final-10
  (implies (and (not (specialp))
                (>= (abs (/ (a) (b))) (spn (f))))
           (iff (> (rnd (abs (/ (a) (b))) (modep) (p))
	           (lpn (f)))
		(>= (expo (rnd (abs (/ (a) (b))) (modep) (p)))
		    (- (expt 2 (expw (f))) (1+ (bias (f)))))))
  :hints (("Goal" :in-theory (enable expw si dp sp hp f p prec bias)
                  :use (fnum-vals qrnd-4 final-9
		        (:instance expo>= (x (rnd (abs (/ (a) (b))) (modep) (p))) (n (- (expt 2 (expw (f))) (1+ (bias (f))))))
			(:instance expo<= (x (rnd (abs (/ (a) (b))) (modep) (p))) (n (- (expt 2 (expw (f))) (+ 2 (bias (f))))))))))

(local-defthmd final-11
  (implies (not (specialp))
           (iff (> (rnd (abs (/ (a) (b))) (modep) (p))
	           (lpn (f)))
		(>= (si (expq) 13) (1- (expt 2 (expw (f)))))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias)
                  :use (fnum-vals drnd-77 drnd-12 final-7 final-8 final-10))))

(local-defthm final-12
  (equal (bits (rz) 23 22)
         (bits (rin) 23 22))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (rin)) (n 23) (m 22))
                        (:instance bitn-plus-bits (x (rz)) (n 23) (m 22)))
		  :in-theory (enable b-flags bitn-logior))))

(local-defthmd final-13
  (implies (and (not (specialp))
                (> (rnd (abs (/ (a) (b))) (modep) (p))
                   (lpn (f))))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rz) (flags-final)) b))))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     ovf-d-dp ovf-d-sp ovf-d-hp ovf-flags selmaxnorm sign-rewrite cat bitn-logior modep
				     b-flags mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 rnd-modep-mode
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-14
  (implies (and (not (specialp))
                (>= (abs (/ (a) (b))) (spn (f))))
	   (>= (si (expq) 13) 1))
  :hints (("Goal" :in-theory (enable si dp sp hp f p prec bias)
                  :use (fnum-vals qrnd-4 final-8
		        (:instance expo-rnd (x (abs (/ (a) (b)))) (mode (modep)) (n (p)))
			(:instance expo-monotone (x (spn (f))) (y (abs (/ (a) (b)))))))))

(local-defthmd final-15
  (implies (not (specialp))
           (iff (< (abs (/ (a) (b))) (spn (f)))
	        (<= (si (expq) 13) 0)))
  :hints (("Goal" :in-theory (enable si dp sp hp f p prec bias)
                  :use (fnum-vals final-14 drnd-12 drnd-77))))

(local-defthmd final-16
  (implies (not (specialp))
           (equal (fzp) (bitn (rz) 24)))
  :hints (("Goal" :in-theory (enable fzp rz))))

(local-defthmd final-17
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 1))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rz) (flags-final)) b))))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp unf-flags selmaxnorm sign-rewrite cat 
				     bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 rnd-modep-mode
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd drnd-modep-mode
  (implies (not (specialp))
           (equal (drnd (/ (a) (b)) (mode) (f))
	          (if (< (/ (a) (b)) 0)
		      (- (drnd (abs (/ (a) (b))) (modep) (f)))
		    (drnd (abs (/ (a) (b))) (modep) (f)))))
  :hints (("Goal" :in-theory (enable rnd modep mode flip-mode rmode common-mode-p dp sp hp f p prec)
                  :use ((:instance drnd-minus (mode (modep)) (x (abs (/ (a) (b)))) (f (f)))
		        (:instance drnd-minus (mode (mode)) (x (abs (/ (a) (b)))) (f (f)))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd final-18
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0))
	   (let ((r (mv-nth 1 (mv-list 2 (arm-post-comp (/ (a) (b)) (rz) (f))))))
	     (implies (member b (list 2 3 4))
	              (= (bitn r b) (bitn (logior (rz) (flags-final)) b)))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp unf-flags selmaxnorm sign-rewrite cat 
				     bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 drnd-modep-mode rnd-modep-mode drnd-inxden-rewrite
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-19
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(= (drnd (/ (a) (b)) (mode) (f)) 0))
	   (equal (mv-nth 0 (mv-list 2 (arm-post-comp (/ (a) (b)) (rz) (f))))
	          (data-final)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp unf-flags selmaxnorm sign-rewrite cat 
				     bitn-logior modep b-flags mode rmode fpscr-rc zencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 drnd-modep-mode rnd-modep-mode drnd-a/b-qrndden
		        (:instance bitn-plus-bits (x (qrndden)) (n (1- (p))) (m 0))
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-20
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f))))
	   (equal (bits (qrndden) (1- (p)) 0)
	          (expt 2 (1- (p)))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp unf-flags selmaxnorm sign-rewrite cat 
				     bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 drnd-modep-mode rnd-modep-mode drnd-a/b-qrndden
		        (:instance bitn-plus-bits (x (qrndden)) (n (1- (p))) (m 0))
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-21
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f))))
	   (and (equal (bitn (qrndden) (1- (p))) 1)
	        (equal (bits (qrndden) (- (p) 2) 0) 0)))
  :hints (("Goal" :use (final-20 p-vals
                        (:instance bits-bounds (x (qrndden)) (i (- (p) 2)) (j 0))
                        (:instance bitn-plus-bits (x (qrndden)) (n (1- (p))) (m 0))
                        (:instance bitn-0-1 (x (qrndden)) (n (1- (p))))))))

(local-defthmd final-22
  (implies (and (not (specialp))
		(< (abs (/ (a) (b))) (spn (f))))
           (and (>= (drnd (abs (/ (a) (b))) (mode) (f)) 0)
	        (implies (<= (/ (a) (b)) 0)
	                 (<= (drnd (/ (a) (b)) (mode) (f)) 0))
	        (implies (>= (/ (a) (b)) 0)
	                 (>= (drnd (/ (a) (b)) (mode) (f)) 0))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp unf-flags selmaxnorm sign-rewrite cat 
				     bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn drnd)
                  :use (fnum-vals
		        (:instance rnd-non-neg (x (abs (/ (a) (b))))
			                       (mode (modep))
					       (n (+ (p) (expo (abs (/ (a) (b)))) (- (expo (spn (f)))))))
		        (:instance rnd-non-neg (x (/ (a) (b)))
			                       (mode (mode))
					       (n (+ (p) (expo (/ (a) (b))) (- (expo (spn (f)))))))
		        (:instance rnd-non-pos (x (/ (a) (b)))
			                       (mode (mode))
					       (n (+ (p) (expo (/ (a) (b))) (- (expo (spn (f)))))))))))

(local-defthmd final-23
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f))))
	   (equal (mv-nth 0 (mv-list 2 (arm-post-comp (/ (a) (b)) (rz) (f))))
	          (data-final)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp unf-flags selmaxnorm sign-rewrite cat 
				     bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 drnd-modep-mode rnd-modep-mode final-21 final-22
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-24
  (implies (and (not (specialp))
		(< (abs (/ (a) (b))) (spn (f)))
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (<= (expo (drnd (abs (/ (a) (b))) (modep) (f))) (- (bias (f)))))
  :hints (("Goal" :in-theory (enable drepp sgn expw dp sp hp f p prec bias)
                  :use (fnum-vals qrnd-4 drnd-modep-mode rnd-modep-mode drnd-a/b-qrndden
		        (:instance drnd-exactp-a (f (f)) (mode (modep)) (x (abs (/ (a) (b)))))))))

(local-defthmd final-25
  (implies (and (not (specialp))
		(< (abs (/ (a) (b))) (spn (f)))
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
  	   (< (drnd (abs (/ (a) (b))) (modep) (f)) (expt 2 (- 1 (bias (f))))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias)
                  :use (fnum-vals final-24 drnd-modep-mode rnd-modep-mode
		        (:instance expo>= (x (drnd (abs (/ (a) (b))) (modep) (f))) (n (- 1 (bias (f)))))))))

(local-defthmd final-26
  (implies (and (not (specialp))
		(< (abs (/ (a) (b))) (spn (f)))
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (and (not (= (bits (qrndden) (1- (p)) 0) 0))
	        (< (bits (qrndden) (1- (p)) 0)
	           (expt 2 (1- (p))))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias)
                  :nonlinearp t
                  :use (fnum-vals final-25 drnd-modep-mode drnd-a/b-qrndden))))

(local-defthmd final-27
  (implies (and (not (specialp))
		(< (abs (/ (a) (b))) (spn (f)))
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (and (not (= (bits (qrndden) (- (p) 2) 0) 0))
	        (< (bits (qrndden) (- (p) 2) 0) (expt 2 (1- (p))))
	        (= (bitn (qrndden) (1- (p))) 0)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias)
                  :use (fnum-vals final-26
		        (:instance bitn-plus-bits (x (qrndden)) (n (1- (p))) (m 0))
		        (:instance bits-bounds (x (qrndden)) (i (- (p) 2)) (j 0))
			(:instance bitn-0-1 (x (qrndden)) (n (1- (p))))))))

(local-defthmd final-28
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (encodingp (data-final) (f)))
  :hints (("Goal" :in-theory (enable encodingp denormp data* final-lemma expw sigw dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     sigf expf bvecp unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp sign-rewrite cat sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-27
		        (:instance bits-plus-mult-2 (x (bits (qrndden) (- (p) 2) 0))
			                            (y 1) (k (+ (expw (f)) (sigw (f)))) (n (- (p) 2)) (m 0))))))

(local-defthm final-29
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (not (= (sigf (data-final) (f)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable encodingp denormp data* final-lemma expw sigw dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     bitn-logior b-flags sigf expf bvecp unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp sign-rewrite sgn cat)
                  :use (fnum-vals final-11 final-15 final-16 final-27		  
		        (:instance bits-plus-mult-2 (x (bits (qrndden) (- (p) 2) 0))
			                            (y 1) (k (+ (expw (f)) (sigw (f)))) (n (- (p) 2)) (m 0))))))

(local-defthm final-30
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (= (expf (data-final) (f)) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable encodingp denormp data* final-lemma expw sigw dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     bitn-logior b-flags sigf expf bvecp unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp sign-rewrite sgn cat)
                  :use (fnum-vals final-11 final-15 final-16 final-27		  
		        (:instance bits-plus-mult-2 (x (bits (qrndden) (- (p) 2) 0))
			                            (y 1) (k (+ (expw (f)) (sigw (f)))) (n (1- (+ (expw (f)) (sigw (f))))) (m (sigw (f))))))))

(local-defthmd final-31
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (denormp (data-final) (f)))
  :hints (("Goal" :in-theory (enable encodingp denormp data* final-lemma expw sigw dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     sigf expf bvecp unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp sign-rewrite cat sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-27 final-28 final-29 final-30))))


(local-defthm final-32
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (= (sigf (data-final) (f)) (bits (qrndden) (1- (p)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable encodingp denormp data* final-lemma expw sigw dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     bitn-logior b-flags sigf expf bvecp unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp sign-rewrite sgn cat)
                  :use (fnum-vals final-11 final-15 final-16 final-27
		        (:instance bitn-plus-bits (x (qrndden)) (n (1- (p))) (m 0))
		        (:instance bits-plus-mult-2 (x (bits (qrndden) (- (p) 2) 0))
			                            (y 1) (k (+ (expw (f)) (sigw (f)))) (n (- (p) 2)) (m 0))))))

(local-defthm final-33
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (= (sgnf (data-final) (f)) (sign)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable encodingp denormp data* final-lemma expw sigw dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     bitn-logior b-flags sigf expf bvecp unf-dp unf-sp unf-hp unf-d-dp unf-d-sp unf-d-hp sign-rewrite sgnf)
                  :use (fnum-vals final-11 final-15 final-16))))

(local-defthm final-34
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (equal (ddecode (data-final) (f))
	          (drnd (/ (a) (b)) (mode) (f))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias ddecode sign-rewrite)
                  :use (fnum-vals final-33 final-32 drnd-modep-mode drnd-a/b-qrndden))))

(local-defthm final-35
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (equal (data-final)
	          (dencode (drnd (/ (a) (b)) (mode) (f)) (f))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias)
                  :use (fnum-vals final-34 final-31
		        (:instance dencode-ddecode (x (data-final)) (f (f)))))))

(local-defthmd final-36
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (/ (a) (b)) (mode) (f)) 0))
		(not (= (abs (drnd (/ (a) (b)) (mode) (f))) (spn (f)))))
	   (equal (mv-nth 0 (mv-list 2 (arm-post-comp (/ (a) (b)) (rz) (f))))
	          (data-final)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias arm-post-comp
				     bitn-logior b-flags mode rmode fpscr-rc sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-35 rnd-modep-mode
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-37
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (let ((r (mv-nth 1 (mv-list 2 (arm-post-comp (/ (a) (b)) (rz) (f))))))
	     (implies (member b (list 2 3 4))
	              (= (bitn r b) (bitn (logior (rz) (flags-final)) b)))))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias flags* data* final-lemma arm-post-comp ovf-dp ovf-sp ovf-hp
                                     unf-dp unf-sp unf-hp sign-rewrite cat norm-flags
				     bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 rnd-modep-mode rnd-inx-rewrite
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd bvecp-setbits
  (implies (and (natp w) (natp i) (< i w))
           (bvecp (setbits x w i j y) w)))

(local-defthmd final-38
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (bvecp (data-final) 64))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     cat-0 bitn-logior modep mode rmode fpscr-rc nencode sgn bvecp-setbits)
                  :use (fnum-vals final-11 final-15))))

(local-defthmd final-39
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (bits (data-final) 63 (+ 1 (sigw (f)) (expw (f))))
	          0))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     cat-0 bitn-logior modep mode rmode fpscr-rc nencode sgn bvecp-setbits)
                  :use (fnum-vals final-11 final-15))))

(local-defthmd final-40
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (encodingp (data-final) (f)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     encodingp bvecp bitn-logior modep mode rmode fpscr-rc nencode sgn bvecp-setbits)
                  :use (fnum-vals final-38 final-39
		        (:instance bits-bounds (x (data-final)) (i (+ (sigw (f)) (expw (f)))) (j 0))
		        (:instance bits-plus-bits (x (data-final)) (n 63) (p (+ 1 (sigw (f)) (expw (f)))) (m 0))))))

(local-defthmd final-41
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (expf (data-final) (f))
	          (si (expq) 13)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     si expf bvecp bitn-logior modep mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 ))))

(local-defthmd final-42
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (normp (data-final) (f)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     normp si expf bvecp bitn-logior modep mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-40 final-41))))

(local-defthmd final-43
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (sgnf (data-final) (f))
	          (sign)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     sgnf bvecp bitn-logior modep mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 ))))

(local-defthmd final-44
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (manf (data-final) (f))
	          (bits (qrnd) (- (p) 2) 0)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias data* final-lemma ovf-dp ovf-sp ovf-hp
                                     sign-rewrite unf-dp unf-sp unf-hp norm-d-dp norm-d-sp norm-d-hp
				     manf sigf bvecp bitn-logior modep mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 ))))

(local-defthmd final-45
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (ndecode (data-final) (f))
	          (rnd (/ (a) (b)) (mode) (p))))
  :hints (("Goal" :in-theory (enable dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     sign-rewrite ndecode bvecp bitn-logior mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-41 final-43 final-44 rnd-modep-mode rnd-a/b-qrnd))))

(local-defthmd final-46
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (data-final)
	          (nencode (rnd (/ (a) (b)) (mode) (p)) (f))))
  :hints (("Goal" :in-theory (enable dp sp hp f p prec bias ovf-dp ovf-sp ovf-hp
                                     bvecp bitn-logior mode rmode fpscr-rc nencode sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-42 final-45
		        (:instance ndecode-nencode (x (data-final)) (f (f)))))))
		  
(local-defthmd final-47
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (equal (mv-nth 0 (mv-list 2 (arm-post-comp (/ (a) (b)) (rz) (f))))
	          (data-final)))
  :hints (("Goal" :in-theory (enable expw dp sp hp f p prec bias arm-post-comp
				     bitn-logior b-flags mode rmode fpscr-rc sgn)
                  :use (fnum-vals final-11 final-15 final-16 final-46 rnd-modep-mode
		        (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(local-defthmd final-48
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(>= (abs (/ (a) (b))) (spn (f))))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rz) (flags-final)) b))))))
  :hints (("Goal" :use (final-37 final-47))))

(local-defthmd final-49
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f)))
		(= (bitn (rin) (fz)) 0))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rz) (flags-final)) b))))))
  :hints (("Goal" :use (final-18 final-19 final-23 final-36))))

(local-defthmd final-50
  (implies (and (not (specialp))
                (<= (rnd (abs (/ (a) (b))) (modep) (p))
                    (lpn (f)))
		(< (abs (/ (a) (b))) (spn (f))))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rz) (flags-final)) b))))))
  :hints (("Goal" :use (final-49 final-17))))

(local-defthmd final-51
  (implies (not (specialp))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rz) (flags-final)) b))))))
  :hints (("Goal" :use (final-13 final-48 final-50))))

(local-defthmd final-52
  (implies (not (specialp))
	   (mv-let (d r) (arm-post-comp (/ (a) (b)) (rz) (f))
	     (and (= d (data-final))
	          (implies (member b (list 2 3 4))
		           (= (bitn r b) (bitn (logior (rin) (flags-final)) b))))))
  :hints (("Goal" :use (final-51)
                  :in-theory (enable rz-flags-b bitn-logior b-flags))))

(local-defthmd final-53
  (implies (and (not (specialp))
                (natp b)
		(not (member b (list 2 3 4))))
	   (equal (bitn (flags-final) b)
	          (bitn (flags-b) b)))
  :hints (("Goal" :use ((:instance bvecp-member (x b) (n 3)))
                  :in-theory (enable b-flags bvecp bitn-cat bitn-bits flags* final-lemma ovf-flags unf-flags norm-flags))))

(local-defthmd final-54
  (implies (and (not (specialp))
                (natp b)
		(not (member b (list 2 3 4))))
	   (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'div (opaw) (opbw) (rin) (f)))) b)
	          (bitn (logior (rin) (flags-b)) b)))
  :hints (("Goal" :in-theory (enable rz-flags-b final-6 arm-post-comp))))

(local-defthmd final-55
  (implies (not (specialp))
	   (bvecp (flags-final) 8))
  :hints (("Goal" :in-theory (enable b-flags bitn-cat bitn-bits flags* final-lemma ovf-flags unf-flags norm-flags))))

(local-defthmd final-56
  (implies (and (not (specialp))
                (natp b)
		(not (member b (list 2 3 4))))
	   (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'div (opaw) (opbw) (rin) (f)))) b)
	          (bitn (logior (rin) (flags-final)) b)))
  :hints (("Goal" :use (final-53 final-54 final-55) :in-theory (enable b-flags bitn-logior))))

(local-defthmd final-57
  (implies (not (specialp))
	   (mv-let (d r) (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
	     (and (= d (data-final))
	          (implies (natp b)
		           (= (bitn r b) (bitn (logior (rin) (flags-final)) b))))))
  :hints (("Goal" :use (final-6 final-52 final-56))))

(local-defthmd final-58
  (implies (not (specialp))
	   (integerp (mv-nth 1 (mv-list 2 (arm-binary-spec 'div (opaw) (opbw) (rin) (f))))))
  :hints (("Goal" :in-theory (enable final-6 arm-post-comp))))

(local-defthmd final-59
  (implies (not (specialp))
	   (mv-let (d r) (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
	     (and (= d (data-final))
	          (= r (logior (rin) (flags-final))))))
  :hints (("Goal" :use (final-55 final-58
                        (:instance final-57
                                   (b (bit-diff (mv-nth 1 (mv-list 2 (arm-binary-spec 'div (opaw) (opbw) (rin) (f))))
				                (logior (rin) (flags-final)))))
			(:instance bit-diff-diff (x (mv-nth 1 (mv-list 2 (arm-binary-spec 'div (opaw) (opbw) (rin) (f)))))
			                         (y (logior (rin) (flags-final))))))))

(local-defthmd final-60
  (implies (not (specialp))
           (and (equal (data) (data-final))
	        (equal (flags) (flags-final))))
  :hints (("Goal" :in-theory (enable specialp flags data))))

(local-defthmd final-61
  (implies (not (specialp))
	   (mv-let (d r) (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
	     (and (= d (data))
	          (= r (logior (rin) (flags))))))
  :hints (("Goal" :use (final-59 final-60))))

(local-defthm not-specialp-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
      (implies (not (specialp))
               (and (equal (data) data-spec)
                    (equal (logior (rin) (flags)) r-spec)))))
  :hints (("Goal" :use (final-61)
                  :in-theory (enable opaw opbw fmtw))))

(defthm fdiv8-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec)
            (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (not-specialp-main specialp-main))))


(defthmd lemma-to-be-functionally-instantiated
  (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
         (fmtw (+ 1 (expw f) (sigw f)))
         (dnp (bitn (rin) 25))
         (fzp (bitn (rin) 24))
         (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fdiv8 (opa) (opb) (fnum) fzp dnp rmode)
      (mv-let (data-spec r-spec)
              (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) f)
        (and (equal data data-spec)
             (equal (logior (rin) flags) r-spec)))))
  :hints (("Goal" :use (fdiv8-main fdiv8-lemma)
                  :in-theory (enable f fzp dnp rmode))))

(defmacro ic ()
  '(input-constraints opa opb fnum rin))

(defthm fdiv8-correct
  (implies (input-constraints opa opb fnum rin)
           (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (dnp (bitn rin 25))
                  (fzp (bitn rin 24))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fdiv8 opa opb fnum fzp dnp rmode)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-binary-spec 'div (bits opa (1- fmtw) 0) (bits opb (1- fmtw) 0) rin f)
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (opb (lambda () (if (ic) opb (opb))))
                         (fnum (lambda () (if (ic) fnum (fnum))))
                         (rin (lambda () (if (ic) rin (rin))))))
		  :in-theory (disable arm-binary-spec))		  
          ("Subgoal 1" :use (input-constraints-lemma))))
