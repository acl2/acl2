(in-package "RTL")

(include-book "rounder")


(local-defthmd spec-1
  (implies (not (specialp))
           (equal (arm-sqrt-pre-comp-val (opaz) (rz) (f))
                  ()))
  :hints (("Goal" :in-theory (enable snanp qnanp specialp)
                  :use (a-fields a-class))))

(local-defthmd spec-2
  (implies (not (specialp))
           (equal (arm-sqrt-pre-comp-excp (opaz) (rz) (f))
                  (rz)))
  :hints (("Goal" :in-theory (enable snanp qnanp specialp)
                  :use (a-fields a-class))))

(local-defthmd spec-3
  (implies (not (specialp))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (arm-sqrt-comp (opaz) (rz) (f))))
  :hints (("Goal" :in-theory (enable arm-sqrt-spec-rewrite)
                  :use (spec-1 spec-2))))

(in-theory (disable arm-post-comp (arm-post-comp) arm-sqrt-spec (arm-sqrt-spec)))

(local-defthmd spec-4
  (implies (not (specialp))
           (equal (decode (opaz) (f)) (a)))
  :hints (("Goal" :in-theory (enable a specialp))))

(local-defthmd spec-5
  (implies (not (specialp))
           (not (equal (a) 0))))
		
(local-defthmd spec-6
  (implies (not (specialp))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (arm-post-comp (qsqrt (a) (+ (p) 2)) (rz) (f))))
  :hints (("Goal" :in-theory (enable p specialp spec-3)
           :use (spec-4 spec-5 a-class))))

(local-defthm spec-7
  (implies (not (specialp))
           (equal (prec (f)) (p)))
  :hints (("Goal" :in-theory (enable p prec f sp dp hp)
           :use (fnum-vals))))

(local-defthm spec-8
  (implies (not (specialp))
           (equal (fpscr-rc (rz)) (mode)))
  :hints (("Goal" :in-theory (enable fpscr-rc mode rmode bitn-logior a-flags)
                  :use ((:instance bitn-plus-bits (x (rin)) (n 23) (m 22))
		        (:instance bitn-plus-bits (x (rz)) (n 23) (m 22))))))

(local-defthm spec-9
  (implies (not (specialp))
           (common-mode-p (mode)))
  :hints (("Goal" :in-theory (enable mode rmode)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd spec-10
  (implies (not (specialp))
           (equal (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	          (rnd (qsqrt (a) (+ (p) 2)) (mode) (p))))
  :hints (("Goal" :in-theory (enable n f dp sp hp p prec)
                  :use (n fnum-vals
		        (:instance rnd-qsqrt-equal (x (a)) (m (1+ (* 2 (n)))) (n (+ (p) 2)) (k (p)) (mode (mode)))))))

(local-defthmd spec-11
  (implies (not (specialp))
           (equal (expo (qsqrt (x) (+ (p) 2)))
	          -1))
  :hints (("Goal" :in-theory (enable qsqrt-rto-sqrt)
                  :use (p-vals x-bounds))))

(local-defthmd spec-12
  (implies (not (specialp))
           (equal (qsqrt (a) (+ (p) 2))
                  (* (expt 2 (1+ (- (expq) (bias (f)))))
                     (qsqrt (x) (+ (p) 2)))))
  :hints (("Goal" :in-theory (enable n a-x dp sp hp p prec bias f)
                  :use (fnum-vals x-bounds
                        (:instance qsqrt-shift (x (x)) (n (+ (p) 2)) (k (1+ (- (expq) (bias (f))))))))))

(local-defthmd spec-13
  (implies (not (specialp))
           (equal (expo (qsqrt (a) (+ (p) 2)))
	          (- (expq) (bias (f)))))
  :hints (("Goal" :in-theory (enable n a-x dp sp hp p prec bias f)
                  :use (fnum-vals spec-11 spec-12
                        (:instance expo-shift (x (qsqrt (x) (+ (p) 2))) (n (1+ (- (expq) (bias (f))))))))))

(local-defthmd spec-14
  (implies (not (specialp))
           (>= (qsqrt (a) (+ (p) 2))
	       (spn (f))))
  :hints (("Goal" :in-theory (enable expw spn n a-x dp sp hp p prec bias f)
                  :nonlinearp t
                  :use (fnum-vals spec-13 expq-bounds x-bounds
		        (:instance qsqrt-pos (x (a)) (n (+ (p) 2)))
                        (:instance expo-lower-bound (x (qsqrt (a) (+ (p) 2))))))))

(local-defthmd spec-15
  (implies (not (specialp))
           (<= (abs (rnd (qsqrt (a) (+ (p) 2)) (mode) (p)))
	       (lpn (f))))
  :hints (("Goal" :in-theory (enable expw lpn n dp sp hp p prec bias f exprnd-rewrite)
                  :nonlinearp t
                  :use (fnum-vals spec-10 expq-bounds rnd-qsqrt-a
                        (:instance bits-bounds (x (qrnd)) (i (- (p) 2)) (j 0))))))

(local-defthmd spec-16
  (implies (not (specialp))
           (iff (= (rnd (qsqrt (a) (+ (p) 2)) (mode) (p))
	           (qsqrt (a) (+ (p) 2)))
		(= (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	           (qsqrt (a) (1+ (* 2 (n)))))))
  :hints (("Goal" :in-theory (enable n dp sp hp p prec f)
                  :use (fnum-vals
                        (:instance qsqrt-exact-equal (x (a)) (k (p)) (m (1+ (* 2 (n)))) (n (+ (p) 2)))
                        (:instance qsqrt-exact-equal (x (a)) (k (p)) (n (1+ (* 2 (n)))) (m (+ (p) 2)))
			(:instance rnd-exactp-b (x (qsqrt (a) (1+ (* 2 (n))))) (mode (mode)) (n (p)))
			(:instance rnd-exactp-b (x (qsqrt (a) (+ (p) 2))) (mode (mode)) (n (p)))))))

(local-defthmd spec-17
  (implies (not (specialp))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (mv (nencode (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p)) (f))
                      (if (= (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	                     (qsqrt (a) (1+ (* 2 (n)))))
		          (rz)
			(set-flag 4 (rz))))))
  :hints (("Goal" :in-theory (enable spec-6 arm-post-comp)
                  :use (spec-16 spec-14 spec-15 spec-10))))

(local-defthmd spec-18
  (implies (not (specialp))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (mv (nencode (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p)) (f))
                      (if (= (inx) 0)
		          (rz)
			(set-flag 4 (rz))))))
  :hints (("Goal" :in-theory (enable rnd-inx-rewrite)
                  :use (spec-17))))

(local-defthmd sqrtpow2-1
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (not (equal (expa) 0)))
  :hints (("Goal" :in-theory (enable expa normp)
                  :use (a-class a-fields))))

(local-defthmd sqrtpow2-2
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (siga) (expt 2 52)))
  :hints (("Goal" :in-theory (enable si normalize siga)
                  :use (sqrtpow2-1 fnum-vals))))

(local-defthmd sqrtpow2-3
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (sig (a)) 1))
  :hints (("Goal" :use (sqrtpow2-2) :in-theory (enable siga-rewrite))))

(local-defthmd sqrtpow2-4
  (implies (not (specialp))
	   (equal (expodd)
	          (if (oddp (expshft)) 1 0)))
  :hints (("Goal" :in-theory (enable bitn-rec-0 normalize expodd si))))

(local-defthmd sqrtpow2-5
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (a)
	          (if (= (expodd) 1)
		      (expt 2 (* 2 (- (expq) (bias (f)))))
		    (* 2 (expt 2 (* 2 (- (expq) (bias (f)))))))))
  :hints (("Goal" :use (a-x) :in-theory (enable si f sp dp hp bias x sqrtpow2-3 sqrtpow2-4))))

(local-defthmd sqrtpow2-6
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (qsqrt (a) (1+ (* 2 (n))))
	          (if (= (expodd) 1)
		      (expt 2 (- (expq) (bias (f))))
		    (* (expt 2 (- (expq) (bias (f))))
		       (qsqrt 2 (1+ (* 2 (n))))))))
  :hints (("Goal" :use (sqrtpow2-5 fnum-vals
                        (:instance qsqrt-shift (x 1) (k (- (expq) (bias (f)))) (n (1+ (* 2 (n)))))
                        (:instance qsqrt-shift (x 2) (k (- (expq) (bias (f)))) (n (1+ (* 2 (n))))))
                  :in-theory (enable n f sp dp hp bias x))))

(local-defthmd sqrtpow2-7
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	          (if (= (expodd) 1)
		      (expt 2 (- (expq) (bias (f))))
		    (* (expt 2 (- (expq) (bias (f))))
		       (rnd (qsqrt 2 (1+ (* 2 (n)))) (mode) (p))))))
  :hints (("Goal" :use (sqrtpow2-6 fnum-vals
                        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
			(:instance rnd-shift (x 1) (mode (mode)) (n (p)) (k (- (expq) (bias (f)))))
                        (:instance rnd-shift (x (qsqrt 2 (1+ (* 2 (n))))) (mode (mode)) (n (p)) (k (- (expq) (bias (f))))))
                  :in-theory (enable mode rmode n f sp dp hp bias x p prec))))

(local-defthmd sqrtpow2-8
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (ndecode (d-sqrtpow2) (f))
	          (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))))	          
  :hints (("Goal" :use (sqrtpow2-7 fnum-vals expq-bounds (:instance bvecp-member (x (bits (rin) 23 22)) (n 2)))
                  :in-theory (enable mode rmode bvecp sgnf manf expf ndecode d-sqrtpow2 sqrtpow2 sqrtpow2-4 n
		                     f sp dp hp bias x p prec))))

(local-defthmd sqrtpow2-9
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (expf (d-sqrtpow2) (f))
	          (expq)))
  :hints (("Goal" :use (fnum-vals expq-bounds)
                  :in-theory (enable mode rmode bvecp sgnf manf expf ndecode d-sqrtpow2 sqrtpow2 n
		                     normp expw encodingp f sp dp hp bias x p prec))))

(local-defthmd sqrtpow2-10
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (encodingp (d-sqrtpow2) (f)))
  :hints (("Goal" :use (fnum-vals expq-bounds (:instance bvecp-member (x (bits (rin) 23 22)) (n 2)))
                  :in-theory (enable mode rmode bvecp sgnf manf expf ndecode d-sqrtpow2 sqrtpow2 n
		                     cat encodingp f sp dp hp bias x p prec))))

(local-defthmd sqrtpow2-11
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (normp (d-sqrtpow2) (f)))
  :hints (("Goal" :use (fnum-vals sqrtpow2-9 sqrtpow2-10 expq-bounds)
                  :in-theory (enable normp expw f sp dp hp bias x p prec))))

(local-defthmd sqrtpow2-12
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (d-sqrtpow2)
	          (nencode (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p)) (f))))
  :hints (("Goal" :use (fnum-vals sqrtpow2-11 sqrtpow2-8
                        (:instance nencode-ndecode (x (d-sqrtpow2)) (f (f))))
                  :in-theory (enable f sp dp hp p prec))))

(local-defthmd sqrtpow2-13
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (iff (= (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	           (qsqrt (a) (1+ (* 2 (n)))))
		(= (expodd) 1)))
  :hints (("Goal" :use (fnum-vals sqrtpow2-6 sqrtpow2-7
                        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2)))
                  :in-theory (enable mode rmode n bias f sp dp hp p prec))))

(local-defthmd sqrtpow2-14
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (flags-sqrtpow2)
	          (if (= (expodd) 1) 0 16)))
  :hints (("Goal" :use (fnum-vals)
                  :in-theory (enable flags-sqrtpow2 sqrtpow2 expodd))))

(local-defthmd sqrtpow2-15
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
	   (equal (rz) (rin)))
  :hints (("Goal" :use (a-class)
                  :in-theory (enable rz))))

(local-defthmd sqrtpow2-16
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (mv (d-sqrtpow2)
                      (logior (rin) (flags-sqrtpow2)))))
  :hints (("Goal" :in-theory (enable set-flag sqrtpow2-12 sqrtpow2-14 sqrtpow2-15 spec-17)
                  :use (sqrtpow2-13))))

(local-defthmd sqrtpow2-lemma
  (implies (and (not (specialp))
                (= (classa) 4)
	        (= (mana) 0))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (mv (data) (logior (rin) (flags)))))
  :hints (("Goal" :use (signa-0-1) :in-theory (enable sqrtpow2-16 data flags specialp))))

(local-defund selmaxnorm ()
  (logior1 (logior1 (logand1 (log= (rmode) 2)
                             (lognot1 0))
                    (logand1 (log= (rmode) 1) 0))
           (log= (rmode) 3)))

(local-defund ovf-dp () (log>= (si (exprnd) 13) 2047))

(local-defund ovf-d-dp ()
  (if1 (selmaxnorm)
       (setbits (setbits (setbitn (bits 0 63 0) 64 63 0) 64 62 52 2046) 64 51 0 4503599627370495)
       (setbits (setbits (setbitn (bits 0 63 0) 64 63 0) 64 62 52 2047) 64 51 0 0)))

(local-defund unf-dp () (log<= (si (exprnd) 13) 0))

(local-defund unf-d-dp ()
  (if1 (fzp)
       (setbitn (bits 0 63 0) 64 63 0)
       (let* ((exp (bitn (qrndden) 52))
              (d (setbits (setbitn (bits 0 63 0) 64 63 0) 64 62 52 exp)))
         (setbits d 64 51 0 (bits (qrndden) 51 0)))))

(local-defund norm-d-dp ()
  (setbits (setbits (setbitn (bits 0 63 0) 64 63 0) 64 62 52 (si (exprnd) 13)) 64 51 0 (bits (qrnd) 51 0)))

(local-defund ovf-sp () (log>= (si (exprnd) 13) 255))

(local-defund ovf-d-sp ()
  (if1 (selmaxnorm)
       (setbits (setbits (setbitn (bits 0 63 0) 64 31 0) 64 30 23 254) 64 22 0 8388607)
       (setbits (setbits (setbitn (bits 0 63 0) 64 31 0) 64 30 23 255) 64 22 0 0)))

(local-defund unf-sp () (log<= (si (exprnd) 13) 0))

(local-defund unf-d-sp ()
  (if1 (fzp)
       (setbitn (bits 0 63 0) 64 31 0)
       (let* ((exp (bitn (qrndden) 23))
              (d (setbits (setbitn (bits 0 63 0) 64 31 0) 64 30 23 exp)))
         (setbits d 64 22 0 (bits (qrndden) 22 0)))))

(local-defund norm-d-sp ()
  (setbits (setbits (setbitn (bits 0 63 0) 64 31 0) 64 30 23 (si (exprnd) 13)) 64 22 0 (bits (qrnd) 22 0)))

(local-defund ovf-hp () (log>= (si (exprnd) 13) 31))

(local-defund ovf-d-hp ()
  (if1 (selmaxnorm)
       (setbits (setbits (setbitn (bits 0 63 0) 64 15 0) 64 14 10 30) 64 9 0 1023)
       (setbits (setbits (setbitn (bits 0 63 0) 64 15 0) 64 14 10 31) 64 9 0 0)))

(local-defund unf-hp () (log<= (si (exprnd) 13) 0))

(local-defund unf-d-hp ()
  (if1 (fzp)
       (setbitn (bits 0 63 0) 64 15 0)
       (let* ((exp (bitn (qrndden) 10))
              (d (setbits (setbitn (bits 0 63 0) 64 15 0) 64 14 10 exp)))
         (setbits d 64 9 0 (bits (qrndden) 9 0)))))

(local-defund norm-d-hp ()
  (setbits (setbits (setbitn (bits 0 63 0) 64 15 0) 64 14 10 (si (exprnd) 13)) 64 9 0 (bits (qrnd) 9 0)))

(local-defund ovf-flags ()
  (setbitn (setbitn (flags-a) 8 2 1) 8 4 1))

(local-defund unf-flags ()
  (if1 (fzp)
       (setbitn (flags-a) 8 3 1)
       (let ((flags (setbitn (flags-a) 8 4 (logior1 (bitn (flags-a) 4) (inxden)))))
         (setbitn flags 8 3 (logior1 (bitn flags 3) (inxden))))))

(local-defund norm-flags ()
  (setbitn (flags-a) 8 4 (logior1 (bitn (flags-a) 4) (inx))))

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
    (t (flags-a))))

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

(local-defthm no-ovf-unf
  (implies (not (specialp))
           (and (equal (data-final)
	               (case (fnum)
		         (2 (norm-d-dp))
			 (1 (norm-d-sp))
			 (0 (norm-d-hp))))
	        (equal (flags-final)
		       (norm-flags))))
  :hints (("Goal" :in-theory (enable exprnd-rewrite final-lemma expw f dp sp hp ovf-dp unf-dp ovf-sp unf-sp
                                     bvecp si ovf-hp unf-hp flags* data*)
                  :use (fnum-vals expq-bounds))))

(local-defthmd exprnd-bounds
  (implies (not (specialp))
           (and (> (exprnd) 0)
	        (< (exprnd) (1- (expt 2 (expw (f)))))))
  :hints (("Goal" :in-theory (enable f dp sp hp p prec expw exprnd-rewrite)
		  :use (fnum-vals expq-bounds))))

(local-defthmd final-1
  (implies (not (specialp))
           (equal (sgnf (data-final) (f)) 0))
  :hints (("Goal" :in-theory (enable f dp sp hp p prec bias no-ovf-unf norm-d-dp norm-d-sp norm-d-hp
                              ndecode manf sgnf expf expw sigw bvecp si)
		  :use (fnum-vals exprnd-bounds))))

(local-defthmd final-2
  (implies (not (specialp))
           (equal (expf (data-final) (f))
	          (exprnd)))
  :hints (("Goal" :in-theory (enable f dp sp hp p prec bias no-ovf-unf norm-d-dp norm-d-sp norm-d-hp
                              ndecode manf sgnf expf expw sigw bvecp si)
		  :use (fnum-vals exprnd-bounds))))

(local-defthmd final-3
  (implies (not (specialp))
           (equal (manf (data-final) (f))
	          (bits (qrnd) (- (p) 2) 0)))
  :hints (("Goal" :in-theory (enable f dp sp hp p prec bias no-ovf-unf norm-d-dp norm-d-sp norm-d-hp
                              ndecode manf sgnf expf expw sigw bvecp si)
		  :use (fnum-vals exprnd-bounds))))

(local (in-theory (disable no-ovf-unf)))

(local-defthmd final-4
  (implies (not (specialp))
           (equal (ndecode (data-final) (f))
	          (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))))
  :hints (("Goal" :in-theory (enable f dp sp hp p prec bias ndecode expw sigw)
		  :use (rnd-qsqrt-a final-1 final-2 final-3  fnum-vals))))

(local-defthm final-5
  (implies (and (natp n) (natp m) (natp x) (natp y))
           (<= (cat x n y m) (+ (* (expt 2 m) x) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-mod cat))))

(local-defthmd final-6
  (implies (not (specialp))
           (encodingp (data-final) (f)))
  :hints (("Goal" :in-theory (enable encodingp norm-d-dp norm-d-sp norm-d-hp no-ovf-unf f dp sp hp p
                                     cat-0 bvecp prec bias ndecode expw sigw)
		  :use (fnum-vals
		        (:instance final-5 (x (bits (si (exprnd) 13) (1- (expw (f))) 0))
			                   (y (bits (qrnd) (- (p) 2) 0))
					   (m (sigw (f)))
					   (n 54))
		        (:instance final-5 (x (bits (si (exprnd) 13) (1- (expw (f))) 0))
			                   (y (bits (qrnd) (- (p) 2) 0))
					   (m (sigw (f)))
					   (n 41))
		        (:instance bits-bounds (x (si (exprnd) 13)) (i (1- (expw (f)))) (j 0))
		        (:instance bits-bounds (x (qrnd)) (i (- (p) 2)) (j 0))))))

(local-defthmd final-7
  (implies (not (specialp))
           (normp (data-final) (f)))
  :hints (("Goal" :in-theory (enable normp f dp sp hp expw p prec)
		  :use (fnum-vals exprnd-bounds final-2 final-6))))

(local-defthmd final-8
  (implies (not (specialp))
           (equal (data-final)
	          (nencode (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p)) (f))))
  :hints (("Goal" :in-theory (enable normp f dp sp hp expw p prec)
		  :use (fnum-vals final-4 final-7
		        (:instance nencode-ndecode (x (data-final)) (f (f)))))))

(local-defthmd final-9
  (implies (not (specialp))
           (equal (data-final)
	          (nencode (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p)) (f))))
  :hints (("Goal" :in-theory (enable normp f dp sp hp expw p prec)
		  :use (fnum-vals final-4 final-7
		        (:instance nencode-ndecode (x (data-final)) (f (f)))))))

(local-defthmd final-9-a
  (implies (not (specialp))
           (equal (data-final)
	          (mv-nth 0 (mv-list 2 (arm-sqrt-spec (opaw) (rin) (f)))))) 
  :hints (("Goal" :in-theory (enable final-9 spec-18))))

(local-defthmd final-10
  (implies (and (not (specialp))
                (natp b)
		(< b 8))
	   (equal (bitn (flags-final) b)
	          (if (= b 4)
		      (logior (bitn (flags-a) 4) (inx))
		    (bitn (flags-a) b))))
  :hints (("Goal" :in-theory (enable bitn-cat bitn-bits rnd-inx-rewrite no-ovf-unf norm-flags))))

(local-defthmd bvecp-flags-final
  (implies (not (specialp))
           (bvecp (flags-final) 8))
  :hints (("Goal" :in-theory (enable no-ovf-unf norm-flags a-flags))))

(local-defthmd final-11
  (implies (and (not (specialp))
                (natp b)
		(< b 8))
	   (equal (bitn (logior (flags-final) (rin)) b)
	          (if (= b 4)
		      (logior (bitn (rz) 4) (inx))
		    (bitn (rz) b))))
  :hints (("Goal" :use (bvecp-flags-final)
                  :in-theory (enable a-flags bitn-cat bitn-bits final-10 rz-flags-a bitn-logior))))

(local-defthmd final-12
  (implies (and (not (specialp))
                (natp b))
	   (equal (bitn (logior (flags-final) (rin)) b)
	          (if (= b 4)
		      (logior (bitn (rz) 4) (inx))
		    (bitn (rz) b))))
  :hints (("Goal" :use (bvecp-flags-final (:instance bvecp-bitn-0 (x (flags-final)) (n b)))
                  :cases ((< b 8))
                  :in-theory (enable bvecp a-flags bitn-cat bitn-bits final-10 rz-flags-a bitn-logior))))

(local-defthmd inx-0-1
  (implies (not (specialp))
           (member (inx) '(0 1)))
  :hints (("Goal" :in-theory (enable rnd-inx-rewrite))))

(local-defthmd final-13
  (implies (and (not (specialp))
                (natp b))
	   (equal (bitn (logior (flags-final) (rin)) b)
	          (bitn (mv-nth 1 (mv-list 2 (arm-sqrt-spec (opaw) (rin) (f)))) b)))
  :hints (("Goal" :use (inx-0-1 bvecp-flags-final)
                  :in-theory (enable bitn-logior a-flags final-12 spec-18))))

(local-defthmd final-14
  (and (integerp (logior (flags-final) (rin)))
       (integerp (mv-nth 1 (mv-list 2 (arm-sqrt-spec (opaw) (rin) (f))))))
  :hints (("Goal" :in-theory (enable arm-post-comp arm-sqrt-spec))))

(local-defthmd final-15
  (implies (not (specialp))
           (equal (logior (rin) (flags-final))
	          (mv-nth 1 (mv-list 2 (arm-sqrt-spec (opaw) (rin) (f))))))
  :hints (("Goal" :use (final-14
                        (:instance final-13 (b (bit-diff (logior (flags-final) (rin))
			                                 (mv-nth 1 (mv-list 2 (arm-sqrt-spec (opaw) (rin) (f)))))))
			(:instance bit-diff-diff (x (logior (flags-final) (rin)))
			                         (y (mv-nth 1 (mv-list 2 (arm-sqrt-spec (opaw) (rin) (f))))))))))

(local-defthmd final-16
  (implies (not (specialp))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
	          (mv (data-final) (logior (rin) (flags-final)))))
  :hints (("Goal" :use (spec-18 final-15 final-9-a))))

(local-defthmd final-17
  (implies (not (specialp))
           (equal (arm-sqrt-spec (opaw) (rin) (f))
                  (mv (data) (logior (rin) (flags)))))
  :hints (("Goal" :use (signa-0-1 final-16 sqrtpow2-lemma) :in-theory (enable specialp data flags))))

(local-defthmd final-18
  (implies (not (specialp))
	   (mv-let (d r) (arm-sqrt-spec (opaw) (rin) (f))
	     (and (= d (data))
	          (= r (logior (rin) (flags))))))
  :hints (("Goal" :use (final-17))))

(local-defthm not-specialp-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) (f))
      (implies (not (specialp))
               (and (equal (data) data-spec)
                    (equal (logior (rin) (flags)) r-spec)))))
  :hints (("Goal" :use (final-18)
                  :in-theory (enable opaw fmtw))))

(defthm fsqrt4-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (not-specialp-main specialp-main))))

(defthmd lemma-to-be-functionally-instantiated
  (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
         (fmtw (+ 1 (expw f) (sigw f)))
         (dnp (bitn (rin) 25))
         (fzp (bitn (rin) 24))
         (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fsqrt4 (opa) (fnum) fzp dnp rmode)
      (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) f)
        (and (equal data data-spec)
             (equal (logior (rin) flags) r-spec)))))
  :hints (("Goal" :use (fsqrt4-main fsqrt4-lemma)
                  :in-theory (enable f fzp dnp rmode))))

(defmacro ic ()
  '(input-constraints opa fnum rin))

(defthm fsqrt4-correct
  (implies (input-constraints opa fnum rin)
           (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (dnp (bitn rin 25))
                  (fzp (bitn rin 24))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fsqrt4 opa fnum fzp dnp rmode)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-sqrt-spec (bits opa (1- fmtw) 0) rin f)
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (fnum (lambda () (if (ic) fnum (fnum))))
                         (rin (lambda () (if (ic) rin (rin))))))
		  :in-theory (disable arm-sqrt-spec))		  
          ("Subgoal 1" :use (input-constraints-lemma))))
