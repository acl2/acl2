;;;***************************************************************
;;;Proof of Correctness of a Floating Point Multiplier

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1999
;;;***************************************************************

;;This book generates a proof of the correctness theorem, according to
;;the plan outlined in "spec.lisp".  The proof is faithfully based on
;;the informal proof presented in the paper, "Formal Verification of
;;Floating Point Operations with ACL2".  Thus, the paper may serve as
;;documentation for this file.  As a way of identifying the ACL2
;;lemmas that correspond to the lemmas listed in the paper, their
;;names appear here in upper case.

(in-package "ACL2")

(include-book "fmul-star")

; v2-6 change:
(in-theory (disable rearrange-fractional-coefs-equal))

(defun mu* () (precision (pc*)))

(defun mode* () (mode (rc*)))

(defun sticky* ()
  (if (= (overflow*) 1)
      (sticky_of*)
    (sticky_nof*)))

(defun rconst* ()
  (if (= (overflow*) 1)
      (rconst_of*)
    (rconst_nof*)))

(defun add* ()
  (if (= (overflow*) 1)
      (add_of*)
    (add_nof*)))

(defun carry* ()
  (if (= (overflow*) 1)
      (carry_of*)
    (carry_nof*)))

(progn

; Matt K. mod: In April 2016, ACL2 started providing a type-set bit for the set
; {1}.  The new computed type-set of {0,1} for carry* and overflow*, as opposed
; to natp, caused some proofs below to fail.  We take care of that here, by
; restoring the former type-sets for these two functions.

(defthm natp-carry*
  (natp (carry*))
  :rule-classes :type-prescription)

(defthm natp-overflow*
  (natp (overflow*))
  :rule-classes :type-prescription)

(in-theory (disable (:t carry*) (:t overflow*)))
)

(defun mask* ()
  (if (= (overflow*) 1)
      (mask_of*)
    (mask_nof*)))

(defun sig* ()
  (if (= (overflow*) 1)
      (sig_of*)
    (sig_nof*)))

(defun p* ()
  (if (= (overflow*) 1)
      128
    127))

(defun modep* ()
  (cond ((and (eql (mode*) 'inf) (= (sgnz*) 1))
	 'minf)
	((and (eql (mode*) 'minf) (= (sgnz*) 1))
	 'inf)
	(t
	 (mode*))))

(in-theory (disable mu* mode* sticky* rconst* add* mask* carry* sig* p* modep*
		    (:executable-counterpart mu*) (:executable-counterpart mode*)
		    (:executable-counterpart sticky*) (:executable-counterpart rconst*)
		    (:executable-counterpart add*) (:executable-counterpart mask*)
		    (:executable-counterpart carry*) (:executable-counterpart sig*)
		    (:executable-counterpart p*) (:executable-counterpart modep*)))

(in-theory (enable rc_c2* pc_c2* sgnz_c3* exp_sum_c3* sigx_c3* sigy_c3*
		   rc_c3* pc_c3* rc_c4* pc_c4* sgnz_c4* exp_sum_c4*))

(in-theory (disable normal-encoding-p flip fmul rnd ieee-mode-p repp
		    expt (:executable-counterpart expt)))

(defthm overflow-0-1
    (or (= (overflow*) 0)
	(= (overflow*) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn overflow*))))

(defthm pc-0-1
    (or (= (pc*) 0)
	(= (pc*) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec)
		  :use (input-spec*))))

(defthm rc-vals
    (member (rc*) '(0 1 2 3))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec)
		  :use (input-spec*))))

(defthm mu-vals
    (member (mu*) '(24 53))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mu*)
		  :use (pc-0-1))))

(defthm sticky-0-1
    (or (= (sticky*) 0)
	(= (sticky*) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky* sticky_nof* sticky_of*)
		  :use (pc-0-1
			(:instance bitn-0-1
				   (x (mu*))
				   (n (- 126 (mu*))))))))

(defthm sgnz-rewrite
    (equal (sgnz*) (if (= (sgnx*) (sgny*)) 0 1))
  :hints (("Goal" :in-theory (enable sgnz* sgnx* sgny*)
		  :use ((:instance bitn-0-1 (x (x*)) (n 79))
			(:instance bitn-0-1 (x (y*)) (n 79))))))

(in-theory (disable sgnz-rewrite))

(defthm CARRY-REWRITE
    (equal (carry*) (bitn (add*) (p*)))
  :hints (("Goal" :in-theory (enable p* carry_of* carry_nof* carry* add*)
		  :use (overflow-0-1))))

(in-theory (disable carry-rewrite))

(defthm carry-0-1
    (member (carry*) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* carry-rewrite)
		  :use ((:instance bitn-0-1 (x (add*)) (n (p*)))))))

(defthm SIG-REWRITE
    (equal  (sig*)
	    (logior (* (carry*) (expt 2 (1- (p*))))
		    (logand (add*) (mask*))))
  :hints (("Goal" :in-theory (enable sticky* p* mask* sig* sig_of* sig_nof* carry* add*)
		  :use (sticky-0-1
			(:instance bitn-0-1 (x (add*)) (n (- (1- (p*)) (mu*))))))))

(in-theory (disable sig-rewrite))

(defthm MASK-REWRITE
    (equal (mask*)
	   (if (and (eql (mode*) 'near)
		    (= (sticky*) 0)
		    (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))
	       (- (expt 2 (p*)) (expt 2 (- (p*) (1- (mu*)))))
	     (- (expt 2 (p*)) (expt 2 (- (p*) (mu*))))))
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) add* mode*
				     sticky* p* mu* mask* mask_of* mask_nof*)
		  :use (pc-0-1
			rc-vals
			sticky-0-1
			overflow-0-1
			(:instance bitn-0-1 (x (add_nof*)) (n 73))
			(:instance bitn-0-1 (x (add_of*)) (n 74))
			(:instance bitn-0-1 (x (add_nof*)) (n 102))
			(:instance bitn-0-1 (x (add_of*)) (n 103))))))

(in-theory (disable mask-rewrite))

(defthm rem-mask
    (= (rem (mask*) (expt 2 (- (p*) 64)))
       0)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) mask-rewrite
				     precision p* mu*))))

(defthm mask-nat
    (and (integerp (mask*))
	 (>= (mask*) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* (:executable-counterpart expt) mask-rewrite)
		  :use (mu-vals overflow-0-1))))

(defthm RCONST-REWRITE
    (equal (rconst*)
	   (case (modep*)
	     (near (expt 2 (- (p*) (1+ (mu*)))))
	     (inf (1- (expt 2 (- (p*) (mu*)))))
	     (t 0)))
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) modep* mode*
				     rconst* rconst_doub_of* rconst_sing_of*
				     rconst_of* mu* rconst_nof* p* sgnz-rewrite)
		  :use (pc-0-1 rc-vals overflow-0-1))))

(in-theory (disable rconst-rewrite))

(defthm sigf-bnds
    (implies (normal-encoding-p z (extfmt))
	     (and (integerp (sigf z (extfmt)))
		  (< (sigf z (extfmt)) (expt 2 64))
		  (>= (sigf z (extfmt)) (expt 2 63))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable extfmt normal-encoding-p)
		  :use ((:instance normal-encoding-lemma (phi (extfmt)))))))

(defthm sigx-bnds
    (and (integerp (sigx*))
	 (< (sigx*) (expt 2 64))
	 (>= (sigx*) (expt 2 63)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec sigx*)
		  :use (input-spec*
			(:instance sigf-bnds (z (x*)))))))

(defthm sigx-nat
    (not (< (sigx*) 0))
  :hints (("Goal" :use (sigx-bnds))))

(defthm sigy-bnds
    (and (integerp (sigy*))
	 (< (sigy*) (expt 2 64))
	 (>= (sigy*) (expt 2 63)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec sigy*)
		  :use (input-spec*
			(:instance sigf-bnds (z (y*)))))))

(defthm sigy-nat
    (not (< (sigy*) 0))
  :hints (("Goal" :use (sigy-bnds))))

(defthm expo-sigx
    (= (expo (sigx*)) 63)
  :rule-classes ()
  :hints (("Goal" :use (sigx-bnds
			(:instance expo-unique (x (sigx*)) (n 63))))))

(defthm expo-sigy
    (= (expo (sigy*)) 63)
  :rule-classes ()
  :hints (("Goal" :use (sigy-bnds
			(:instance expo-unique (x (sigy*)) (n 63))))))

(defthm prod-bnds
    (and (integerp (prod*))
	 (< (prod*) (expt 2 128))
	 (>= (prod*) (expt 2 126)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable prod* (:executable-counterpart expt))
		  :use (sigx-bnds sigy-bnds))))

(defthm integerp-prod
    (integerp (prod*))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use (prod-bnds))))

(defthm prod-nat
    (not (< (prod*) 0))
  :hints (("Goal" :use (prod-bnds))))

(defthm EXPO-PROD
    (equal (expo (prod*)) (1- (p*)))
  :hints (("Goal" :in-theory (enable p* overflow*)
		  :use (prod-bnds
			(:instance expo-unique (x (prod*)) (n 126))
			(:instance expo-unique (x (prod*)) (n 127))
			(:instance expo-upper-bound (x (prod*)))
			(:instance expo-lower-bound (x (prod*)))
			(:instance bit-expo-b (x (prod*)) (n 127))
			(:instance bit-expo-a (x (prod*)) (n 127))))))

(in-theory (disable expo-prod))

(defthm sig-hat
    (implies (normal-encoding-p z (extfmt))
	     (= (sigf z (extfmt))
		(* (expt 2 63) (sig (hat z)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable extfmt hat expt)
		  :use (:instance code-b (phi (extfmt))))))

(defthm sig-hat-x
    (equal (sigx*)
	   (* (expt 2 63) (sig (hat (x*)))))
  :hints (("Goal" :in-theory (enable input-spec sigx*)
		  :use (input-spec*
			(:instance sig-hat (z (x*)))))))

(defthm sig-hat-y
    (equal (sigy*)
	   (* (expt 2 63) (sig (hat (y*)))))
  :hints (("Goal" :in-theory (enable input-spec sigy*)
		  :use (input-spec*
			(:instance sig-hat (z (y*)))))))

(in-theory (disable sig-hat-x sig-hat-y))

(defthm sig-x-y-bnds
    (and (integerp (* (sigx*) (sigy*)))
	 (>= (* (sigx*) (sigy*)) (expt 2 126))
	 (< (* (sigx*) (sigy*)) (expt 2 128)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt))
		  :use (sigx-bnds sigy-bnds))))

(defthm sig-prod-1
    (= (prod*) (* (expt 2 126) (sig (hat (x*))) (sig (hat (y*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) prod*
				     sig-hat-x sig-hat-y)
		  :use (sig-x-y-bnds sig-hat-x sig-hat-y))))

(defthm sig-prod-2
    (= (prod*)
       (* (expt 2 (expo (prod*)))
	  (sig (hat (x*)))
	  (sig (hat (y*)))
	  (expt 2  (- (overflow*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable prod* p* sig-hat-x sig-hat-y)
		  :use (expo-prod
			sig-prod-1
			overflow-0-1
			(:instance expo+
				   (m (+ (overflow*) 126))
				   (n (- (overflow*))))))))

(defthm SIG-PROD
    (equal (sig (prod*) )
	   (* (sig (hat (x*)))
	      (sig (hat (y*)))
	      (expt 2  (- (overflow*)))))
  :hints (("Goal" :use (sig-prod-2
			(:instance fp-abs (x (prod*)))
			(:instance cancel-equal-*
				   (a (expt 2 (expo (prod*))))
				   (r (sig (prod*)))
				   (s (* (sig (hat (x*)))
					 (sig (hat (y*)))
					 (expt 2  (- (overflow*))))))))))

(in-theory (disable sig-prod))

(defthm hat-x-hat-y-rewrite-1
    (equal (* (hat (x*)) (hat (y*)))
	   (* (sgn (hat (x*)))
	      (sig (hat (x*)))
	      (expt 2 (expo (hat (x*))))
	      (sgn (hat (y*)))
	      (sig (hat (y*)))
	      (expt 2 (expo (hat (y*))))))
  :hints (("Goal" :use ((:instance fp-rep (x (hat (x*))))
			(:instance fp-rep (x (hat (y*))))))))

(in-theory (disable hat-x-hat-y-rewrite-1))

(defthm hat-x-hat-y-rewrite-2
    (equal (* (hat (x*)) (hat (y*)))
	   (* (sgn (hat (x*)))
	      (sgn (hat (y*)))
	      (sig (prod*))
	      (expt 2 (+ (expo (hat (x*))) (expo (hat (y*))) (overflow*)))))
  :hints (("Goal" :in-theory (enable sig-prod sgn hat-x-hat-y-rewrite-1)
		  :use (overflow-0-1
			sig-prod
			(:instance expt-pos
				   (x (+ (expo (hat (x*)))
					 (expo (hat (y*))))))
			(:instance sig-lower-bound (x (hat (x*))))
			(:instance sig-lower-bound (x (hat (y*))))
			(:instance expo+ (m (expo (hat (x*)))) (n (hat (y*))))))))

(in-theory (disable hat-x-hat-y-rewrite-2))

(defthm x-non-zero
    (not (= (hat (x*)) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec extfmt hat)
		  :use (input-spec*
			(:instance normal-non-zero (z (x*)) (phi (extfmt)))))))

(defthm y-non-zero
    (not (= (hat (y*)) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec extfmt hat)
		  :use (input-spec*
			(:instance normal-non-zero (z (y*)) (phi (extfmt)))))))

(defthm abs-hat-x-hat-y
    (equal (abs (* (hat (x*)) (hat (y*))))
	   (* (sig (prod*))
	      (expt 2 (+ (expo (hat (x*))) (expo (hat (y*))) (overflow*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn hat-x-hat-y-rewrite-2)
		  :use (overflow-0-1
			x-non-zero
			y-non-zero
			(:instance expt-pos
				   (x (+ (overflow*)
					 (expo (hat (x*)))
					 (expo (hat (y*))))))
			(:instance sig-lower-bound (x (prod*)))))))

(defthm EXPO-XY
    (equal (expo (* (hat (x*)) (hat (y*))))
	   (+ (expo (hat (x*))) (expo (hat (y*))) (overflow*)))
  :hints (("Goal" :in-theory (enable sgn)
		  :use (x-non-zero
			y-non-zero
			(:instance sig-lower-bound (x (prod*)))
			(:instance sig-upper-bound (x (prod*)))
			abs-hat-x-hat-y
			(:instance fp-rep-unique
				   (x (* (hat (x*)) (hat (y*))))
				   (m (sig (prod*)))
				   (e (+ (expo (hat (x*)))
					 (expo (hat (y*)))
					 (overflow*))))))))

(defthm SIG-XY
    (equal (sig (* (hat (x*)) (hat (y*))))
	   (sig (prod*)))
  :hints (("Goal" :in-theory (enable sgn)
		  :use (x-non-zero
			y-non-zero
			(:instance sig-lower-bound (x (prod*)))
			(:instance sig-upper-bound (x (prod*)))
			abs-hat-x-hat-y
			(:instance fp-rep-unique
				   (x (* (hat (x*)) (hat (y*))))
				   (m (sig (prod*)))
				   (e (+ (expo (hat (x*)))
					 (expo (hat (y*)))
					 (overflow*))))))))

(in-theory (disable expo-xy sig-xy))

(defthm sticky-exact-1
    (iff (= (sticky_nof*) 0)
	 (= (rem (prod*) (expt 2 (- 126 (mu*)))) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mu* sticky_nof* bits-0-rem)
		  :use (pc-0-1))))

(defthm sticky-exact-2
    (iff (= (sticky_of*) 0)
	 (and (= (sticky_nof*) 0)
	      (= (bitn (prod*) (- 126 (mu*))) 0)))
  :hints (("Goal" :in-theory (enable sticky_of* sticky_nof* mu*)
		  :use ((:instance bitn-0-1 (x (prod*)) (n (- 126 (mu*))))
			(:instance bits-bitn (x (prod*)) (n (- 126 (mu*))))))))

(defthm sticky-exact-3
    (iff (= (sticky_of*) 0)
	 (and (= (rem (prod*) (expt 2 (- 126 (mu*)))) 0)
	      (= (rem (fl (/ (prod*) (expt 2 (- 126 (mu*))))) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable precision mu*)
		  :use ((:instance sticky-exact-2)
			(:instance sticky-exact-1)
			(:instance bitn-def (x (prod*)) (k (- 126 (mu*))))))))

(defthm sticky-exact-4
    (iff (= (sticky_of*) 0)
	 (= (rem (prod*) (expt 2 (- 127 (mu*)))) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) precision mu*)
		  :use ((:instance sticky-exact-3)
			(:instance fl-rem-5 (m (prod*)) (n (expt 2 (- 126 (mu*)))) (p 2))
			(:instance expo+ (m (- 126 (mu*))) (n 1))))))

(defthm sticky-exact-5
    (iff (= (sticky*) 0)
	 (= (rem (prod*) (expt 2 (- (p*) (1+ (mu*))))) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mu* p* precision sticky*)
		  :use ((:instance sticky-exact-1)
			(:instance sticky-exact-4)))))

(defthm sticky-exact-6
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (> k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (= (rem x (expt 2 k)) 0)
		  (exactp x (- n k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use (exact-bits-a-b exact-bits-a-d))))

(defthm STICKY-EXACT
    (iff (= (sticky*) 0)
	 (exactp (prod*) (1+ (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* precision mu*)
		  :use (sticky-exact-5
			expo-prod
			(:instance sticky-exact-6
				   (x (prod*))
				   (k (- (p*) (1+ (mu*))))
				   (n (p*)))))))

(defthm rconst-bnds
    (and (integerp (rconst*))
	 (not (< (rconst*) 0))
	 (< (rconst*) (expt 2 (p*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* precision rconst-rewrite
				     (:executable-counterpart expt)))))

(defthm ADD-REWRITE
    (equal (add*)
	   (+ (prod*) (rconst*)))
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) expo-prod
				     rconst* add* add_of* add_nof* rconst* p*)
		  :use (prod-bnds
			rconst-bnds
			(:instance expo-upper-bound (x (prod*)))))))

(in-theory (disable add-rewrite))

(defthm add-bnds
    (and (integerp (add*))
	 (<= (expt 2 (1- (p*))) (add*))
	 (< (add*) (expt 2 (1+ (p*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* (:executable-counterpart expt) expo-prod add-rewrite)
		  :use (prod-bnds
			rconst-bnds
			overflow-0-1
			(:instance expo-upper-bound (x (prod*)))
			(:instance expo-lower-bound (x (prod*)))))))

(defthm sig-nat
    (>= (sig*) 0)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sig-rewrite)
		  :use (mask-nat
			add-bnds
			carry-0-1
			(:instance logior-nat
				   (i (* (carry*) (expt 2 (1- (p*)))))
				   (j (logand (add*) (mask*))))
			(:instance logand-nat (i (add*)) (j (mask*)))))))

(defthm sig-bit-1
    (implies (= (carry*) 1)
	     (= (bitn (sig*) (1- (p*))) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* sig-rewrite)
		  :use (mask-nat
			add-bnds
			(:instance bitn-2**n (n (1- (p*))))
			(:instance logand-nat (i (add*)) (j (mask*)))
			(:instance bit-dist-b
				   (x (* (carry*) (expt 2 (1- (p*)))))
				   (y (logand (add*) (mask*)))
				   (n (1- (p*))))
			(:instance bitn-0-1 (x (logand (add*) (mask*))) (n (1- (p*))))))))

(defthm bitn-mask
    (= (bitn (mask*) (1- (p*))) 1)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mask* mask_of* mask_nof* p*)
		  :use (overflow-0-1
			pc-0-1))))

(defthm bitn-add
    (implies (= (carry*) 0)
	     (= (bitn (add*) (1- (p*))) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* carry-rewrite)
		  :use (add-bnds
			overflow-0-1
			(:instance bit-expo-b (x (add*)) (n (p*)))
			(:instance bit-expo-b (x (add*)) (n (1- (p*))))))))

(defthm sig-rewrite-0
    (implies (= (carry*) 0)
	     (equal (sig*)
		    (logand (add*) (mask*))))
  :hints (("Goal" :in-theory (enable sig-rewrite)
		  :use (mask-nat
			add-bnds
			(:instance logand-nat (i (add*)) (j (mask*)))
			(:instance bit-basic-d (x 0) (y (logand (add*) (mask*))))
			(:instance bit-basic-b (x (logand (add*) (mask*))))))))

(in-theory (disable sig-rewrite-0))

(defthm sig-bit-0
    (implies (= (carry*) 0)
	     (= (bitn (sig*) (1- (p*))) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* sig-rewrite-0)
		  :use (mask-nat
			add-bnds
			bitn-add
			bitn-mask
			(:instance logand-nat (i (add*)) (j (mask*)))
			(:instance bit-dist-a (x (add*)) (y (mask*)) (n (1- (p*))))))))

(defthm SIG-BIT
    (= (bitn (sig*) (1- (p*))) 1)
  :rule-classes ()
  :hints (("Goal" :use (carry-0-1 sig-bit-0 sig-bit-1))))

(defthm sig-add-expo-1
    (implies (= (carry*) 0)
	     (<= (sig*) (add*)))
  :rule-classes()
  :hints (("Goal" :in-theory (enable sig-rewrite-0)
		  :use (mask-nat
			add-bnds
			(:instance and-dist-a (x (add*)) (y (mask*)))))))

(defthm sig-add-expo-2
    (implies (= (carry*) 0)
	     (< (add*) (expt 2 (p*))))
  :rule-classes()
  :hints (("Goal" :in-theory (enable carry-rewrite)
		  :use (add-bnds
			(:instance bit-expo-b (x (add*)) (n (p*)))))))

(defthm sig-add-expo-3
    (<= (expt 2 (1- (p*))) (sig*))
  :rule-classes()
  :hints (("Goal" :use (sig-bit
			sig-nat
			(:instance bit-expo-a (x (sig*)) (n (1- (p*))))))))

(defthm sig-add-expo-4
    (implies (= (carry*) 0)
	     (and (= (expo (sig*)) (1- (p*)))
		  (= (expo (add*)) (1- (p*)))))
  :rule-classes()
  :hints (("Goal" :in-theory (enable p*)
		  :use (sig-add-expo-1
			sig-add-expo-2
			sig-add-expo-3
			(:instance expo-squeeze (x (sig*)) (n (1- (p*))))
			(:instance expo-squeeze (x (add*)) (n (1- (p*))))))))

(defthm sig-add-expo-5
    (implies (= (carry*) 1)
	     (= (expo (add*)) (p*)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable carry-rewrite p*)
		  :use (add-bnds
			(:instance expo-squeeze (x (add*)) (n (p*)))
			(:instance bit-expo-a (x (add*)) (n (p*)))))))

(defthm sig-add-expo-6
    (implies (= (carry*) 1)
	     (< (sig*) (expt 2 (1+ (p*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* sig-rewrite)
		  :use (mask-nat
			add-bnds
			(:instance or-dist-a
				   (n (1+ (p*)))
				   (x (expt 2 (1- (p*))))
				   (y (logand (add*) (mask*))))
			(:instance logand-nat (i (add*)) (j (mask*)))
			(:instance and-dist-a (x (add*)) (y (mask*)))))))

(defthm sig-add-expo-7
    (implies (= (carry*) 1)
	     (<= (expo (sig*)) (p*)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt p*)
		  :use (sig-nat
			sig-add-expo-6
			(:instance expo<= (x (sig*)) (n (p*)))))))

(defthm SIG-ADD-EXPO
    (and (<= (expo (sig*)) (expo (add*)))
	 (equal (expo (add*)) (+ (1- (p*)) (carry*))))
  :rule-classes ()
  :hints (("Goal" :use (carry-0-1
			sig-add-expo-5
			sig-add-expo-7
			sig-add-expo-4))))

(defthm rem-add-mask
    (= (rem (logand (add*) (mask*)) (expt 2 (- (p*) 64)))
       0)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p*)
		  :use (mask-nat
			add-bnds
			rem-mask
			(:instance rem-logand (x (add*)) (y (mask*)) (n (- (p*) 64)))
			(:instance bit-basic-a (x (rem (add*) (expt 2 (- (p*) 64)))))
			(:instance rem>=0 (m (add*)) (n (expt 2 (- (p*) 64))))))))

(defthm REM-SIG
    (= (rem (sig*) (expt 2 (- (p*) 64)))
       0)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) p* sig-rewrite)
		  :use (rem-add-mask
			carry-0-1
			mask-nat
			add-bnds
			(:instance or-dist-d
				   (x (* (carry*) (expt 2 (1- (p*)))))
				   (y (logand (add*) (mask*)))
				   (n (- (p*) 64)))
			(:instance logand-nat (i (add*)) (j (mask*)))
			(:instance bit-basic-b
				   (x (rem (* (carry*) (expt 2 (1- (p*))))
					   (expt 2 (- (p*) 64)))))))))

(defthm sigz-rewrite
    (equal (sigz*)
	   (bits (sig*) (1- (p*)) (- (p*) 64)))
  :hints (("Goal" :in-theory (enable p* sigz* sig*)
		  :use (overflow-0-1))))

(in-theory (disable sigz-rewrite))

(defthm sigz-bnds
    (and (>= (sigz*) 0)
	 (< (sigz*) (expt 2 64)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sigz-rewrite p*)
		  :use (sig-nat
			(:instance bits-nat (x (sig*)) (i (1- (p*))) (j (- (p*) 64)))
			(:instance bits< (x (sig*)) (i (1- (p*))) (j (- (p*) 64)))))))

(defthm expf-bnds
    (implies (normal-encoding-p z (extfmt))
	     (and (integerp (expf z (extfmt)))
		  (< (expf z (extfmt)) (expt 2 15))
		  (>= (expf z (extfmt)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable extfmt)
		  :use ((:instance normal-encoding-lemma (phi (extfmt)))))))

(defthm expx-bnds
    (and (integerp (expx*))
	 (< (expx*) (expt 2 15))
	 (>= (expx*) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec expx*)
		  :use (input-spec*
			(:instance expf-bnds (z (x*)))))))

(defthm expy-bnds
    (and (integerp (expy*))
	 (< (expy*) (expt 2 15))
	 (>= (expy*) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec expy*)
		  :use (input-spec*
			(:instance expf-bnds (z (y*)))))))

(defthm exp-sum-bnds
    (and (integerp (exp_sum*))
	 (< (exp_sum*) (expt 2 15))
	 (>= (exp_sum*) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem exp_sum* expx* expy*)
		  :use (expx-bnds
			expy-bnds
			(:instance rem+rem (a #x4001) (b (+ (expx*) (expy*))) (n (expt 2 15)))
			(:instance bits-nat
				   (x (+ (expx*) (expy*) 16385))
				   (i 14)
				   (j 0))
			(:instance bits<
				   (x (+ (expx*) (expy*) 16385))
				   (i 14)
				   (j 0))))))

(defthm expz-rewrite
    (equal (expz*)
	   (if (= (overflow*) 1)
	       (rem (+ (exp_sum*) (+ (carry*) 1)) (expt 2 15))
	     (rem (+ (exp_sum*) (+ (carry*))) (expt 2 15))))
  :hints (("Goal" :in-theory (enable carry* expz* exp_of* exp_nof* bits-0-rem)
		  :use (overflow-0-1
			exp-sum-bnds
			(:instance rem+rem (a 1) (b (+ (carry*) (exp_sum*))) (n (expt 2 15)))))))

(in-theory (disable expz-rewrite))

(defthm expz-bnds
    (and (>= (expz*) 0)
	 (< (expz*) (expt 2 15)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exp_sum* expz-rewrite)
		  :use (carry-0-1
			exp-sum-bnds
			(:instance rem<n (m (+ (exp_sum*) (+ (carry*) 1))) (n (expt 2 15)))
			(:instance rem<n (m (+ (exp_sum*) (carry*))) (n (expt 2 15)))
			(:instance rem>=0 (m (+ (exp_sum*) (+ (carry*) 1))) (n (expt 2 15)))
			(:instance rem>=0 (m (+ (exp_sum*) (carry*))) (n (expt 2 15)))))))

(defthm sgnf-z
    (= (sgnf (z*) (extfmt)) (sgnz*))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) z* extfmt
				     bits-0-rem p* sgnz-rewrite)
		  :use (sigz-bnds
			expz-bnds
			(:instance bitn-def (x (z*)) (k 79))
			(:instance fl-unique
				   (x (/ (z*) (expt 2 79)))
				   (n (sgnz*)))))))

(defthm expf-z
    (= (expf (z*) (extfmt)) (expz*))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) z* bits extfmt
				     bits-0-rem p* sgnz-rewrite)
		  :use (sigz-bnds
			expz-bnds
			(:instance fl-unique
				   (x (+ (sgnz*) (/ (sigz*) (expt 2 64))))
				   (n (sgnz*)))
			(:instance rem<
				   (m (+ (* (expt 2 64) (expz*)) (sigz*)))
				   (n (expt 2 79)))
			(:instance rem+
				   (m (+ (* (expt 2 64) (expz*)) (sigz*)))
				   (n (expt 2 79))
				   (a (sgnz*)))))))

(defthm sigf-z
    (= (sigf (z*) (extfmt)) (sigz*))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable z* extfmt bits-0-rem p* sgnz-rewrite)
		  :use (sigz-bnds
			expz-bnds
			(:instance rem< (m (sigz*)) (n (expt 2 64)))
			(:instance rem+
				   (m (sigz*))
				   (n (expt 2 64))
				   (a (+ (expz*) (* (expt 2 15) (sgnz*)))))))))

(defun rho* () (rem (sig*) (expt 2 (p*))))

(in-theory (disable rho* (:executable-counterpart rho*)))

(defthm rho-bit
    (= (bitn (rho*) (1- (p*)))
       1)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho*)
		  :use (sig-bit
			sig-nat
			(:instance bitn-rem (x (sig*)) (j (1- (p*))) (k (p*)))))))

(defthm rho-nat
    (and (integerp (rho*))
	 (>= (rho*) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* rho*)
		  :use (sig-nat
			(:instance rem>=0 (m (sig*)) (n (expt 2 (p*))))))))

(defthm expo-rho
    (= (expo (rho*)) (1- (p*)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho* p*)
		  :use (sig-nat
			rho-nat
			rho-bit
			(:instance rem<n (m (sig*)) (n (expt 2 (p*))))
			(:instance expo-squeeze (x (rho*)) (n (1- (p*))))
			(:instance bit-expo-a (x (rho*)) (n (1- (p*))))))))

(defthm rem-rho
    (= (rem (rho*) (expt 2 (- (p*) 64)))
       0)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* rho*)
		  :use (rem-sig
			sig-nat
			(:instance rem-rem (x (sig*)) (a (p*)) (b (- (p*) 64)))))))

(defthm sigz-rho
    (= (sigz*)
       (/ (rho*) (expt 2 (- (p*) 64))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) bits rho* p* sigz-rewrite)
		  :use (rho-nat
			sig-nat
			rem-rho
			(:instance rem=rem (a (rho*)) (b 0) (n (expt 2 (- (p*) 64))))
			(:instance rem-bits (x (sig*)) (y (rho*)) (i (1- (p*))) (j (- (p*) 64)))
			(:instance rem-rem (x (sig*)) (a (p*)) (b (p*)))))))

(defthm expo-sigz
    (= (expo (sigz*)) 63)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho* p*
                                     ;; v2-6 change
                                     rearrange-fractional-coefs-equal)
		  :use (sigz-rho
			expo-rho
			(:instance sig-expo-shift (x (sigz*)) (n (- (p*) 64)))))))

(defthm z-nat
    (>= (z*) 0)
  :rule-classes ()
  :hints (("Goal" :in-theory (enable z*)
		  :use (sigz-bnds
			expz-bnds
			sgnz-rewrite))))

(defthm z-normal
    (normal-encoding-p (z*) (extfmt))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable normal-encoding-p z* extfmt)
		  :use (sigf-z
			expo-sigz
			sigz-bnds
			z-nat
			(:instance expo-lower-bound (x (sigz*)))))))

(defthm x-y-normal
    (and (normal-encoding-p (x*) (extfmt))
	 (normal-encoding-p (y*) (extfmt)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable input-spec)
		  :use (input-spec*))))

(defthm sgn-hat
    (and (= (sgn (hat (z*))) (if (= (sgnz*) 0) 1 -1))
	 (= (sgn (hat (x*))) (if (= (sgnx*) 0) 1 -1))
	 (= (sgn (hat (y*))) (if (= (sgny*) 0) 1 -1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgnx* sgny* extfmt hat)
		  :use (sgnf-z
			z-normal
			x-y-normal
			(:instance code-a (phi (extfmt)) (z (z*)))
			(:instance code-a (phi (extfmt)) (z (x*)))
			(:instance code-a (phi (extfmt)) (z (y*)))))))

(defthm x-y-non-zero
    (and (not (= (hat (x*)) 0))
	 (not (= (hat (y*)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable extfmt hat)
		  :use (x-y-normal
			(:instance normal-non-zero (phi (extfmt)) (z (x*)))
			(:instance normal-non-zero (phi (extfmt)) (z (y*)))))))


(defthm sgn-xy
    (= (sgn (* (hat (x*)) (hat (y*))))
       (* (sgn (hat (x*))) (sgn (hat (y*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn)
		  :use (x-y-non-zero))))

(defthm SGN-Z
    (= (sgn (hat (z*)))
       (sgn (* (hat (x*)) (hat (y*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgnx* sgny* sgnz-rewrite)
		  :use (sgn-hat
			sgn-xy
			sgn-hat
			(:instance bitn-0-1 (x (x*)) (n 79))
			(:instance bitn-0-1 (x (y*)) (n 79))))))

(defthm sig-z-lemma
    (= (sig (hat (z*)))
       (* (sigf (z*) (extfmt))
	  (expt 2 -63)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable hat extfmt)
		  :use (z-normal
			(:instance code-b (z (z*)) (phi (extfmt)))))))

(defthm SIG-Z
    (= (sig (hat (z*)))
       (/ (rho*)
	  (expt 2 (1- (p*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* (:executable-counterpart expt))
		  :use (sig-z-lemma sigf-z sigz-rho))))

(defthm expo-hat
    (and (= (expo (hat (z*))) (- (expz*) (1- (expt 2 14))))
	 (= (expo (hat (x*))) (- (expx*) (1- (expt 2 14))))
	 (= (expo (hat (y*))) (- (expy*) (1- (expt 2 14)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable hat expx* expy* extfmt)
		  :use (expf-z
			x-y-normal
			z-normal
			(:instance code-c (z (z*)) (phi (extfmt)))
			(:instance code-c (z (x*)) (phi (extfmt)))
			(:instance code-c (z (y*)) (phi (extfmt)))))))

(defthm expo-z-1
    (= (expz*)
       (rem (+ (expx*) (expy*) (expt 2 14) 1 (carry*) (overflow*))
	    (expt 2 15)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem exp_sum* expz-rewrite
				     (:executable-counterpart expt))
		  :use (overflow-0-1
			carry-0-1
			expx-bnds
			expy-bnds
			(:instance rem+rem
				   (a (1+ (expt 2 14)))
				   (b (+ (expx*) (expy*)))
				   (n (expt 2 15)))
			(:instance rem+rem
				   (a (+ (carry*) (overflow*)))
				   (b (+ (expx*) (expy*) (expt 2 14) 1))
				   (n (expt 2 15)))))))

(defthm expo-z-2
    (= (rem (+ (expt 2 15) (expo (hat (z*))))
	    (expt 2 15))
       (rem (+ (expt 2 15)
	       (expo (* (hat (x*)) (hat (y*))))
	       (carry*))
	    (expt 2 15)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt))
		  :use (expo-z-1
			expo-hat
			expx-bnds
			expy-bnds
			expo-xy
			carry-0-1
			overflow-0-1
			(:instance rem+rem
				   (a (1+ (expt 2 14)))
				   (b (+ (expx*) (expy*) (expt 2 14) 1 (carry*) (overflow*)))
				   (n (expt 2 15)))
			(:instance rem+
				   (a 1)
				   (m (+ (expx*) (expy*) 2 (carry*) (overflow*)))
				   (n (expt 2 15)))))))

(defun k* ()
  (/ (- (expo (hat (z*)))
	(+ (expo (* (hat (x*)) (hat (y*)))) (carry*)))
     (expt 2 15)))

(in-theory (disable k* (:executable-counterpart k*)))

(defthm rewrite-hack-1
    (equal (+ 1 (expo (* (hat (x*)) (hat (y*))))
	      32768)
	   (+ (expo (* (hat (x*)) (hat (y*))))
	      32769)))

(defthm EXPO-Z
    (and (integerp (k*))
	 (= (expo (hat (z*)))
	    (+ (expo (* (hat (x*)) (hat (y*))))
	       (carry*)
	       (* (k*) (expt 2 15)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable k* (:executable-counterpart expt))
		  :use (expo-z-2
			expx-bnds
			expy-bnds
			expz-bnds
			expo-hat
			carry-0-1
			(:instance expo-prod-lower (x (hat (x*))) (y (hat (y*))))
			(:instance rem=rem
				   (a (+ (expt 2 15) (expo (hat (z*)))))
				   (b (+ (expt 2 15) (expo (* (hat (x*)) (hat (y*)))) (carry*)))
				   (n (expt 2 15)))))))

(defthm carry-0-sig-bnd
    (implies (= (carry*) 0)
	     (< (sig*) (expt 2 (p*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p*)
		  :use (sig-nat
			sig-add-expo
			(:instance expo>= (x (sig*)) (n (p*)))))))

(defthm carry-0-sig-rho
    (implies (= (carry*) 0)
	     (= (sig*) (rho*)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho* p*)
		  :use (carry-0-sig-bnd
			sig-nat
			(:instance rem< (m (sig*)) (n (expt 2 (p*))))))))

(defthm prod-bit
    (implies (= (modep*) 'near)
	     (iff (= (bitn (add*) (- (p*) (1+ (mu*)))) 0)
		  (= (bitn (prod*) (- (p*) (1+ (mu*)))) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable add-rewrite rconst-rewrite precision p* mu*)
		  :use (prod-nat
			(:instance bitn-0-1 (x (prod*)) (n (- (p*) (1+ (mu*)))))
			(:instance bitn-0-1 (x (add*)) (n (- (p*) (1+ (mu*)))))
			(:instance bit+-a (x (prod*)) (n (- (p*) (1+ (mu*)))))))))

(defthm prod-exactp-1
    (iff (exactp (prod*) (mu*))
	 (= (bits (prod*) (- (p*) (1+ (mu*))) 0)
	    0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* precision)
		  :use (prod-nat
			expo-prod
			pc-0-1
			(:instance exact-bits-a-b (x (prod*)) (n (p*)) (k (- (p*) (mu*))))
			(:instance exact-bits-a-d
				   (x (prod*))
				   (n (p*))
				   (k (- (p*) (mu*))))))))

(defthm prod-exactp-2
    (iff (exactp (prod*) (mu*))
	 (and (= (sticky*) 0)
	      (= (bitn (prod*) (- (p*) (1+ (mu*)))) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mu* bits-0-rem precision p*)
		  :use (prod-nat
			prod-exactp-1
			pc-0-1
			sticky-exact-5
			(:instance bits-bitn (x (prod*)) (n (- (p*) (1+ (mu*)))))))))

(defthm carry-0-near-1
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near)
		  (= (sticky*) 0)
		  (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))
	     (= (sig*)
		(logand (+ (prod*) (expt 2 (- (p*) (1+ (mu*)))))
		        (- (expt 2 (p*)) (expt 2 (- (p*) (1- (mu*))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* precision modep* add-rewrite
				     rconst-rewrite mask-rewrite)
		  :use (sig-rewrite-0))))

(defthm carry-0-near-2
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near)
		  (= (sticky*) 0)
		  (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))
	     (= (sig*)
		(trunc (+ (prod*) (expt 2 (- (p*) (1+ (mu*)))))
		       (1- (mu*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* precision add-rewrite
				     rconst-rewrite mask-rewrite)
		  :use (prod-nat
			add-bnds
			pc-0-1
			carry-0-near-1
			sig-add-expo
			(:instance expo-lower-bound (x (add*)))
			(:instance expo-upper-bound (x (add*)))
			(:instance bits-trunc
				   (x (add*))
				   (k (1- (mu*)))
				   (m (p*))
				   (n (p*)))))))

(defthm carry-0-near-3
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near)
		  (= (sticky*) 0)
		  (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))
	     (= (sig*)
		(rnd (prod*) (modep*) (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd p* mu* precision expo-prod)
		  :use (prod-bit
			pc-0-1
			prod-bnds
			carry-0-near-2
			sticky-exact
			prod-exactp-2
			(:instance near-trunc (x (prod*)) (n (mu*)))))))

(defthm carry-0-near-4
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near)
		  (not (and (= (sticky*) 0)
			    (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))))
	     (= (sig*)
		(logand (+ (prod*) (expt 2 (- (p*) (1+ (mu*)))))
		        (- (expt 2 (p*)) (expt 2 (- (p*) (mu*)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* precision modep* add-rewrite
				     rconst-rewrite mask-rewrite)
		  :use (sig-rewrite-0))))

(defthm carry-0-near-5
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near)
		  (not (and (= (sticky*) 0)
			    (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))))
	     (= (sig*)
		(trunc (+ (prod*) (expt 2 (- (p*) (1+ (mu*)))))
		       (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* precision add-rewrite
				     rconst-rewrite mask-rewrite)
		  :use (prod-nat
			add-bnds
			pc-0-1
			carry-0-near-4
			sig-add-expo
			(:instance expo-lower-bound (x (add*)))
			(:instance expo-upper-bound (x (add*)))
			(:instance bits-trunc
				   (x (add*))
				   (k (mu*))
				   (m (p*))
				   (n (p*)))))))

(defthm carry-0-near-6
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near)
		  (not (and (= (sticky*) 0)
			    (= (bitn (add*) (- (p*) (1+ (mu*)))) 0))))
	     (= (sig*)
		(rnd (prod*) (modep*) (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd p* mu* precision expo-prod)
		  :use (prod-bit
			pc-0-1
			prod-bnds
			carry-0-near-5
			sticky-exact
			prod-exactp-2
			(:instance bitn-0-1 (x (prod*)) (n (- (p*) (1+ (mu*)))))
			(:instance near-trunc (x (prod*)) (n (mu*)))))))

(defthm carry-0-near
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'near))
	     (= (sig*)
		(rnd (prod*) (modep*) (mu*))))
  :rule-classes ()
  :hints (("Goal" :use (carry-0-near-3 carry-0-near-6))))

(defthm carry-0-inf-1
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'inf))
	     (= (sig*)
		(logand (+ (prod*) (1- (expt 2 (- (p*) (mu*)))))
		        (- (expt 2 (p*)) (expt 2 (- (p*) (mu*)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* modep* add-rewrite rconst-rewrite mask-rewrite)
		  :use (sig-rewrite-0))))

(defthm carry-0-inf-2
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'inf))
	     (= (sig*)
		(trunc (+ (prod*) (1- (expt 2 (- (p*) (mu*)))))
		       (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* add-rewrite rconst-rewrite mask-rewrite)
		  :use (prod-nat
			add-bnds
			pc-0-1
			carry-0-inf-1
			sig-add-expo
			(:instance expo-lower-bound (x (add*)))
			(:instance expo-upper-bound (x (add*)))
			(:instance bits-trunc (x (add*)) (k (mu*)) (m (p*)) (n (p*)))))))

(defthm carry-0-inf
    (implies (and (= (carry*) 0)
		  (eql (modep*) 'inf))
	     (= (sig*)
		(rnd (prod*) (modep*) (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd p* mu* expo-prod exactp2 (:executable-counterpart expt))
		  :use (pc-0-1
			prod-bnds
			carry-0-inf-2
			(:instance away-imp (x (prod*)) (n (mu*)) (m (p*)))))))

(defthm prod-0
    (equal (+ (prod*) 0)
	   (prod*)))

(defthm carry-0-minf-1
    (implies (and (= (carry*) 0)
		  (or (eql (modep*) 'trunc)
		      (eql (modep*) 'minf)))
	     (= (sig*)
		(logand (prod*)
		        (- (expt 2 (p*)) (expt 2 (- (p*) (mu*)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* modep* add-rewrite rconst-rewrite mask-rewrite)
		  :use (sig-rewrite-0))))

(defthm carry-0-minf
    (implies (and (= (carry*) 0)
		  (or (eql (modep*) 'trunc)
		      (eql (modep*) 'minf)))
	     (= (sig*)
		(rnd (prod*) (modep*) (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd p* mu* add-rewrite rconst-rewrite mask-rewrite)
		  :use (prod-nat
			add-bnds
			pc-0-1
			carry-0-minf-1
			sig-add-expo
			(:instance expo-lower-bound (x (add*)))
			(:instance expo-upper-bound (x (add*)))
			(:instance bits-trunc (x (add*)) (k (mu*)) (m (p*)) (n (p*)))))))

(defthm carry-0
    (implies (= (carry*) 0)
	     (= (rho*)
		(rnd (prod*) (modep*) (mu*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd modep* mode*)
		  :use (carry-0-sig-rho
			rc-vals
			carry-0-near
			carry-0-inf
			carry-0-minf))))

(defthm add-upper
    (implies (= (carry*) 1)
	     (< (add*) (+ (expt 2 (p*)) (expt 2 (- (p*) (mu*))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* rconst-rewrite add-rewrite expo-prod
				     (:executable-counterpart expt))
		  :use (add-bnds
			pc-0-1
			prod-nat
			(:instance expo-upper-bound (x (prod*)))))))

(defthm add-lower
    (implies (= (carry*) 1)
	     (<= (expt 2 (p*)) (add*)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p*)
		  :use (add-bnds
			sig-add-expo
			(:instance expo-lower-bound (x (add*)))))))

(defthm rem-add-upper
    (implies (= (carry*) 1)
	     (< (rem (add*) (expt 2 (p*))) (expt 2 (- (p*) (mu*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu*)
		  :use (pc-0-1
			add-upper
			add-lower
			(:instance rem-squeeze
				   (m (add*))
				   (n (expt 2 (p*)))
				   (r (expt 2 (- (p*) (mu*))))
				   (a 1))))))

(defthm rem-add-lower
    (implies (= (carry*) 1)
	     (<= 0 (rem (add*) (expt 2 (p*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p*)
		  :use (add-bnds
			(:instance rem>=0 (m (add*)) (n (expt 2 (p*))))))))

(defthm carry-1-rho-1
    (implies (= (carry*) 1)
	     (= (rho*)
		(rem (logior (expt 2 (1- (p*)))
			     (logand (add*) (mask*)))
		     (expt 2 (p*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho* sig-rewrite p*))))

(defthm carry-1-rho-2
    (implies (= (carry*) 1)
	     (= (rho*)
		(logior (expt 2 (1- (p*)))
			(rem (logand (add*) (mask*))
			     (expt 2 (p*))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* (:executable-counterpart expt))
		  :use (carry-1-rho-1
			mask-nat
			add-bnds
			(:instance or-dist-d
				   (x (expt 2 (1- (p*))))
				   (y (logand (add*) (mask*)))
				   (n (p*)))
			(:instance logand-nat (i (add*)) (j (mask*)))))))

(defthm carry-1-rho-3
    (implies (= (carry*) 1)
	     (= (rho*)
		(logior (expt 2 (1- (p*)))
			(logand (rem (add*) (expt 2 (p*)))
				(mask*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* (:executable-counterpart expt))
		  :use (carry-1-rho-2
			mask-nat
			add-bnds
			(:instance and-dist-c (x (add*)) (y (mask*)) (n (p*)))))))

(defthm carry-1-rho-4
    (implies (= (carry*) 1)
	     (= (rho*)
		(logior (expt 2 (1- (p*)))
			(logand (rem (add*) (expt 2 (p*)))
				(rem (mask*) (expt 2 (- (p*) (mu*))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* (:executable-counterpart expt))
		  :use (carry-1-rho-3
			pc-0-1
			mask-nat
			rem-add-upper
			rem-add-lower
			(:instance and-dist-d
				   (x (rem (add*) (expt 2 (p*))))
				   (y (mask*))
				   (n (- (p*) (mu*))))))))

(defthm carry-1-rho
    (implies (= (carry*) 1)
	     (= (rho*)
		(expt 2 (1- (p*)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p* mu* mask-rewrite (:executable-counterpart expt))
		  :use (carry-1-rho-4
			pc-0-1
			rem-add-lower
			(:instance bit-basic-a (x (rem (add*) (expt 2 (p*)))))))))

(defthm carry-1-near
    (implies (and (= (carry*) 1)
		  (eql (modep*) 'near))
	     (= (rnd (prod*) (modep*) (mu*))
		(expt 2 (p*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd p* mu* rconst-rewrite add-rewrite expo-prod
				     (:executable-counterpart expt))
		  :use (add-lower
			pc-0-1
			(:instance near-power-a (x (prod*)) (n (mu*)))))))

(defthm carry-1-inf
    (implies (and (= (carry*) 1)
		  (eql (modep*) 'inf))
	     (= (rnd (prod*) (modep*) (mu*)) (expt 2 (p*))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rnd p* mu* rconst-rewrite add-rewrite expo-prod
				     (:executable-counterpart expt))
		  :use (add-lower
			pc-0-1
			prod-nat
			(:instance fp+1
				   (x (- (expt 2 (p*)) (expt 2 (- (p*) (mu*)))))
				   (y (away (prod*) (mu*)))
				   (n (mu*)))
			(:instance expo-away (x (prod*)) (n (mu*)))
			(:instance expo-upper-bound (x (away (prod*) (mu*))))
			(:instance away-lower-pos (x (prod*)) (n (mu*)))
			(:instance away-exactp-b (x (prod*)) (n (mu*)))))))

(defthm carry-1-minf
    (implies (= (carry*) 1)
	     (not (or (eql (modep*) 'minf)
		      (eql (modep*) 'trunc))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rconst-rewrite add-rewrite expo-prod)
		  :use (sig-add-expo))))

(defthm carry-1
    (implies (= (carry*) 1)
	     (= (rho*)
		(* (rnd (prod*) (modep*) (mu*))
		   (expt 2  (- (carry*))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable modep* mu* mode* (:executable-counterpart expt) p*)
		  :use (carry-1-rho
			pc-0-1
			rc-vals
			carry-1-near
			carry-1-inf
			carry-1-minf))))

(defthm RHO-REWRITE
    (equal (rho*)
	   (* (rnd (prod*) (modep*) (mu*))
	      (expt 2  (- (carry*)))))
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt) p*)
		  :use (carry-1
			carry-0
			carry-0-1))))

(in-theory (disable rho-rewrite))

(defthm sig-z-rnd-1
    (= (sig (hat (z*)))
       (* (rnd (prod*) (modep*) (mu*))
	  (expt 2 (- (- (carry*)) (1- (p*))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho-rewrite p* (:executable-counterpart expt))
		  :use (sig-z
			carry-0-1))))

(defthm sig-z-rnd-2
    (= (sig (hat (z*)))
       (* (rnd (* (sig (* (hat (x*)) (hat (y*))))
		  (expt 2 (1- (p*))))
	       (modep*)
	       (mu*))
	  (expt 2 (- (- (carry*)) (1- (p*))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expo-prod sgn)
		  :use (sig-z-rnd-1
			rc-vals
			sig-xy
			prod-nat
			(:instance fp-rep (x (prod*)))))))

(defthm mode-ieee
    (ieee-mode-p (mode*))
  :hints (("Goal" :in-theory (enable ieee-mode-p mode*)
		  :use (rc-vals))))

(defthm modep-ieee
    (ieee-mode-p (modep*))
  :hints (("Goal" :in-theory (enable ieee-mode-p modep* mode*)
		  :use (rc-vals))))

(defthm sig-z-rnd
    (equal (sig (hat (z*)))
	   (* (rnd (sig (* (hat (x*)) (hat (y*)))) (modep*) (mu*))
	      (expt 2 (- (carry*)))))
  :hints (("Goal" :in-theory (enable p* mu* (:executable-counterpart expt))
		  :use (sig-z-rnd-2
			carry-0-1
			pc-0-1
			x-non-zero
			y-non-zero
			(:instance sig-lower-bound (x (* (hat (x*)) (hat (y*)))))
			(:instance rnd-shift
				   (x (sig (* (hat (x*)) (hat (y*)))))
				   (mode (modep*))
				   (n (mu*))
				   (k (1- (p*))))))))

(defthm k-0-1
    (repp (rnd (* (hat (x*)) (hat (y*)))
	       (mode*)
	       (mu*))
	  (extfmt))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mode* mu* input-spec)
		  :use (input-spec*))))

(defthm k-0-2
    (< (abs (- (expo (hat (z*)))
	       (expo (rnd (* (hat (x*)) (hat (y*)))
			  (mode*)
			  (mu*)))))
       (expt 2 15))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable repp hat extfmt (:executable-counterpart expt))
		  :use (k-0-1
			z-normal
			(:instance code-d (z (z*)) (phi (extfmt)))))))

(defthm sgn-rnd
    (implies (and (rationalp x)
		  (ieee-mode-p m)
		  (integerp n)
		  (> n 0))
	     (= (sgn (rnd x m n)) (sgn x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ieee-mode-p near rnd))))

(defthm rationalp-rnd
    (implies (ieee-mode-p m)
	     (rationalp (rnd x m n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable ieee-mode-p rnd))))

(defthm k-0-3
    (and (rationalp (rnd (* (hat (x*)) (hat (y*))) (mode*) (mu*)))
	 (not (= (rnd (* (hat (x*)) (hat (y*))) (mode*) (mu*)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn mu*)
		  :use (x-non-zero
			y-non-zero
			pc-0-1
			(:instance sgn-rnd
				   (x (* (hat (x*)) (hat (y*))))
				   (m (mode*))
				   (n (mu*)))
			(:instance rationalp-rnd
				   (x (* (hat (x*)) (hat (y*))))
				   (m (mode*))
				   (n (mu*)))))))

; slight change for v2-6:
(defthm rewrite-hack-2
    (equal (+ (* -1 (carry*))
	      (carry*)
	      (* 32768 (k*))
	      (expo (* (hat (x*)) (hat (y*)))))
	   (+ (expo (* (hat (x*)) (hat (y*))))
	      (* (k*) 32768))))

(defthm z-hat-rewrite-1
    (equal (hat (z*))
	   (* (sgn (* (hat (x*)) (hat (y*))))
	      (rnd (sig (* (hat (x*)) (hat (y*)))) (modep*) (mu*))
	      (expt 2 (+ (expo (* (hat (x*)) (hat (y*)))) (* (k*) (expt 2 15))))))
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt))
		  :use (expo-z
			sgn-z
			(:instance fp-rep (x (hat (z*))))))))

(defthm rewrite-hack-3
    (equal (expt 2 (+ (expo (* (hat (x*)) (hat (y*)))) (* (k*) (expt 2 15))))
	   (* (expt 2 (expo (* (hat (x*)) (hat (y*)))))
	      (expt 2 (* (k*) (expt 2 15)))))
  :hints (("Goal" :in-theory (disable a15)
		  :use (expo-z
			(:instance expo+
				   (m (expo (* (hat (x*)) (hat (y*)))))
				   (n (* (k*) (expt 2 15))))))))

(defthm z-hat-rewrite-2
    (equal (hat (z*))
	   (* (sgn (* (hat (x*)) (hat (y*))))
	      (rnd (* (sig (* (hat (x*)) (hat (y*))))
		      (expt 2 (expo (* (hat (x*)) (hat (y*))))))
		   (modep*)
		   (mu*))
	      (expt 2 (* (k*) (expt 2 15)))))
  :hints (("Goal" :in-theory (disable a15)
		  :use (mu-vals
			expo-z
			x-non-zero
			y-non-zero
			(:instance sig-lower-bound (x (* (hat (x*)) (hat (y*)))))
			(:instance rnd-shift
				   (x (sig (* (hat (x*)) (hat (y*)))))
				   (mode (modep*))
				   (k (expo (* (hat (x*)) (hat (y*)))))
				   (n (mu*)))))))

(defthm flip-modep
    (implies (< (* (hat (x*)) (hat (y*))) 0)
	     (equal (flip (modep*)) (mode*)))
  :hints (("Goal" :in-theory (enable sgn flip sgnz-rewrite modep*)
		  :use (sgn-hat
			sgn-z))))

(defthm modep-mode
    (implies (>= (* (hat (x*)) (hat (y*))) 0)
	     (equal (modep*) (mode*)))
  :hints (("Goal" :in-theory (enable sgn sgnz-rewrite modep*)
		  :use (x-non-zero
			y-non-zero
			sgn-hat
			sgn-z))))

(defthm rnd-flip-modep
    (equal (* (sgn (* (hat (x*)) (hat (y*))))
	      (rnd (* (sig (* (hat (x*)) (hat (y*))))
		      (expt 2 (expo (* (hat (x*)) (hat (y*))))))
		   (modep*)
		   (mu*)))
	   (rnd (* (sgn (* (hat (x*)) (hat (y*))))
		   (sig (* (hat (x*)) (hat (y*))))
		   (expt 2 (expo (* (hat (x*)) (hat (y*))))))
		(mode*)
		(mu*)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn mu*)
		  :use (pc-0-1
			x-non-zero
			y-non-zero
			(:instance rationalp-rnd
				   (x (* (sgn (* (hat (x*)) (hat (y*))))
					 (sig (* (hat (x*)) (hat (y*))))
					 (expt 2 (expo (* (hat (x*)) (hat (y*)))))))
				   (m (mode*))
				   (n (mu*)))
			(:instance rnd-flip
				   (x (* (sig (* (hat (x*)) (hat (y*))))
					 (expt 2 (expo (* (hat (x*)) (hat (y*)))))))
				   (m (modep*))
				   (n (mu*)))))))

(defthm z-hat-rewrite-3
    (equal (hat (z*))
	   (* (rnd (* (sgn (* (hat (x*)) (hat (y*))))
		      (sig (* (hat (x*)) (hat (y*))))
		      (expt 2 (+ (expo (* (hat (x*)) (hat (y*)))))))
		   (mode*)
		   (mu*))
	      (expt 2 (* (k*) (expt 2 15)))))
  :hints (("Goal" :use (rnd-flip-modep))))

(defthm z-hat-rewrite-4
    (equal (hat (z*))
	   (* (rnd (* (hat (x*)) (hat (y*)))
		   (mode*)
		   (mu*))
	      (expt 2 (* (k*) (expt 2 15)))))
  :hints (("Goal" :use ((:instance fp-rep (x (* (hat (x*)) (hat (y*)))))))))

(defthm k-0-4
    (= (- (expo (hat (z*)))
	  (expo (rnd (* (hat (x*)) (hat (y*)))
		     (mode*)
		     (mu*))))
       (* (k*) (expt 2 15)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt))
		  :use (k-0-3
			expo-z
			(:instance sig-expo-shift
				   (x (rnd (* (hat (x*)) (hat (y*))) (mode*) (mu*)))
				   (n (* (k*) (expt 2 15))))))))

(defthm k-0-5
    (< (abs (* (k*) (expt 2 15)))
       (expt 2 15))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt))
		  :use (k-0-2
			k-0-4))))

(defthm k-0
    (equal (k*) 0)
  :hints (("Goal" :in-theory (enable (:executable-counterpart expt))
		  :use (k-0-5
			expo-z))))

(defthm z*-spec
    (and (normal-encoding-p (z*) (extfmt))
	 (= (hat (z*))
            (rnd (* (hat (x*)) (hat (y*)))
		 (mode (rc*))
		 (precision (pc*)))))
  :rule-classes()
  :hints (("Goal" :in-theory (enable mode precision mode* mu* (:executable-counterpart expt))
		  :use (k-0-3
			z-normal))))

(defthm output-spec*
    (output-spec (x*) (y*) (rc*) (pc*))
  :hints (("Goal" :in-theory (enable output-spec)
		  :use (z*-spec fmul-star-equivalence))))

(defthm fmul-input-output
    (implies (input-spec x y rc pc)
	     (output-spec x y rc pc))
  :hints (("Goal" :in-theory (enable input-spec*)
		  :use ((:functional-instance
			 output-spec*
			 (x* (lambda () (if (input-spec x y rc pc) x (x*))))
			 (y* (lambda () (if (input-spec x y rc pc) y (y*))))
			 (rc* (lambda () (if (input-spec x y rc pc) rc (rc*))))
			 (pc* (lambda () (if (input-spec x y rc pc) pc (pc*))))))))
  :rule-classes ())

(defthm CORRECTNESS-OF-FMUL
    (let ((ideal (rnd (* (hat x) (hat y))
		      (mode rc)
		      (precision pc)))
	  (z (fmul x y rc pc)))
      (implies (and (normal-encoding-p x (extfmt))
		    (normal-encoding-p y (extfmt))
		    (member rc (list 0 1 2 3))
		    (member pc (list 0 1))
		    (repp ideal (extfmt)))
	       (and (normal-encoding-p z (extfmt))
		    (= (hat z) ideal))))
  :hints (("Goal" :in-theory (enable input-spec output-spec)
		  :use (fmul-input-output))))
