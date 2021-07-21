(in-package "RTL")

(include-book "prelim")

(defthm bitn-set-flag
  (implies (and (natp k)
                (natp b)
		(natp r))
           (equal (bitn (set-flag b r) k)
	          (if (= k b) 1 (bitn r k))))
  :hints (("Goal" :use ((:instance bitn-logior (x (expt 2 b)) (y r) (n k)))
                  :in-theory (enable bitn-expt bitn-expt-0 set-flag))))

(defthm natp-set-flag
  (implies (and (natp r) (natp b))
           (natp (set-flag b r)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm bvecp-expt-2
  (implies (and (natp n)
                (natp b)
		(< b n))
	   (bvecp (expt 2 b) n))
  :hints (("Goal" :in-theory (enable bvecp))))

(defthm bvecp-set-flag
  (implies (and (natp n)
                (bvecp r n)
		(natp b)
		(< b n))
	   (bvecp (set-flag b r) n))
   :hints (("Goal" :in-theory (enable set-flag))))

(in-theory (disable set-flag))

(defund opaz ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opa) (dp)))
      (zencode (sgnf (opa) (dp)) (dp))
     (opa)))
     
(defund opbz ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opb) (dp)))
      (zencode (sgnf (opb) (dp)) (dp))
     (opb)))

(defund rz ()
  (if (and (= (bitn (rin) (fz)) 1)
           (or (denormp (opa) (dp)) (denormp (opb) (dp))))
      (set-flag (idc) (rin))
    (rin)))

(in-theory (disable (opaz) (opbz) (rz)))

(defthm integerp-opa
  (integerp (opa))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm integerp-opb
  (integerp (opb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm natp-rin
  (natp (rin))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthmd bvecp-rin
  (bvecp (rin) 32)
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm natp-rz
  (natp (rz))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable rz))))

(defthmd member-classa
  (member (classa) '(0 1 2 3 4 5))
  :hints (("Goal" :in-theory (enable classa analyze))))

(defthmd member-classb
  (member (classb) '(0 1 2 3 4 5))
  :hints (("Goal" :in-theory (enable classb analyze))))

(defund specialp ()
  (or (member (classa) '(0 1 2 3))
      (member (classb) '(0 1 2 3))))

(in-theory (disable (specialp)))

(defthmd a-class
  (and (equal (zerp (opaz) (dp)) (= (classa) 0))
       (equal (infp (opaz) (dp)) (= (classa) 1))
       (equal (snanp (opaz) (dp)) (= (classa) 2))
       (equal (qnanp (opaz) (dp)) (= (classa) 3))
       (equal (normp (opaz) (dp)) (= (classa) 4))
       (equal (denormp (opaz) (dp)) (= (classa) 5)))
  :hints (("Goal" :in-theory (enable opaz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints unsupp sigf bitn-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opa)) (n 63))
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(defthmd b-class
  (and (equal (zerp (opbz) (dp)) (= (classb) 0))
       (equal (infp (opbz) (dp)) (= (classb) 1))
       (equal (snanp (opbz) (dp)) (= (classb) 2))
       (equal (qnanp (opbz) (dp)) (= (classb) 3))
       (equal (normp (opbz) (dp)) (= (classb) 4))
       (equal (denormp (opbz) (dp)) (= (classb) 5)))
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classb bits-bits
				     input-constraints unsupp sigf bitn-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthmd a-fields
  (and (equal (sgnf (opaz) (dp)) (signa))
       (equal (expf (opaz) (dp)) (expa))
       (implies (not (= (classa) 0)) (equal (manf (opaz) (dp)) (mana))))
  :hints (("Goal" :in-theory (enable opaz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints signa mana expa unsupp sigf bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opa)) (n 63))
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(defthm opaz-opa
  (implies (not (= (classa) 0))
           (equal (opaz) (opa)))
  :hints (("Goal" :in-theory (enable opaz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints signa mana expa unsupp sigf bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opa)) (n 63))
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(defthm opaz-63
  (equal (bitn (opaz) 63)
         (bitn (opa) 63))
  :hints (("Goal" :in-theory (enable opaz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints signa mana expa unsupp sigf bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opa)) (n 63))
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(defthm opbz-63
  (equal (bitn (opbz) 63)
         (bitn (opb) 63))
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints signa mana expa unsupp sigf bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthmd b-fields
  (and (equal (sgnf (opbz) (dp)) (signb))
       (equal (expf (opbz) (dp)) (expb))
       (implies (not (= (classb) 0)) (equal (manf (opbz) (dp)) (manb))))
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classb bits-bits
				     input-constraints signb manb expb unsupp sigf bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthm opbz-opb
  (implies (not (= (classb) 0))
           (equal (opbz) (opb)))
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classb bits-bits
				     input-constraints signb manb expb unsupp sigf bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthmd a-flags
  (equal (flags-a)
         (if (and (denormp (opa) (dp)) (not (= (fzp) 0))) 128 0))	     
  :hints (("Goal" :in-theory (enable si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints flags-a unsupp sigf bitn-bits)
                  :use (input-constraints-lemma
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(defthmd b-flags
  (equal (flags-b)
         (if (and (or (denormp (opa) (dp)) (denormp (opb) (dp)))
	          (not (= (fzp) 0)))
	     128 0))	     
  :hints (("Goal" :in-theory (enable si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints flags-b a-flags unsupp sigf bitn-bits)
                  :use (input-constraints-lemma
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthm no-traps
  (and (equal (bitn (rin) 15) 0)
       (equal (bitn (rin) 12) 0)
       (equal (bitn (rin) 11) 0)
       (equal (bitn (rin) 10) 0)
       (equal (bitn (rin) 9) 0)
       (equal (bitn (rin) 8) 0))
  :hints (("Goal" :use (input-constraints-lemma
                        (:instance bitn-bits (x (rin)) (i 12) (j 8) (k 4))
                        (:instance bitn-bits (x (rin)) (i 12) (j 8) (k 3))
                        (:instance bitn-bits (x (rin)) (i 12) (j 8) (k 2))
                        (:instance bitn-bits (x (rin)) (i 12) (j 8) (k 1))
                        (:instance bitn-bits (x (rin)) (i 12) (j 8) (k 0)))
                  :in-theory (e/d (input-constraints) (bitn-bits)))))

(defthm rz-flags-b
  (implies (natp k)
           (equal (bitn (rz) k)
	          (bitn (logior (rin) (flags-b)) k)))
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp 
                                     zerp infp nanp snanp qnanp normp denormp encodingp classb bits-bits
				     input-constraints rz b-flags bitn-logior signb manb expb unsupp sigf
				     bitn-bits bits-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-expt-0 (i 7) (n k))
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthmd arm-binary-spec-rewrite
  (equal (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
         (let ((d (arm-binary-pre-comp-val 'mul (opaz) (opbz) (rz) (dp)))
               (r (arm-binary-pre-comp-excp 'mul (opaz) (opbz) (rz) (dp))))
	   (if d (mv d r)
	       (arm-binary-comp 'mul (opaz) (opbz) r (dp)))))
  :hints (("Goal" :in-theory (enable dp hp opaz opbz rz))))

(in-theory (disable arm-binary-spec))

(defthm sign-0-1
  (and (member (signa) '(0 1))
       (member (signb) '(0 1)))
  :rule-classes ()
  :hints (("Goal" :use (a-fields b-fields input-constraints-lemma
                        (:instance bitn-0-1 (x (opaz)) (n (+ 11 52)))
                        (:instance bitn-0-1 (x (opbz)) (n (+ 11 52))))
		  :in-theory (enable sgnf expw sigw))))

(local-defthm special-1
  (implies (and (zerp a (dp))
                (or (zerp b (dp)) (normp b (dp)) (denormp b (dp))))
	   (equal (binary-eval 'mul (decode a (dp)) (decode b (dp)))
	          0))
  :hints (("Goal" :in-theory (enable binary-eval nrepp drepp zerp decode ddecode)
                  :use ((:instance nrepp-ndecode (x b))
		        (:instance drepp-ddecode (x b))))))

(local-defthm special-2
  (implies (and (qnanp a (dp)) (= n (expt 2 51)))
           (equal (logior n a) a))
  :hints (("Goal" :use ((:instance logior-2**n (n 51) (x a)))
                  :in-theory (enable dp formatp encodingp prec nanp qnanp))))

(local-defthm decode-zerp
  (implies (zerp x (dp))
           (equal (decode x (dp)) 0))
  :hints (("Goal" :in-theory (enable zerp expf sgnf sigf prec decode dp ddecode))))

(local-defthm specialp-3
  (implies (and (specialp) (= (fused) 0))
           (equal (mv-nth 0 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp))))
	          (data-special)))
  :hints (("Goal" :use (sign-0-1 input-constraints-lemma member-classa member-classb arm-binary-spec-rewrite a-class b-class
                        a-fields b-fields
			(:instance decode-zerp (x (opaz)))
			(:instance decode-zerp (x (opbz))))
	          :expand ((:free (a b) (binary-eval 'mul a b)))
                  :in-theory (enable input-constraints b-flags qnanize bitn-logior cat-0 zencode bitn-logxor sign binary-zero-sgn
		                     bvecp binary-eval sgnf binary-inf-sgn binary-undefined-p specialcase specialp data-special dnp
				     indef dp))))

(in-theory (disable ACL2::|(logior 1 x)|))

(local-defthm specialp-4
  (implies (and (specialp) (member k (nats 8)))
           (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))) k)
	          (bitn (logior (flags-special) (rin)) k)))
  :hints (("Goal" :use (sign-0-1 input-constraints-lemma member-classa member-classb arm-binary-spec-rewrite a-class b-class
                        a-fields b-fields
			(:instance decode-zerp (x (opaz)))
			(:instance decode-zerp (x (opbz))))
	          :expand ((:free (a b) (binary-eval 'mul a b)))
                  :in-theory (enable input-constraints b-flags qnanize bitn-logior cat-0 zencode bitn-logxor sign binary-zero-sgn
		                     bvecp binary-eval sgnf binary-inf-sgn binary-undefined-p specialcase specialp data-special dnp
				     flags-special indef dp))))

(local-defthm specialp-5
  (implies (and (specialp) (natp k) (>= k 8))
           (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))) k)
	          (bitn (rin) k)))
  :hints (("Goal" :use (arm-binary-spec-rewrite)
		  :in-theory (enable rz cat-0 bitn-logxor bitn-logior))))

(local-defthmd specialp-6
  (implies (specialp)
           (bvecp (flags-special) 8))
  :hints (("Goal" :in-theory (enable rz b-flags specialcase flags-special bitn-logior))))

(local-defthm specialp-7
  (implies (and (specialp) (natp k) (>= k 8))
           (equal (bitn (flags-special) k) 0))
  :hints (("Goal" :use (specialp-6) :in-theory (enable bvecp-monotone))))

(local-defthmd specialp-8
  (implies (and (specialp) (natp k))
           (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))) k)
	          (bitn (logior (flags-special) (rin)) k)))
  :hints (("Goal" :use (specialp-4 specialp-5 specialp-7)
		  :in-theory (e/d (bitn-logior) (specialp-4 specialp-5 specialp-7)))))

(local-defthmd specialp-9
  (implies (specialp)
           (integerp (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp))))))
  :hints (("Goal" :use (arm-binary-spec-rewrite))))

(local-defthm specialp-10
  (implies (specialp)
           (equal (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp))))
	          (logior (flags-special) (rin))))
  :hints (("Goal" :use (specialp-9
                        arm-binary-spec-rewrite(:instance specialp-8
                                   (k (bit-diff (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp))))
				                (logior (flags-special) (rin)))))
                        (:instance bit-diff-diff
			           (x (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))))
				   (y (logior (flags-special) (rin))))))))

(defthm specialp-main
  (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
    (implies (and (= (fused) 0) (specialp))
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (specialp-3 specialp-10)
           :in-theory (enable specialp flags data))))

(defthm fscale-1
  (implies (= (fscale) 1)
           (equal (opb) #x3ff0000000000000))
  :hints (("Goal" :in-theory (enable input-constraints) :use (input-constraints-lemma))))

(defthm fscale-2
  (implies (= (fscale) 1)
           (equal (opbz) #x3ff0000000000000))
  :hints (("Goal" :in-theory (enable dp opbz input-constraints) :use (input-constraints-lemma))))

(defthm fscale-3
  (implies (= (fscale) 1)
           (equal (classb) 4))
  :hints (("Goal" :in-theory (enable dp analyze classb))))
  
(in-theory (disable arm-fscale-comp))

(defthmd arm-fscale-spec-rewrite
  (implies (= (fscale) 1)
           (equal (arm-fscale-spec (opa) (scale) (rin) (dp))
                  (let ((d (if (nanp (opaz) (dp)) (process-nan (opaz) (rz) (dp)) ()))
                        (r (if (snanp (opaz) (dp)) (set-flag (ioc) (rz)) (rz))))
                    (if d (mv d r)
	                (arm-fscale-comp (opaz) (scale) r (dp))))))
  :hints (("Goal" :in-theory (enable dp opaz rz))))

(in-theory (disable arm-fscale-spec))

(in-theory (disable fscale-1 fscale-2))

(local-defthm fscale-4
  (implies (zerp (opaz) (dp))
           (= (opaz) (* (expt 2 63) (signa))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable zerp encodingp dp expw sigw sgnf expf sigf)
                  :use (a-fields
		        (:instance bitn-plus-bits (x (opaz)) (n 63) (m 0))
		        (:instance bits-plus-bits (x (opaz)) (n 62) (p 52) (m 0))))))

(local-defthm fscale-5
  (implies (infp (opaz) (dp))
           (= (opaz)
	      (+ (* (expt 2 63) (signa))
	            #x7ff0000000000000)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable infp manf encodingp dp expw sigw sgnf expf sigf)
                  :use (a-fields
		        (:instance bitn-plus-bits (x (opaz)) (n 63) (m 0))
		        (:instance bits-plus-bits (x (opaz)) (n 62) (p 52) (m 0))))))

(local-defthm fscale-6
  (implies (and (specialp) (= (fscale) 1))
           (equal (mv-nth 0 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp))))
	          (data-special)))
  :hints (("Goal" :use (sign-0-1 input-constraints-lemma member-classa member-classb arm-fscale-spec-rewrite a-class b-class
                        a-fields b-fields fscale-4 fscale-5 a-fields
			(:instance decode-zerp (x (opaz))))
                  :in-theory (enable input-constraints b-flags qnanize bitn-logior cat-0 zencode bitn-logxor sign binary-zero-sgn
		                     opaz snanp qnanp arm-fscale-comp bvecp sgnf specialcase specialp data-special dnp dp))))

(local-defthm fscale-7
  (implies (and (specialp) (= (fscale) 1) (member k (nats 8)))
           (equal (bitn (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))) k)
	          (bitn (logior (flags-special) (rin)) k)))
  :hints (("Goal" :use (sign-0-1 input-constraints-lemma member-classa member-classb arm-fscale-spec-rewrite a-class b-class
                        a-fields b-fields fscale-4 fscale-5 a-fields
			(:instance decode-zerp (x (opaz))))
                  :in-theory (enable input-constraints b-flags qnanize bitn-logior cat-0 zencode bitn-logxor sign binary-zero-sgn
		                     flags-special opaz snanp qnanp arm-fscale-comp bvecp sgnf specialcase specialp data-special
				     dnp dp))))

(local-defthm fscale-8
  (implies (and (specialp) (= (fscale) 1) (natp k) (>= k 8))
           (equal (bitn (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))) k)
	          (bitn (rin) k)))
  :hints (("Goal" :use (arm-fscale-spec-rewrite)
		  :in-theory (enable arm-fscale-comp snanp rz cat-0 bitn-logxor bitn-logior))))

(local-defthmd fscale-9
  (implies (and (specialp) (= (fscale) 1) (natp k))
           (equal (bitn (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))) k)
	          (bitn (logior (flags-special) (rin)) k)))
  :hints (("Goal" :use (fscale-7 fscale-8 specialp-7)
		  :in-theory (e/d (bitn-logior) (specialp-7)))))

(local-defthmd fscale-10
  (implies (and (specialp) (= (fscale) 1))
           (integerp (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp))))))
  :hints (("Goal" :in-theory (enable arm-fscale-comp) :use (arm-fscale-spec-rewrite))))

(local-defthm fscale-11
  (implies (and (specialp) (= (fscale) 1))
           (equal (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp))))
	          (logior (flags-special) (rin))))
  :hints (("Goal" :use (fscale-10
                        arm-binary-spec-rewrite
			(:instance fscale-9
                                   (k (bit-diff (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp))))
				                (logior (flags-special) (rin)))))
                        (:instance bit-diff-diff
			           (x (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))))
				   (y (logior (flags-special) (rin))))))))

(defthm specialp-fscale
  (mv-let (data-spec r-spec) (arm-fscale-spec (opa) (scale) (rin) (dp))
    (implies (and (= (fscale) 1) (specialp))
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (fscale-6 fscale-11)
           :in-theory (enable specialp flags data))))

(local-defthmd denormp-a-class
  (implies (denormp (opa) (dp))
           (equal (classa)
                  (if1 (fzp) 0 5)))
  :hints (("Goal" :in-theory (enable opaz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints unsupp sigf bitn-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opa)) (n 63))
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(local-defthmd denormp-b-class
  (implies (denormp (opb) (dp))
           (equal (classb)
                  (if1 (fzp) 0 5)))
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classb bits-bits
				     input-constraints unsupp sigf bitn-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(local-defthm zerp-a-class
  (implies (= (classa) 0)
           (if (or (= (fzp) 0) (zerp (opa) (dp)) (infp (opa) (dp)) (nanp (opa) (dp)) (normp (opa) (dp)))
               (equal (opaz) (opa))
	     (denormp (opa) (dp))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable opaz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classa bits-bits
				     input-constraints unsupp sigf bitn-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opa)) (n 63))
		        (:instance logand-bit (x (manf (opa) (dp))) (n 51))
		        (:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(local-defthm zerp-b-class
  (implies (= (classb) 0)
           (if (or (= (fzp) 0) (zerp (opb) (dp)) (infp (opb) (dp)) (nanp (opb) (dp)) (normp (opb) (dp)))
               (equal (opbz) (opb))
	     (denormp (opb) (dp))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable opbz si signb analyze sgnf expf manf expw sigw dp
                                     zerp infp nanp snanp qnanp normp denormp encodingp classb bits-bits
				     input-constraints unsupp sigf bitn-bits fzp zencode)
                  :use (input-constraints-lemma
		        (:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance logand-bit (x (manf (opb) (dp))) (n 51))
		        (:instance bits-bounds (x (opb)) (i 62) (j 52))))))

(defthmd specialp-fused
  (implies (and (= (fused) 1) (specialp))
           (fmul64-fused-spec (opa) (opb) (fzp) (dnp) (data) (flags) (prodinfzero) (infnanzero) (expovfl)))
  :hints (("Goal" :use (sign-0-1 input-constraints-lemma member-classa member-classb a-class b-class
                        a-fields b-fields denormp-a-class denormp-b-class zerp-a-class zerp-b-class
			(:instance decode-zerp (x (opaz))) (:instance bitn-0-1 (x (rin)) (n 25))
			(:instance decode-zerp (x (opbz))))
                  :in-theory (enable input-constraints b-flags qnanize bitn-logior cat-0 zencode bitn-logxor sign binary-zero-sgn
		                     bvecp sgnf binary-inf-sgn binary-undefined-p specialcase specialp data-special dnp
				     data infnanzero-special infnanzero prodinfzero-special prodinfzero flags
                                     expovfl expovfl-special fzp qnanp snanp ash flags-special indef dp))))
