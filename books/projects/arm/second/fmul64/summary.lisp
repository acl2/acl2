(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "fmul64")

(local (include-book "fused"))

;; Three operations are performed by fmul64: FMUL, FSCALE, and a multiplication in
;; support of FMA.  These are distinguished by two boolean arguments, fscale and fused.
;; For FMUL and FMA, opa and opb are the operands and scale is ignored.  For FSCALE,
;; opa and scale are the operands and opb is forced to #x3FF0000000000000 (the DP
;; encoding of 1).

;; We impose the following constraints on the arguments of fmul64:

(defund input-constraints (opa opb scale rin fused fscale)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (bvecp scale 64)
       (bvecp rin 32)
       (bitp fused)
       (bitp fscale)
       (not (and (= fused 1) (= fscale 1)))
       (implies (= fscale 1) (equal opb #x3FF0000000000000))
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; With regard to FMUL, our ultimate objective is the following theorem:

;; (defthm fmul64-fmul-correct
;;   (implies (input-constraints opa opb scale rin 0 0)
;;            (let ((dnp (bitn rin 25))
;;                  (fzp (bitn rin 24))
;;                  (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (fmul64 opa opb scale fzp dnp rmode 0 0)
;;                (let ((r (logior rin flags)))         
;;                  (mv-let (data-spec r-spec)
;;                          (arm-binary-spec 'mul opa opb rin (dp))
;;                    (and (equal data data-spec)
;;                         (equal r r-spec)))))))
;;   :rule-classes ())

;; For FSCALE, we define a separate specification predicate, arm-fscale-spec,
;; and prove this:

;; (defthm fmul64-fscale-correct
;;   (implies (input-constraints opa opb scale rin 0 1)
;;            (let ((dnp (bitn rin 25))
;;                  (fzp (bitn rin 24))
;;                  (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (fmul64 opa opb scale fzp dnp rmode 0 1)
;;                (let ((r (logior rin flags)))         
;;                  (mv-let (data-spec r-spec)
;;                          (arm-fscale-spec opa scale rin (dp))
;;                    (and (equal data data-spec)
;;                         (equal r r-spec)))))))
;;   :rule-classes ())
  
;; For the multiplication in support of FMA, there is no architectural specification,
;; so we define a separate specification predicate, fmul64-fused-spec as follows.

;; IEEE rounding modes:

(defun rmodenear () 0)
(defun rmodeup () 1)
(defun rmodedn () 2)
(defun rmodezero () 3)

;; An operand is forced to 0:

(defun fzerp (x fz)
  (and (= fz 1) (denormp x (dp))))

;; The special case of a NaN, zero, or infinity operand is handled separately:

(defun fmul64-fused-special-p (a b fz)
  (or (nanp a (dp)) (nanp b (dp))
      (zerp a (dp)) (zerp b (dp))
      (fzerp a fz) (fzerp b fz)
      (infp a (dp)) (infp b (dp))))

;; Product of zero and infinity:

(defun inf-times-zero (a b fz)
  (or (and (infp a (dp))
           (or (zerp b (dp)) (fzerp b fz)))
      (and (infp b (dp))
           (or (zerp a (dp)) (fzerp a fz)))))

;; The special case data result:
      
(defun fmul64-fused-spec-special-val (a b fz dn)
  (cond ((inf-times-zero a b fz)
         (indef (dp)))
	((and (= dn 1) (or (nanp a (dp)) (nanp b (dp))))
         (indef (dp)))
        ((snanp a (dp))
         a)
        ((snanp b (dp))
         b)
        ((qnanp a (dp))
         a)
        ((qnanp b (dp))
         b)
        ((or (infp a (dp)) (infp b (dp)))
         (iencode (logxor (sgnf a (dp)) (sgnf b (dp))) (dp)))
        (t
         (zencode (logxor (sgnf a (dp)) (sgnf b (dp))) (dp)))))

(defun fmul64-fused-special (a b fz dn data flags prodinfzero infnanzero expovfl)
  (and (= prodinfzero
          (if (inf-times-zero a b fz) 1 0))
       (= infnanzero 1)
       (bvecp flags 8)
       (= (bitn flags 1) 0)
       (= (bitn flags 3) 0)
       (= (bitn flags 2) 0)
       (= (bitn flags 4) 0)
       (= (bitn flags 5) 0)
       (= (bitn flags 6) 0)
       (= (bitn flags 7)
          (if (or (fzerp a fz) (fzerp b fz)) 1 0))
       (= (bitn flags 0)
          (if (or (snanp a (dp)) (snanp b (dp)) (inf-times-zero a b fz)) 1 0))
       (= expovfl 0)
       (bvecp data 117)
       (= data (ash (fmul64-fused-spec-special-val a b fz dn) 53))))

;; Note that in the case of a subnormal product, the specification does not compute 
;; a specific value, but rather constrains it:

(defun fmul64-fused-comp (a b data flags prodinfzero infnanzero expovfl)
  (let ((prod (* (decode a (dp)) (decode b (dp)))))
    (and (= prodinfzero 0)
         (= infnanzero 0)
         (bvecp flags 8)
         (= (bitn flags 1) 0)
         (= (bitn flags 3) 0)
         (= (bitn flags 2) 0)
         (= (bitn flags 7) 0)
         (= (bitn flags 0) 0)
         (= (bitn flags 5) 0)
         (= (bitn flags 6) 0)
         (= (bitn data 116) (if (< prod 0) 1 0))
	 (bitp expovfl)
	 (bvecp data 117)
         (cond ((= expovfl 1)
                (and (>= (abs prod) (expt 2 (1+ (expt 2 10))))
	   	     (= (bitn flags 4) 0)))
               ((> (bits data 115 105) 0)
                (and (equal (abs prod)
	                    (* (expt 2 (- (bits data 115 105) (1- (expt 2 10))))
		               (1+ (* (expt 2 -105) (bits data 104 0)))))
	  	     (equal (bitn flags 4) 0)))
               (t
                (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		            (bits data 104 52))
		         (abs prod))
	   	     (< (abs prod)
		        (* (expt 2 (- -52 (1- (expt 2 10))))
		           (1+ (bits data 104 52))))
		     (iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
		                (bits data 104 52))
		             (abs prod))
	                  (and (equal (bits data 51 0) 0)
	                       (equal (bitn flags 4) 0)))))))))

(defun fmul64-fused-spec (a b fz dn data flags prodinfzero infnanzero expovfl)
  (if (fmul64-fused-special-p a b fz)
      (fmul64-fused-special a b fz dn data flags prodinfzero infnanzero expovfl)
    (fmul64-fused-comp a b data flags prodinfzero infnanzero expovfl)))

;; With regard to FMA, our ultimate objective is the following theorem:

;; (defthm fmul64-fused-correct
;;   (implies (input-constraints opa opb scale rin 1 0)
;;            (let ((dnp (bitn rin 25))
;;                  (fzp (bitn rin 24))
;;                  (rmode (bits rin 23 22)))
;;              (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb scale fzp dnp rmode 1 0)
;;                (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
;;   :rule-classes ())


;; In order to address the lack of modularity of the ACL2 code, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate (((opa) => *) ((opb) => *) ((scale) => *) ((rin) => *) ((fused) => *) ((fscale) => *))
  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun scale () 0))
  (local (defun rin () 0))
  (local (defun fused () 0))
  (local (defun fscale () 0))
  (defthm input-constraints-lemma
    (input-constraints (opa) (opb) (scale) (rin) (fused) (fscale))
    :rule-classes ()))

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))

;; In terms of these constants, we shall define constants corresponding to the local 
;; variables of fmul64, culminating in the constants (data) and (flags), corresponding to
;; the outputs.

;; The constant definitions will be derived from that of fmul64 in such a way that 
;; the proof of the following will be trivial:

;; (defthmd fmul64-lemma
;;   (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) (fzp) (dnp) (rmode) (fused))
;;     (and (equal (data) data)
;;          (equal (flags) flags)
;;   	    (equal (prodinfzero) prodinfzero)
;; 	    (equal (infnanzero) infnanzero)
;; 	    (equal (expovfl) expovfl))))

;; For FMUL, the real work will be the proof of the following theorem:

;; (defthm fmul64-main
;;   (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
;;     (implies (and (= (fused) 0)
;;                   (= (fscale) 0))
;;              (and (equal (data) data-spec)
;;                   (equal (logior (rin) (flags)) r-spec)))))

;; The following is an immediate consequence of the preceding results:

;; (defthmd fmul64-lemma-to-be-functionally-instantiated
;;   (let ((dnp (bitn (rin) 25))
;;         (fzp (bitn (rin) 24))
;;         (rmode (bits (rin) 23 22)))
;;     (mv-let (data flags) (fmul64 (opa) (opb) (scale) fzp dnp rmode 0 0)
;;       (mv-let (data-spec r-spec)
;;               (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
;; 	(implies (and (= (fused) 0)
;; 	              (= (fscale) 0))
;;                  (and (equal data data-spec)
;;                       (equal (logior (rin) flags) r-spec)))))))

;; The desired theorem, fmul64-fmul-correct, can then be derived by functional instantiation.
;; The correctness theorems for FSCALE and FMA are proved similarly.

;;*******************************************************************************
;; fmul64
;;*******************************************************************************

;; Here we define the constants corresponding to the local variables of fmul64.

;; Opeerand components and data classes, returned by analyze:

(defund signa () (mv-nth 0 (mv-list 5 (analyze (opa) 3 (fzp) (bits 0 7 0)))))
(defund expa () (mv-nth 1 (mv-list 5 (analyze (opa) 3 (fzp) (bits 0 7 0)))))
(defund mana () (mv-nth 2 (mv-list 5 (analyze (opa) 3 (fzp) (bits 0 7 0)))))
(defund classa () (mv-nth 3 (mv-list 5 (analyze (opa) 3 (fzp) (bits 0 7 0)))))
(defund flags-a () (mv-nth 4 (mv-list 5 (analyze (opa) 3 (fzp) (bits 0 7 0)))))
(defund signb () (mv-nth 0 (mv-list 5 (analyze (opb) 3 (fzp) (flags-a)))))
(defund expb () (mv-nth 1 (mv-list 5 (analyze (opb) 3 (fzp) (flags-a)))))
(defund manb () (mv-nth 2 (mv-list 5 (analyze (opb) 3 (fzp) (flags-a)))))
(defund classb () (mv-nth 3 (mv-list 5 (analyze (opb) 3 (fzp) (flags-a)))))
(defund flags-b () (mv-nth 4 (mv-list 5 (analyze (opb) 3 (fzp) (flags-a)))))

;; Special case outputs:

(defund data-special ()
  (mv-nth 0 (mv-list 5 (specialcase (opa) (opb) (classa) (classb) (dnp) (fused) (flags-b)))))
(defund flags-special ()
  (mv-nth 1 (mv-list 5 (specialcase (opa) (opb) (classa) (classb) (dnp) (fused) (flags-b)))))
(defund prodinfzero-special ()
  (mv-nth 2 (mv-list 5 (specialcase (opa) (opb) (classa) (classb) (dnp) (fused) (flags-b)))))
(defund infnanzero-special ()
  (mv-nth 3 (mv-list 5 (specialcase (opa) (opb) (classa) (classb) (dnp) (fused) (flags-b)))))
(defund expovfl-special ()
  (mv-nth 4 (mv-list 5 (specialcase (opa) (opb) (classa) (classb) (dnp) (fused) (flags-b)))))

;; Leading zero count (assuming that expa and expb are not both 0):

(defund lzc ()
  (let* ((lzc (bits 0 5 0))
         (lzc (if1 (log= (expa) 0)
                   (logior lzc (clz53 (mana)))
                   lzc)))
    (if1 (log= (expb) 0)
         (logior lzc (clz53 (manb)))
         lzc)))

;; Multiplier output:

(defund prod ()
  (computeproduct (mana) (manb) (log= (expa) 0) (log= (expb) 0)))

;; Huge values of scale operand:

(defund hugeposscale ()
  (logand1 (fscale) (log>= (si (scale) 64) 4096)))

(defund hugenegscale ()
  (logand1 (fscale) (log< (si (scale) 64) (- 4096))))

;; Biased exponent of the product:

(defund expbunbiased ()
  (bits (if1 (fscale)
             (si (scale) 64)
             (if1 (log= (expb) 0)
                  (- 1022)
                  (- (expb) 1023)))
        13 0))

(defund expabiased ()
  (bits (if1 (log= (expa) 0) 1 (expa)) 13 0))

(defund expbiased ()
  (bits (+ (si (expabiased) 14)
           (si (expbunbiased) 14))
        13 0))

;; Exponent after shifting:

(defund expshft ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 0 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 0 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

;; Indication of exponent increment:

(defund expinc ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 1 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 1 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

;; FMA outputs:

(defund frac105 ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 2 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 2 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

(defund stkshft ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 3 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 3 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

(defund expzero () (log= (expshft) 0))

(defund expmax () (log= (expshft) 2046))

(defund expinf () (log= (expshft) 2047))

(defund expgtinf () (logior1 (log> (expshft) 2047) (hugeposscale)))

(defund exp11 () (bits (expshft) 10 0))

(defund sign () (logxor (signa) (signb)))

(defund data-fma ()
  (let ((d (setbitn 0 117 116 (sign))))
    (setbits (if1 (logand1 (expinc) (lognot1 (expinf)))
                  (setbits d 117 115 105 (+ (exp11) 1))
                  (setbits d 117 115 105 (exp11)))
             117 104 0 (frac105))))

(defund flags-fma ()
  (setbitn (flags-b) 8 4 (stkshft)))
       
(defund prodinfzero-fma () (false$))

(defund infnanzero-fma () (false$))

(defund expovfl-fma () (logior1 (expgtinf) (logand1 (expinf) (expinc))))


;; Rounded result and FMUL outputs:

(defund lsb ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 4 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 4 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

(defund grd ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 5 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 5 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

(defund stk ()
  (if1 (logior1 (log<= (si (expbiased) 14) 0)
                (hugenegscale))
       (mv-nth 6 (mv-list 7 (rightshft (expbiased) (hugenegscale) (prod))))
       (mv-nth 6 (mv-list 7 (leftshft (expbiased) (prod) (lzc))))))

(defund rndup ()
  (logior1 (logior1 (logand1 (logand1 (log= (rmode) (rmodenear)) (grd))
                             (logior1 (lsb) (stk)))
                    (logand1 (logand1 (log= (rmode) (rmodeup))
                                      (lognot1 (sign)))
                             (logior1 (grd) (stk))))
           (logand1 (logand1 (log= (rmode) (rmodedn)) (sign))
                    (logior1 (grd) (stk)))))

(defund fracunrnd () (bits (frac105) 104 53))

(defund fracp1 () (bits (+ (fracunrnd) 1) 52 0))

(defund fracrnd ()
  (bits (if1 (rndup)
             (bits (fracp1) 51 0)
	     (fracunrnd))
        51 0))

(defund exprndinc () (logand1 (rndup) (bitn (fracp1) 52)))

(defund exprnd ()
  (bits (if1 (logior1 (expinc) (exprndinc))
             (+ (exp11) 1)
             (exp11))
        10 0))

(defund underflow () (logand1 (expzero) (lognot1 (expinc))))

(defund overflow ()
  (logior1 (logior1 (expinf) (expgtinf))
           (logand1 (expmax) (logior1 (expinc) (exprndinc)))))

(defund data-fmul ()
  (let ((d (setbitn (bits 0 63 0) 64 63 (sign))))
    (if1 (overflow)
         (if1 (logior1 (logior1 (logand1 (log= (rmode) (rmodeup)) (sign))
                                (logand1 (log= (rmode) (rmodedn))
                                         (lognot1 (sign))))
                       (log= (rmode) (rmodezero)))
              (setbits d 64 62 0 9218868437227405311)
              (setbits d 64 62 0 9218868437227405312))
	 (if1 (underflow)
	      (if1 (fzp)
	           d
		   (setbits (setbits d 64 51 0 (fracrnd)) 64 62 52 (exprnd)))
	      (setbits (setbits d 64 51 0 (fracrnd)) 64 62 52 (exprnd))))))

(defund flags-fmul ()
  (if1 (overflow)
       (setbitn (setbitn (flags-b) 8 4 1) 8 2 1)
       (if1 (underflow)
	    (if1 (fzp)
	         (setbitn (flags-b) 8 3 1)
	         (if1 (logior1 (grd) (stk))
                      (let ((flags (setbitn (flags-b) 8 3 1)))
                        (setbitn flags 8 4 1))
                      (flags-b)))
            (if1 (logior1 (grd) (stk))
                 (setbitn (flags-b) 8 4 1)
                 (flags-b)))))

;; Final outputs:

(defund data ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
           (log= (classb) 3))
       (data-special)
       (if1 (fused)
            (data-fma)
            (data-fmul))))

(defund flags ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
           (log= (classb) 3))
       (flags-special)
       (if1 (fused)
            (flags-fma)
            (flags-fmul))))

(defund prodinfzero ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
           (log= (classb) 3))
       (prodinfzero-special)
       (false$)))

(defund infnanzero ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
           (log= (classb) 3))
       (infnanzero-special)
       (false$)))

(defund expovfl ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
           (log= (classb) 3))
       (expovfl-special)
       (if1 (fused)
            (logior1 (expgtinf) (logand1 (expinf) (expinc)))
            (false$))))
                                          
;; The lemma mentioned earlier:
                                          
(defthmd fmul64-lemma
  (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) (scale) (fzp) (dnp) (rmode) (fused) (fscale))
    (and (equal (data) data)
         (equal (flags) flags)
	 (equal (prodinfzero) prodinfzero)
	 (equal (infnanzero) infnanzero)
	 (equal (expovfl) expovfl))))


;;*******************************************************************************
;; Special Cases
;;*******************************************************************************

;; Zero, infinity, or NaN operand:

(defund specialp ()
  (or (member (classa) '(0 1 2 3))
      (member (classb) '(0 1 2 3))))

;; Operands after possible coercion to 0:

(defund opaz ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opa) (dp)))
      (zencode (sgnf (opa) (dp)) (dp))
     (opa)))
     
(defund opbz ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opb) (dp)))
      (zencode (sgnf (opb) (dp)) (dp))
    (opb)))

;; Main theorems for special cases:

(defthm specialp-main
  (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
    (implies (and (= (fused) 0) (specialp))
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec)))))
		  
(defthm specialp-fscale
  (mv-let (data-spec r-spec) (arm-fscale-spec (opa) (scale) (rin) (dp))
    (implies (and (= (fscale) 1) (specialp))
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec)))))
		  
(defthmd specialp-fused
  (implies (and (= (fused) 1) (specialp))
           (fmul64-fused-spec (opa) (opb) (fzp) (dnp) (data) (flags) (prodinfzero) (infnanzero) (expovfl))))


;;*******************************************************************************
;; Multiplier
;;*******************************************************************************

;; Significands:

(defund sa ()
  (if (= (expa) 0)
      (mana)
    (+ (expt 2 52) (mana))))

(defund sb ()
  (if (= (expb) 0)
      (manb)
    (+ (expt 2 52) (manb))))

(defthmd prod-rewrite
  (implies (not (specialp))
           (equal (prod) (* (sa) (sb)))))

;; Numerical values of operands:
 
(defund ea ()
  (if (= (expa) 0)
      (- 1 (1- (expt 2 10)))
    (- (expa) (1- (expt 2 10)))))

(defund eb ()
  (if (= (fscale) 1)
      (si (scale) 64)
    (if (= (expb) 0)
        (- 1 (1- (expt 2 10)))
      (- (expb) (1- (expt 2 10))))))

(defund a () (decode (opaz) (dp)))

(defund b () (if1 (fscale) (expt 2 (si (scale) 64)) (decode (opbz) (dp))))

(defthmd a-val
  (implies (not (specialp))
           (equal (abs (a))
                  (* (expt 2 (- (ea) 52))
                     (sa)))))

(defthmd b-val
  (implies (not (specialp))
           (equal (abs (b))
                  (* (expt 2 (- (eb) 52))
                     (sb)))))

(defthmd abs-prod
  (implies (not (specialp))
           (equal (abs (* (a) (b)))
	          (* (expt 2 (+ (ea) (eb) -104))
		     (prod)))))


;;*******************************************************************************
;; Unrounded Product and FMA
;;*******************************************************************************

;; Unbiased exponent of unrounded result:

(defund eab ()
  (+ (expshft) (expinc) -1023))

;; Normal case:

(defthmd unround-a
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkshft) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105))))))))

;; Denormal case:

(defthm unround-b
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
		(= (+ (eab) (1- (expt 2 10))) 0))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (frac105) 104 52))
		    (abs (* (a) (b))))
		(< (abs (* (a) (b)))
		   (* (expt 2 (- -52 (1- (expt 2 10))))
		      (1+ (bits (frac105) 104 52))))
		(iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
		           (bits (frac105) 104 52))
		        (abs (* (a) (b))))
	             (and (equal (bits (frac105) 51 0)
		            0)
	                  (equal (stkshft)
		                 0)))))
  :rule-classes ())

;; FMA theorem:

(defthmd fmul64-fused-main
  (implies (= (fused) 1)
           (fmul64-fused-spec (opa) (opb) (fzp) (dnp) (data) (flags)
                             (prodinfzero) (infnanzero) (expovfl))))

(defthmd fmul64-fused-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) (scale) fzp dnp rmode 1 0)
	(implies (= (fused) 1)
                 (fmul64-fused-spec (opa) (opb) fzp dnp data flags prodinfzero infnanzero expovfl)))))

(defthm fmul64-fused-correct
  (implies (input-constraints opa opb scale rin 1 0)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb scale fzp dnp rmode 1 0)
               (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
  :rule-classes ())


;;*******************************************************************************
;; Rounded Product and FMUL
;;*******************************************************************************

;; Rounding mode:

(defund mode ()
  (case (rmode)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

;; Normal case:

(defthmd norm-rnd
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (* (a) (b)) (mode) 53)
	          (if (= (sign) 1)
		      (- (* (expt 2 (+ (eab) -52 (exprndinc)))
		            (+ (expt 2 52) (fracrnd))))
	            (* (expt 2 (+ (eab) -52 (exprndinc)))
		       (+ (expt 2 52) (fracrnd)))))))

(defthmd norm-exact
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (rnd (* (a) (b)) (mode) 53)
	           (* (a) (b)))
	        (and (= (stk) 0) (= (grd) 0)))))

;; Denormal case:

(defthmd denorm-drnd-rndup
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (exprndinc) 1))
           (equal (drnd (* (a) (b)) (mode) (dp))
	          (if (< (* (a) (b)) 0)
		      (- (* (expt 2 (- 2 (expt 2 10)))
                            (1+ (* (expt 2 -52) (fracrnd)))))
	            (* (expt 2 (- 2 (expt 2 10)))
                       (1+ (* (expt 2 -52) (fracrnd))))))))

(defthmd denorm-drnd-no-rndup
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (exprndinc) 0))
           (equal (drnd (* (a) (b)) (mode) (dp))
	          (if (< (* (a) (b)) 0)
		      (- (* (expt 2 (- -50 (expt 2 10)))
                            (fracrnd)))
	            (* (expt 2 (- -50 (expt 2 10)))
                       (fracrnd))))))

(defthmd drnd-equal
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (drnd (* (a) (b)) (mode) (dp))
		   (* (a) (b)))
	        (and (= (stk) 0) (= (grd) 0)))))

;; FMUL theorem:

(defthm fmul64-fmul-main
  (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
    (implies (and (= (fused) 0)
                  (= (fscale) 0))
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec)))))

(defthmd fmul64-fmul-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fmul64 (opa) (opb) (scale) fzp dnp rmode 0 0)
      (mv-let (data-spec r-spec)
              (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
	(implies (and (= (fused) 0)
	              (= (fscale) 0))
                 (and (equal data data-spec)
                      (equal (logior (rin) flags) r-spec)))))))

(defthm fmul64-fmul-correct
  (implies (input-constraints opa opb scale rin 0 0)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags) (fmul64 opa opb scale fzp dnp rmode 0 0)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-binary-spec 'mul opa opb rin (dp))
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())
 
;; FSCALE theorem:

(defthm fmul64-fscale-main
  (mv-let (data-spec r-spec) (arm-fscale-spec (opa) (scale) (rin) (dp))
    (implies (= (fscale) 1)
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec)))))

(defthmd fmul64-fscale-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fmul64 (opa) (opb) (scale) fzp dnp rmode 0 1)
      (mv-let (data-spec r-spec)
              (arm-fscale-spec (opa) (scale) (rin) (dp))
	(implies (= (fscale) 1)
                 (and (equal data data-spec)
                      (equal (logior (rin) flags) r-spec)))))))

(defthm fmul64-fscale-correct
  (implies (input-constraints opa opb scale rin 0 1)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags) (fmul64 opa opb scale fzp dnp rmode 0 1)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-fscale-spec opa scale rin (dp))
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())
