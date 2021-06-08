(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "fmul64")

(local (include-book "fused"))

;; We impose the following constraints on the arguments of fmul64:

(defund input-constraints (opa opb rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Two operations are performed by fmul64: FMUL and a multiplication in
;; support of FMA.  These are distinguished by an additional boolean argument,
;; fused.

;; With regard to FMUL, our ultimate objective is the following theorem:

(defthm fmul64-correct
  (implies (input-constraints opa opb rin)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags) (fmul64 opa opb fzp dnp rmode 0)
               (let ((r (logior rin flags)))
                 (mv-let (data-spec r-spec)
                         (arm-binary-spec 'mul opa opb rin (dp))
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())

;; In order to address the lack of modularity of the ACL2 code, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate (((opa) => *) ((opb) => *) ((rin) => *) ((fused) => *))
  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun rin () 0))
  (local (defun fused () 0))
  (defthm input-constraints-lemma
    (input-constraints (opa) (opb) (rin))
    :rule-classes ())
  (defthm bitp-fused
    (bitp (fused))
    :rule-classes ()))

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))

;; In terms of these constants, we shall define constants corresponding to the
;; local variables of fmul64, culminating in the constants (data) and (flags),
;; corresponding to the outputs.

;; The constant definitions will be derived from that of fmul64 in such a way
;; that the proof of the following will be trivial:

;; (defthmd fmul64-lemma
;;   (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) (fzp) (dnp) (rmode) (fused))
;;     (and (equal (data) data)
;;          (equal (flags) flags)
;;   	    (equal (prodinfzero) prodinfzero)
;; 	    (equal (infnanzero) infnanzero)
;; 	    (equal (expovfl) expovfl))))

;; The real work will be the proof of the following theorems:

;; (defthm fmul64-main
;;   (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
;;     (implies (= (fused) 0)
;;              (and (equal (data) data-spec)
;;                   (equal (logior (rin) (flags)) r-spec)))))

;; The following are immediate consequences of the preceding results:

;; (defthmd fmul64-lemma-to-be-functionally-instantiated
;;   (let ((dnp (bitn (rin) 25))
;;         (fzp (bitn (rin) 24))
;;         (rmode (bits (rin) 23 22)))
;;     (mv-let (data flags) (fmul64 (opa) (opb) fzp dnp rmode 0)
;;       (mv-let (data-spec r-spec)
;;               (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
;; 	(implies (= (fused) 0)
;;                  (and (equal data data-spec)
;;                       (equal (logior (rin) flags) r-spec)))))))

;; The desired theorem can then be derived by functional instantiation.

;; For the multiplication in support of FMA, there is no architectural specification,
;; so we define a separate specification predicate, fmul64-fused-spec.

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
       (= (bitn flags (dzc)) 0)
       (= (bitn flags (ufc)) 0)
       (= (bitn flags (ofc)) 0)
       (= (bitn flags (ixc)) 0)
       (= (bitn flags 5) 0)
       (= (bitn flags 6) 0)
       (= (bitn flags (idc))
          (if (or (fzerp a fz) (fzerp b fz)) 1 0))
       (= (bitn flags (ioc))
          (if (or (snanp a (dp)) (snanp b (dp)) (inf-times-zero a b fz)) 1 0))
       (= expovfl 0)
       (= data (ash (fmul64-fused-spec-special-val a b fz dn) 53))))


;; Note that in the case of a subnormal product, the specification does not
;; compute a specific value, but rather constrains it:

(defun fmul64-fused-comp (a b data flags prodinfzero infnanzero expovfl)
  (let ((prod (* (decode a (dp)) (decode b (dp)))))
    (and (= prodinfzero 0)
         (= infnanzero 0)
         (= (bitn flags (dzc)) 0)
         (= (bitn flags (ufc)) 0)
         (= (bitn flags (ofc)) 0)
         (= (bitn flags (idc)) 0)
         (= (bitn flags (ioc)) 0)
         (= (bitn flags 5) 0)
         (= (bitn flags 6) 0)
         (= (bitn data 116) (if (< prod 0) 1 0))
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

(defthm fmul64-fused-correct
  (implies (input-constraints opa opb rin)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb fzp dnp rmode 1)
               (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
  :rule-classes ())

;; Once again, the theorem is proved by functional instantiation:

;; (defthmd fmul64-fused-main
;;   (implies (= (fused) 1)
;;            (fmul64-fused-spec (opa) (opb) (fzp) (dnp) (data) (flags)
;;                               (prodinfzero) (infnanzero) (expovfl))))

;; (defthmd fmul64-fused-lemma-to-be-functionally-instantiated
;;   (let ((dnp (bitn (rin) 25))
;;         (fzp (bitn (rin) 24))
;;         (rmode (bits (rin) 23 22)))
;;     (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) fzp dnp rmode 1)
;; 	(implies (= (fused) 1)
;;                  (fmul64-fused-spec (opa) (opb) fzp dnp data flags prodinfzero infnanzero expovfl)))))


;;*******************************************************************************
;; fmul64
;;*******************************************************************************

;; Here we define the constants corresponding to the local variables of fmul64.

;; Opeerand components and data classes, returned by analyze:

(defund signa () (mv-nth 0 (mv-list 5 (analyze (opa) 2 (fzp) (bits 0 7 0)))))
(defund expa () (mv-nth 1 (mv-list 5 (analyze (opa) 2 (fzp) (bits 0 7 0)))))
(defund mana () (mv-nth 2 (mv-list 5 (analyze (opa) 2 (fzp) (bits 0 7 0)))))
(defund classa () (mv-nth 3 (mv-list 5 (analyze (opa) 2 (fzp) (bits 0 7 0)))))
(defund flags-a () (mv-nth 4 (mv-list 5 (analyze (opa) 2 (fzp) (bits 0 7 0)))))
(defund signb () (mv-nth 0 (mv-list 5 (analyze (opb) 2 (fzp) (flags-a)))))
(defund expb () (mv-nth 1 (mv-list 5 (analyze (opb) 2 (fzp) (flags-a)))))
(defund manb () (mv-nth 2 (mv-list 5 (analyze (opb) 2 (fzp) (flags-a)))))
(defund classb () (mv-nth 3 (mv-list 5 (analyze (opb) 2 (fzp) (flags-a)))))
(defund flags-b () (mv-nth 4 (mv-list 5 (analyze (opb) 2 (fzp) (flags-a)))))

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

(defund clz* ()
  (let* ((clz (bits 0 5 0))
         (clz (if1 (log= (expa) 0)
                   (logior clz (clz53 (mana)))
                   clz)))
    (if1 (log= (expb) 0)
         (logior clz (clz53 (manb)))
         clz)))

;; Multiplier output:

(defund prod ()
  (computeproduct (mana) (manb) (log= (expa) 0) (log= (expb) 0)))

;; Internal representation of product exponent:

(defund expprodint () (bits (+ (+ (expint (expa)) (expint (expb))) 1) 11 0))
(defund expbiasedzero () (log= (expprodint) 3072))
(defund expbiasedneg () (log= (bits (expprodint) 11 10) 2))

;; Internal representation of exponent after shifting:

(defund expshftint ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 0 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 0 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

;; Indication of exponent increment:

(defund expinc ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 1 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 1 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

;; FMA outputs:

(defund stkfma ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 3 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 3 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

(defund expzero () (log= (bits (expshftint) 11 0) 3072))

(defund expmax () (log= (bits (expshftint) 11 0) 1022))

(defund expinf () (log= (bits (expshftint) 11 0) 1023))

(defund expgtinf () (log= (bits (expshftint) 11 10) 1))

(defund exp11 ()
  (let ((exp11 (bits (expshftint) 10 0)))
    (setbitn exp11 11 10 (lognot1 (bitn exp11 10)))))

(defund sign () (logxor (signa) (signb)))

(defund frac105 ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 2 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 2 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

(defund data-fma ()
  (let ((d (setbitn 0 117 116 (sign))))
    (setbits (if1 (logand1 (expinc) (lognot1 (expinf)))
                  (setbits d 117 115 105 (+ (exp11) 1))
                  (setbits d 117 115 105 (exp11)))
             117 104 0 (frac105))))

(defund flags-fma ()
  (setbitn (flags-b) 8 (ixc) (stkfma)))
       
(defund prodinfzero-fma () (false$))

(defund infnanzero-fma () (false$))

(defund expovfl-fma () (logior1 (expgtinf) (logand1 (expinf) (expinc))))

;; Rounded result and FMUL outputs:

(defund lsb ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 4 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 4 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

(defund grd ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 5 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 5 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

(defund stk ()
  (if1 (logior1 (expbiasedzero) (expbiasedneg))
       (mv-nth 6 (mv-list 7 (rightshft (expa) (expb) (prod))))
       (mv-nth 6 (mv-list 7 (leftshft (expa) (expb) (prod) (clz*))))))

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
  (logior1 (logior1 (expgtinf) (expinf))
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
       (setbitn (setbitn (flags-b) 8 (ixc) 1) 8 (ofc) 1)
       (if1 (underflow)
	    (if1 (fzp)
	         (setbitn (flags-b) 8 (ufc) 1)
	         (if1 (logior1 (grd) (stk))
                      (let ((flags (setbitn (flags-b) 8 (ufc) 1)))
                        (setbitn flags 8 (ixc) 1))
                      (flags-b)))
            (if1 (logior1 (grd) (stk))
                 (setbitn (flags-b) 8 (ixc) 1)
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
  (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) (fzp) (dnp) (rmode) (fused))
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

(defthmd specialp-main
  (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
    (implies (and (= (fused) 0) (specialp))
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
  (if (= (expb) 0)
      (- 1 (1- (expt 2 10)))
    (- (expb) (1- (expt 2 10)))))

(defund a () (decode (opaz) (dp)))

(defund b () (decode (opbz) (dp)))

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

;; Internal representations of operand exponents:

(defthmd si-expaint
  (equal (si (expint (expa)) 12)
         (1- (ea))))

(defthmd si-expbint
  (equal (si (expint (expb)) 12)
         (1- (eb))))

;; Internal representations of product exponent:

(defthmd si-expprodint
  (implies (not (specialp))
           (equal (si (expprodint) 12)
	          (1- (+ (ea) (eb))))))

(defthmd expbiasedzero-rewrite
  (implies (not (specialp))
           (equal (expbiasedzero)
	          (if (= (+ (ea) (eb) (1- (expt 2 10))) 0)
		      1 0))))

(defthmd expbiasedneg-rewrite
  (implies (not (specialp))
           (equal (expbiasedneg)
	          (if (< (+ (ea) (eb) (1- (expt 2 10))) 0)
		      1 0))))

;; Difference between 1 and the biased sum of operand exponents:

(defund expdeficit ()
  (bits (+ (+ (+ (lognot (expa)) (lognot (expb))) 1)
           (logand1 (log<> (expa) 0) (log<> (expb) 0)))
        9 0))

(defthmd expdeficit-rewrite
  (implies (<= (+ (ea) (eb) (1- (expt 2 10))) 0)
	   (equal (expdeficit)
	          (if (and (= (expa) 0) (= (expb) 0))
		      (1- (expt 2 10))
		    (- 1 (+ (ea) (eb) (1- (expt 2 10))))))))

;; Leading zero count:

(defthmd clz-expo
  (implies (and (bvecp s 53) (> s 0))
           (equal (clz53 s) (- 52 (expo s)))))

(defthmd clz-rewrite
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
	   (equal (clz*)
	          (if (= (expa) 0)
		      (clz53 (mana))
		    (if (= (expb) 0)
		        (clz53 (manb))
		      0)))))

;; Values of exponent after shifting:

(defthmd expshftint-bound
  (implies (not (specialp))
           (>= (si (expshftint) 12) (- (expt 2 10)))))

(defthmd expzero-rewrite
  (implies (not (specialp))
           (equal (expzero)
	          (if (= (si (expshftint) 12) (- (expt 2 10)))
		      1 0))))

(defthmd expmax-rewrite
  (implies (not (specialp))
           (equal (expmax)
	          (if (= (si (expshftint) 12) (- (expt 2 10) 2))
		      1 0))))

(defthmd expinf-rewrite
  (implies (not (specialp))
           (equal (expinf)
	          (if (= (si (expshftint) 12) (1- (expt 2 10)))
		      1 0))))

(defthmd expgtinf-rewrite
  (implies (not (specialp))
           (equal (expgtinf)
	          (if (> (si (expshftint) 12) (1- (expt 2 10)))
		      1 0))))

;; Unbiased exponent of unrounded result:

(defund eab ()
  (+ (si (expshftint) 12)
     (expinc)
     1))

(defthmd eab-bound
  (implies (not (specialp))
           (>= (+ (eab) (1- (expt 2 10))) 0)))

(defthmd eab-val
  (implies (not (specialp))
	   (equal (+ (eab) (1- (expt 2 10)))
	          (+ (exp11) (* (expt 2 11) (expgtinf)) (expinc)))))

;; Normal case:

(defthmd unround-a
  (implies (and (not (specialp))
		(> (+ (eab) (1- (expt 2 10))) 0))
           (and (equal (stkfma) 0)
		(equal (abs (* (a) (b)))
	               (* (expt 2 (eab))
		          (1+ (* (expt 2 -105) (frac105))))))))

;; Denormal case:

(defthm unround-b
  (implies (and (not (specialp))
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
	                  (equal (stkfma)
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
    (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) fzp dnp rmode 1)
	(implies (= (fused) 1)
                 (fmul64-fused-spec (opa) (opb) fzp dnp data flags prodinfzero infnanzero expovfl)))))

(defthm fmul64-fused-correct
  (implies (input-constraints opa opb rin)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb fzp dnp rmode 1)
               (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
  :rule-classes ())


;;*******************************************************************************
;; Rounded Product and FMUL
;;*******************************************************************************

;; Rounding bits:

(defthmd stk-rewrite
  (implies (not (specialp))
	   (equal (stk)
	          (if (and (= (bits (frac105) 51 0) 0)
		           (= (stkfma) 0))
		      0 1))))

(defthmd grd-rewrite
  (implies (not (specialp))
	   (equal (grd)
	          (bitn (frac105) 52))))

(defthmd lsb-rewrite
  (implies (not (specialp))
	   (equal (lsb)
	          (bitn (frac105) 53))))

;; Two exponent increments (multiplication and rounding) cannot both occur:

(defthmd expinc-exprndinc
  (implies (and (not (specialp))
		(= (expinc) 1))
           (equal (exprndinc) 0)))

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
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (* (a) (b)) (mode) 53)
	          (if (= (sign) 1)
		      (- (* (expt 2 (+ (eab) -52 (exprndinc)))
		            (+ (expt 2 52) (fracrnd))))
	            (* (expt 2 (+ (eab) -52 (exprndinc)))
		       (+ (expt 2 52) (fracrnd)))))))

(defthmd norm-exact
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (rnd (* (a) (b)) (mode) 53)
	           (* (a) (b)))
	        (and (= (stk) 0) (= (grd) 0)))))

;; Denormal case:

(defthmd denorm-drnd-rndup
  (implies (and (not (specialp))
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
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (drnd (* (a) (b)) (mode) (dp))
		   (* (a) (b)))
	        (and (= (stk) 0) (= (grd) 0)))))

;; FMUL theorem:

(defthm fmul64-main
  (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
    (implies (= (fused) 0)
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec)))))

(defthmd fmul64-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fmul64 (opa) (opb) fzp dnp rmode 0)
      (mv-let (data-spec r-spec)
              (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
	(implies (= (fused) 0)
                 (and (equal data data-spec)
                      (equal (logior (rin) flags) r-spec)))))))

(defthm fmul64-correct
  (implies (input-constraints opa opb rin)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags) (fmul64 opa opb fzp dnp rmode 0)
               (let ((r (logior rin flags)))
                 (mv-let (data-spec r-spec)
                         (arm-binary-spec 'mul opa opb rin (dp))
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())
