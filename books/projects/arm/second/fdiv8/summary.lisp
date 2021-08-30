(in-package "RTL")

(include-book "final")

;; We impose the following constraints on the inputs of execute:

(defund input-constraints (opa opb fnum rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

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
  :rule-classes ())

;; In order to address the lack of modularity of the ACL2 code, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate (((opa) => *) ((opb) => *) ((fnum) => *) ((rin) => *))
  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun fnum () 0))
  (local (defun rin () 0))
  (defthm input-constraints-lemma
    (input-constraints (opa) (opb) (fnum) (rin))
    :rule-classes ()))

;; The following inputs of execute are derived from the above:

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))
(defund f () (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))

;; In terms of these constants, we define constants corresponding to the local 
;; variables of the top-level function, execute, culminating in the constants
;; (data) and (flags) corresponding to the outputs.

;; Operand components and updated flags computed by analyze:

(defund signa () (mv-nth 0 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund expa () (mv-nth 1 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund mana () (mv-nth 2 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund classa () (mv-nth 3 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund flags-a () (mv-nth 4 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))

(defund signb () (mv-nth 0 (mv-list 5 (analyze (opb) (fnum) (fzp) (flags-a)))))
(defund expb () (mv-nth 1 (mv-list 5 (analyze (opb) (fnum) (fzp) (flags-a)))))
(defund manb () (mv-nth 2 (mv-list 5 (analyze (opb) (fnum) (fzp) (flags-a)))))
(defund classb () (mv-nth 3 (mv-list 5 (analyze (opb) (fnum) (fzp) (flags-a)))))
(defund flags-b () (mv-nth 4 (mv-list 5 (analyze (opb) (fnum) (fzp) (flags-a)))))

;; Sign of quotient:

(defund sign () (logxor (signa) (signb)))

;; Outputs in the event of a special case (zero, infinity, or NaN operand):

(defund data-special ()
  (mv-nth 0 (mv-list 2 (specialcase (sign) (opa) (opb) (classa) (classb) (fnum) (dnp) (flags-b)))))
(defund flags-special ()
  (mv-nth 1 (mv-list 2 (specialcase (sign) (opa) (opb) (classa) (classb) (fnum) (dnp) (flags-b)))))

;; Indication of division by a power of 2:

(defund divpow2 () (logand1 (logand1 (log= (classa) 4) (log= (classb) 4)) (log= (manb) 0)))

;; Normalized significands and exponent difference:

(defund siga () (mv-nth 0 (mv-list 3 (normalize (expa) (expb) (mana) (manb) (fnum)))))
(defund sigb () (mv-nth 1 (mv-list 3 (normalize (expa) (expb) (mana) (manb) (fnum)))))
(defund expdiff () (mv-nth 2 (mv-list 3 (normalize (expa) (expb) (mana) (manb) (fnum)))))

;; Multiples of the divisor:

(defund div () (bits (ash (sigb) 14) 70 0))
(defund div2 () (bits (ash (div) 1) 70 0))
(defund div3 () (bits (+ (div) (div2)) 70 0))

;; Array of comparison constants:

(defund cmpconst () (computecmpconst (bits (div) 65 60)))

;; Significand comparison:

(defund sigcmp () (bits (+ (sigb) (bits (lognot (siga)) 52 0)) 53 0))
(defund sigaltsigb () (bitn (sigcmp) 53))

;; Carry vector of partial remainder, RP_1:

(defund rp-1 ()
  (if1 (sigaltsigb)
       (bits (ash (siga) 15) 70 0)
     (bits (ash (siga) 14) 70 0)))

;; Approximation of R_0 and first quotient digit q_1:

(defund rs10-0 () (bits (rp-1) 70 61))

(defund gep2 () (bits (+ (rs10-0) (ag 5 (cmpconst))) 10 0))

(defund q-1 () 
  (if1 (bitn (gep2) 10) 2 1))

;; Initial quotient and decremented quotient:

(defund quot-1 () 
  (if1 (bitn (gep2) 10) (bits 2 64 0) (bits 1 64 0)))

(defund quotm1-1 () 
  (if1 (bitn (gep2) 10) (bits 1 64 0) (bits 0 64 0)))

;; Sum vector of partial remainder, RN_1:

(defund rn-1 () 
  (if1 (bitn (gep2) 10) (div2) (div)))

;; Approximation of R_1:

(defund rs10-1 ()
  (bits (+ (+ (bits (rp-1) 67 58)
              (lognot (bits (rn-1) 67 58)))
           1)
        9 0))

;; Exponent of unrounded quotient:

(defund expq ()
  (if1 (sigaltsigb)
       (bits (- (si (expdiff) 13) 1) 12 0)
     (expdiff)))

;; Number of cycles (and number of iterations of the main loop):

(defund c ()
  (case (fnum)
    (2 (bits 9 4 0))
    (1 (bits 4 4 0))
    (0 (bits 2 4 0))
    (t 0)))

;; lsb of the quotient is a index 1 for SP and index 2 for HP and DP:

(defund lsbis2 () (log<> (fnum) 1))

;; Final signed-digit remainder and the several variants of the quotient computed by the loop:

(defund rpf ()
  (mv-nth 5 (mv-list 12
    (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1)))))
(defund rnf ()
  (mv-nth 6 (mv-list 12
    (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1)))))
(defund quotpf ()
  (mv-nth 8 (mv-list 12
    (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1)))))
(defund quotm1pf ()
  (mv-nth 9 (mv-list 12 
    (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1)))))
(defund quotf ()
  (mv-nth 10 (mv-list 12
    (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1)))))
(defund quotm1f ()
  (mv-nth 11 (mv-list 12
    (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1)))))

;; Assimilated quotient, incremented quotient, and sticky bit, computed by computeQ:

(defund qtrunc ()
  (if1 (divpow2)
       (bits (ash (mana) 1) 52 0)
     (mv-nth 0 (mv-list 3 (computeq (quotf) (quotm1f) (quotpf) (quotm1pf) (rpf) (rnf) (lsbis2))))))

(defund qinc ()
  (if1 (divpow2)
       0
     (mv-nth 1 (mv-list 3 (computeq (quotf) (quotm1f) (quotpf) (quotm1pf) (rpf) (rnf) (lsbis2))))))

(defund stk ()
  (if1 (divpow2)
       0
     (mv-nth 2 (mv-list 3 (computeq (quotf) (quotm1f) (quotpf) (quotm1pf) (rpf) (rnf) (lsbis2))))))

;; Rounded results and inexact indications for normal and subnormal cases, comoputed by rounder:

(defund qrnd () (mv-nth 0 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund inx () (mv-nth 1 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund qrndden () (mv-nth 2 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund inxden () (mv-nth 3 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))

;; Final result derived from rounder outputs:

(defund data-final () (mv-nth 0 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) (sign) (expq) (rmode) (fzp) (fnum) (flags-b)))))
(defund flags-final () (mv-nth 1 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) (sign) (expq) (rmode) (fzp) (fnum) (flags-b)))))

;; Selection between special and rounded results:

(defund data ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0)
                                                                      (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
                (log= (classb) 3))
       (data-special)
     (data-final)))

(defund flags ()
  (if1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0)
                                                                      (log= (classa) 1))
                                                             (log= (classa) 2))
                                                    (log= (classa) 3))
                                           (log= (classb) 0))
                                  (log= (classb) 1))
                         (log= (classb) 2))
                (log= (classb) 3))
       (flags-special)
     (flags-final)))

;; The above constant definitions are based closely on the definition of fdiv8 so that
;; the proof of the following is trivial:

(defthmd fdiv8-lemma
  (mv-let (data flags) (fdiv8 (opa) (opb) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(signa expa mana classa flags-a signb expb manb classb flags-b data-special flags-special divpow2 siga sigb
	                expdiff div div2 div3 cmpconst sigcmp sigaltsigb rp-1 rn-1 expq rs10-0 rs10-1 gep2 q-1 n rp-2n1 rn-2n1 qp-2n1
			qn-2n1 qinc qtrunc stk sign qrnd inx qrndden inxden data-final flags-final data flags fdiv8))))



;; The real work is the proof of the following theorem:

(defthm fdiv8-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec)
            (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (not-specialp-main specialp-main))))


;; The following is an immediate consequence of the two preceding results:

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

;; The desired theorem is then derived by functional instantiation.

;;--------------------------------------------------------------------------------------------

;; We define the sequences of values (q j), (rp j), (rn j), (quotp j), (quotm1p j),
;; (quot j), and (quotm1 j) as a set of mutually recursive functions, as they are 
;; computed by fdiv8-loop-1:

(mutual-recursion

(defund q (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      (q-1)
    (nextdigit (rs10 (1- j)) (cmpconst))))

(defund divsigned (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if1 (bitn (rs10 (1- j)) 9)
         (div)
       (bits (lognot (div)) 70 0))))

(defund div3signed (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if1 (bitn (rs10 (1- j)) 9)
         (div3)
       (bits (lognot (div3)) 70 0))))

(defund rs11 (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (= (mod j 2) 0)
        (computers11 (rp (1- j)) (rn (1- j)) (q j) (divsigned j) (div3signed j))
      (rs11 (1- j)))))

(defund rp (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rp-1)
    (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (bitn (rs10 (1- j)) 9) (q j) (divsigned j) (div3signed j) (fnum))))))

(defund rn (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rn-1)
    (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (bitn (rs10 (1- j)) 9) (q j) (divsigned j) (div3signed j) (fnum))))))

(defund rs10 (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (zp j)
      (rs10-0)
    (if (= j 1)
        (rs10-1)
      (if (= (mod j 2) 0)
          (bits (+ (+ (bits (rp j) 67 58) (lognot (bits (rn j) 67 58))) 1) 9 0)
        (computers10 (divsigned j) (div3signed j) (q j) (rs11 (1- j)))))))

(defund quot (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (quot-1)
    (mv-nth 0 (mv-list 2 (nextquot (q j) (quot (1- j)) (quotm1 (1- j)))))))

(defund quotm1 (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (quotm1-1)
    (mv-nth 1 (mv-list 2 (nextquot (q j) (quot (1- j)) (quotm1 (1- j)))))))

(defund qlast (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (= (mod j 2) 0)
        (q j)
      (qlast (1- j)))))

(defund quotlast (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if (= (mod j 2) 0)
        (quot (1- j))
      (quotlast (1- j)))))

(defund quotm1last (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (= (mod j 2) 0)
        (quotm1 (1- j))
      (quotm1last (1- j)))))

(defund quotp (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (= (mod j 2) 1)
        (mv-nth 0 (mv-list 2 (incquot (q j) (quot (1- j)) (quotm1 (1- j)) (qlast j) (quotlast j) (quotm1last j) (lsbis2))))
      (quotp (1- j)))))

(defund quotm1p (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (= (mod j 2) 1)
        (mv-nth 1 (mv-list 2 (incquot (q j) (quot (1- j)) (quotm1 (1- j)) (qlast j) (quotlast j) (quotm1last j) (lsbis2))))
      (quotm1p (1- j)))))
)

;; The constants (rpf), etc., defined above are related to these functions as follows:

(defthmd rpf-rewrite
  (equal (rpf) (rp (1+ (* 2 (c))))))

(defthmd rnf-rewrite
  (equal (rnf) (rn (1+ (* 2 (c))))))

(defthmd quotf-rewrite
  (equal (quotf) (quot (1+ (* 2 (c))))))

(defthmd quotm1f-rewrite
  (equal (quotm1f) (quotm1 (1+ (* 2 (c))))))

(defthmd quotpf-rewrite
  (equal (quotpf)
         (mv-nth 0 (mv-list 2 (incquot (q (1+ (* 2 (c)))) (quot (* 2 (c))) (quotm1 (* 2 (c)))
	                               (q (* 2 (c))) (quot (1- (* 2 (c)))) (quotm1 (1- (* 2 (c))))
				       (lsbis2))))))

(defthmd quotm1pf-rewrite
  (equal (quotm1pf)
         (mv-nth 1 (mv-list 2 (incquot (q (1+ (* 2 (c)))) (quot (* 2 (c))) (quotm1 (* 2 (c)))
	                               (q (* 2 (c))) (quot (1- (* 2 (c)))) (quotm1 (1- (* 2 (c))))
				       (lsbis2))))))


;;********************************************************************************************
;; Special Cases
;;********************************************************************************************

;; The special cases of a zero, infinity, or NaN operand are handled separately:

(defund specialp ()
  (or (member (classa) '(0 1 2 3))
      (member (classb) '(0 1 2 3))))

(defthm specialp-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
      (implies (specialp)
               (and (equal (data) data-spec)
                    (equal (logior (rin) (flags)) r-spec))))))


;;********************************************************************************************
;; Normalization of Operands
;;********************************************************************************************

;; Formatted operands are in lower bits of inputs:

(defund fmtw () (+ 1 (expw (f)) (sigw (f))))

(defund opaw () (bits (opa) (1- (fmtw)) 0))

(defund opbw () (bits (opb) (1- (fmtw)) 0))

;; Operand fields:

(defthmd spec-fields
  (implies (not (specialp))
           (and (equal (sgnf (opaw) (f)) (signa))
	        (equal (expf (opaw) (f)) (expa))
		(equal (manf (opaw) (f)) (mana))
	        (equal (sgnf (opbw) (f)) (signb))
	        (equal (expf (opbw) (f)) (expb))
		(equal (manf (opbw) (f)) (manb)))))

;; Each operand is either normal or denormal:

(defthm spec-class
  (implies (not (specialp))
           (and (or (normp (opaw) (f))
	            (denormp (opaw) (f)))
		(or (normp (opbw) (f))
	            (denormp (opbw) (f)))))
  :rule-classes ())

;; Operand values:

(defund a () (decode (opaw) (f)))

(defund b () (decode (opbw) (f)))

;; Precision:

(defund p () (prec (f)))

;; Leading zero counter used in normalization:

(defthmd clz-expo
  (implies (and (bvecp s 53) (> s 0))
           (equal (clz53 s) (- 52 (expo s)))))

;; Significands:

(defthmd siga-rewrite
  (implies (not (specialp))
	   (equal (siga) (* (expt 2 52) (sig (a))))))

(defthmd sigb-rewrite
  (implies (not (specialp))
	   (equal (sigb) (* (expt 2 52) (sig (b))))))

;; Exponent difference:

(defthmd expdiff-rewrite
  (implies (not (specialp))
	   (equal (expdiff)
	          (bits (+ (- (expo (a)) (expo (b))) (bias (f))) 12 0))))

(defthmd si-expdiff-rewrite
  (implies (not (specialp))
	   (equal (si (expdiff) 13)
	          (+ (- (expo (a)) (expo (b))) (bias (f))))))

;; Quotient as a function of significands and exponent difference:

(defthmd quotient-formula
  (implies (not (specialp))
           (equal (abs (/ (a) (b)))
	          (* (expt 2 (- (si (expdiff) 13) (bias (f))))
		     (/ (siga) (sigb))))))

;;********************************************************************************************

;; Divisor and dividend:

(defund d () (* (sig (b)) 1/2))

(defund x ()
  (if (>= (sig (a)) (sig (b)))
      (* (sig (a)) 1/2)
    (sig (a))))

(defthmd d-bounds
  (implies (not (specialp))
           (and (<= 1/2 (d))
	        (< (d) 1))))

(defthmd x-bounds
  (implies (not (specialp))
           (and (<= (d) (x))
	        (< (x) (* 2 (d))))))

;; Partial quotients:

(defund quotient (j)
  (if (zp j)
      0
    (+ (quotient (1- j))
       (* (expt 8 (- 1 j)) (q j)))))

;; Partial remainders:

(defund r (j)
  (* (expt 8 (1- j))
     (- (x) (* (d) (quotient j)))))

;; Partial remainder recurrence relation:

(defthmd r0-rewrite
  (equal (r 0) (/ (x) 8))
  :hints (("Goal" :in-theory (enable quot r))))

(defthmd r-recurrence
  (implies (natp j)
           (equal (r (+ 1 j))
                  (- (* 8 (r j))
                     (* (q (1+ j)) (d)))))
  :hints (("Goal" :in-theory (enable r quot))))

;; The final quotient and remainder:

(defund qf () (quotient (1+ (* 2 (c)))))

(defund rf () (r (1+ (* 2 (c)))))

;; Our objective in the selection of quotient digits is to ensure that |R_j| <= 4/7 * d.
;; This holds trivially for j = 0:

(defthmd r0-bound
  (implies (not (specialp))
           (< (abs (r 0)) (* 4/7 (d)))))

;; Invariance of the bound on the partial remainder is ensured by computing an approximation
;; a of 8*R_j and comparing it to a set of "comparision constants", which depend on the top 6
;; bits of the divisor, i = div[65:60].  For -3 <= k <= 4, the comparision constant m(k, i)
;; is the array entry at index k + 3:

(defun m (k i)
  (- (* 1/64 (si (ag (+ k 3) (computecmpconst i)) 10))))

;; Given an approximation A_j of 8*R_j, q_(j+1) is selected as the largest k such that
;; m(k, i) <= A_j:

(defund maxk (a)
  (cond ((<= (m 4 (bits (div) 65 60)) a) 4)
        ((<= (m 3 (bits (div) 65 60)) a) 3)
        ((<= (m 2 (bits (div) 65 60)) a) 2)
        ((<= (m 1 (bits (div) 65 60)) a) 1)
        ((<= (m 0 (bits (div) 65 60)) a) 0)
        ((<= (m -1 (bits (div) 65 60)) a) -1)
        ((<= (m -2 (bits (div) 65 60)) a) -2)
        ((<= (m -3 (bits (div) 65 60)) a) -3)
        (t -4)))

;; The comparison constant (m k i) is (md8 k i) of "books/rtl/rel11/lib/srt.lisp":

(defthmd m-md8
  (implies (and (integerp k) (<= -3 k) (<= k 4)
                (bvecp i 6))
           (equal (m k i) (md8 k i))))

;; And (bits (div) 65 60)) = (fl (* 128 (- (d) 1/2))) = (i64 (d)):
	   
(defthmd bits-div-rewrite
  (implies (not (specialp))
           (equal (bits (div) 65 60)
                  (fl (* 128 (- (d) 1/2))))))

;; Consequently, we have the following equivalence:

(defthmd maxk-select-digit-d8
  (implies (and (not (specialp)) (rationalp a))
           (equal (maxk a) (select-digit-d8 a (i64 (d))))))

;; The desired invariant may be derived by functional instantiation from srt-div-rad-8:

(defthmd r-bound-inv
  (implies (and (not (specialp))
                (natp j)
                (<= (abs (r j)) (* 4/7 (d)))
                (rationalp approx)
                (integerp (* 64 approx))
                (< (abs (- approx (* 8 (r j)))) 1/64)
                (= (q (1+ j)) (maxk approx)))
	   (<= (abs (r (1+ j))) (* 4/7 (d)))))

;; The approximation of 8*R_j is defined as follows:

(defund approx (j)
  (/ (si (rs10 j) 10) 64))

;; The following is proved by induction:

(defthmd induction-result
  (implies (and (not (specialp))
                (not (zp j))
		(<= j (1+ (* 2 (c)))))
           (and (= (q j) (maxk (approx (1- j))))
                (< (abs (- (approx (1- j)) (* 8 (r (1- j))))) 1/64)
                (<= (abs (r j)) (* 4/7 (d)))
                (bvecp (rp j) 71)
                (bvecp (rn j) 71)
                (= (mod (* (expt 2 67) (r j)) (expt 2 71)) (mod (- (rp j) (rn j)) (expt 2 71)))
                (= (bits (rp j) (- 63 (p)) 0) 0)
                (= (bits (rn j) (- 63 (p)) 0) 0)
                (bvecp (quot j) (* 3 j))
                (bvecp (quotm1 j) (* 3 j))
                (= (quot j) (* (expt 8 (1- j)) (quotient j)))
                (= (quotm1 j) (1- (quot j))))))

;; Instantiating the above with j = 2*n+1 yields the following arror bound for the final quotient:

(defthmd q-error
  (implies (not (specialp))
           (<= (abs (- (/ (x) (d)) (qf)))
	       (* 4/7 (expt 2 (- (* 6 (c))))))))
	       

;;********************************************************************************************
;; Quotient Computation
;;********************************************************************************************

;; quotpf and quotm1pf are related to quotf and quotm1f as follows:

(defthmd incquot-lemma
  (implies (not (specialp))
           (let ((inc (if (= (lsbis2) 1) 4 2)))
             (and (equal (quotpf) (+ (quotf) inc))
                  (equal (quotm1pf)(+ (quotm1f) inc))))))

;; Truncated absolute value of quotient:

(defthmd qtrunc-rewrite-gen
  (implies (not (specialp))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p))))))

;; Incremented absolute value of quotient (not needed for division by powere of 2):

(defthmd qinc-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (p)) (/ (x) (d)))) 2) (expt 2 (p))))))

;; Sticky bit:

(defthmd stk-rewrite-gen
  (implies (not (specialp))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1))))

;;********************************************************************************************
;; Rounding
;;********************************************************************************************

;; Rounding mode determined by encoding rmode:

(defund mode ()
  (case (rmode)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

;; Rounding mode to be applied to absolute value of quotient:

(defund modep ()
  (if (< (/ (a) (b)) 0)
      (flip-mode (mode))
    (mode)))

(defthmd rnd-modep-mode
  (implies (not (specialp))
           (equal (rnd (/ (a) (b)) (mode) (p))
	          (if (< (/ (a) (b)) 0)
		      (- (rnd (abs (/ (a) (b))) (modep) (p)))
		    (rnd (abs (/ (a) (b))) (modep) (p))))))

;; Normal case:

(defthmd rnd-inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (= (rnd (abs (/ (a) (b))) (modep) (p))
		         (abs (/ (a) (b))))
		      0 1))))

(defthmd rnd-a/b-qrnd
  (implies (not (specialp))
           (equal (rnd (abs (/ (a) (b))) (modep) (p))
	          (* (expt 2 (+ (si (expq) 13) (- (bias (f))) (- (1- (p)))))
		     (+ (expt 2 (1- (p)))
		        (bits (qrnd) (- (p) 2) 0))))))

;; Subnormal case:

(defthmd drnd-inxden-rewrite
  (implies (and (not (specialp))
                (< (abs (/ (a) (b))) (spn (f))))
           (equal (inxden)
	          (if (= (drnd (abs (/ (a) (b))) (modep) (f))
	                 (abs (/ (a) (b))))
	              0 1))))

(defthmd drnd-a/b-qrndden
  (implies (and (not (specialp))
                (< (abs (/ (a) (b))) (spn (f))))
           (equal (drnd (abs (/ (a) (b))) (modep) (f))
	          (* (expt 2 (+ 1 (- (bias (f))) (- (1- (p)))))
		     (bits (qrndden) (1- (p)) 0)))))


;;********************************************************************************************
;; Final Result
;;********************************************************************************************

(defthm fdiv8-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec)
            (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec)))))

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
             (equal (logior (rin) flags) r-spec))))))

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
  :rule-classes ())
