(in-package "RTL")

(include-book "final")

;; We impose the following constraints on the inputs of fdiv64:

(defund input-constraints (opa opb fnum rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

(defthm fdiv64-correct
  (implies (input-constraints opa opb fnum rin)
           (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (dnp (bitn rin 25))
                  (fzp (bitn rin 24))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fdiv64 opa opb fnum fzp dnp rmode)
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

;; The following inputs of fdiv64 are derived from the above:

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))
(defund f () (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))

;; In terms of these constants, we define constants corresponding to the local
;; variables of the top-level function, fdiv64, culminating in the constants
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

;; Prescaled divisor, exponent of quotient, and results of first iteration, computed by prescale:

(defund div () (mv-nth 0 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund rp-1 () (mv-nth 1 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund rn-1 () (mv-nth 2 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund expq () (mv-nth 3 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund q-1 () (mv-nth 4 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))

;; Number of cycles (and number of iterations of the main loop):

(defund n ()
  (if1 (divpow2)
       (bits 0 4 0)
       (case (fnum)
         (2 (bits 9 4 0))
         (1 (bits 4 4 0))
         (0 (bits 2 4 0))
         (t 0))))

;; Final signed-digit remainder and quotient computed by the loop:

(defund rp-3n1 ()
  (mv-nth 1 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))
(defund rn-3n1 ()
  (mv-nth 2 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))
(defund qp-3n1 ()
  (mv-nth 3 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))
(defund qn-3n1 ()
  (mv-nth 4 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))

;; Assimilated quotient, incremented quotient, and sticky bit, computed by computeQ:

(defund qtrunc ()
  (if1 (divpow2)
       (bits (ash (mana) 1) 52 0)
     (mv-nth 0 (mv-list 3 (computeq (qp-3n1) (qn-3n1) (rp-3n1) (rn-3n1) (fnum) (false$))))))

(defund qinc ()
  (if1 (divpow2)
       0
     (mv-nth 1 (mv-list 3 (computeq (qp-3n1) (qn-3n1) (rp-3n1) (rn-3n1) (fnum) (false$))))))

(defund stk ()
  (if1 (divpow2)
       0
     (mv-nth 2 (mv-list 3 (computeq (qp-3n1) (qn-3n1) (rp-3n1) (rn-3n1) (fnum) (false$))))))

;; Rounded results and inexact indications for normal and subnormal cases, comoputed by rounder:

(defund qrnd () (mv-nth 0 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund inx () (mv-nth 1 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund qrndden () (mv-nth 2 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund inxden () (mv-nth 3 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))

;; Final result derived from rounder outputs:

(defund data-final ()
  (mv-nth 0 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) (sign) (expq) (rmode) (fzp) (fnum) (flags-b)))))
(defund flags-final ()
  (mv-nth 1 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) (sign) (expq) (rmode) (fzp) (fnum) (flags-b)))))

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

;; The aqbove constant definitions are based closely on the definition of fdiv64 so that
;; the proof of the following is trivial:

(defthmd fdiv64-lemma
  (mv-let (data flags) (fdiv64 (opa) (opb) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags))))

;; The real work is the proof of the following theorem:

(defthm fdiv64-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec)
            (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec)))))

;; The following is an immediate consequence of the two preceding results:

(defthmd lemma-to-be-functionally-instantiated
  (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
         (fmtw (+ 1 (expw f) (sigw f)))
         (dnp (bitn (rin) 25))
         (fzp (bitn (rin) 24))
         (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fdiv64 (opa) (opb) (fnum) fzp dnp rmode)
      (mv-let (data-spec r-spec)
              (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) f)
        (and (equal data data-spec)
             (equal (logior (rin) flags) r-spec))))))

;; The desired theorem is then derived by functional instantiation.

;;--------------------------------------------------------------------------------------------

;; We also define sequences of values (q j), (rp j), (rn j), (qp j), and (qn j),
;; representing the quotient digits, partial remainders, and partial quotients,
;; as a set of mutually recursive functions, as they are computed by fdiv64-loop-0:

(mutual-recursion

(defund q (j)
  (declare (xargs :measure (* 2 (nfix j))))
  (if (or (zp j) (= j 1))
      (q-1)
    (case (mod j 3)
      (2 (mv-nth 0 (mv-list 5 (iter1 (rp (1- j)) (rn (1- j)) (div) (fnum)))))
      (0 (mv-nth 0 (mv-list 4 (iter2 (rp (1- j)) (rn (1- j)) (rs6 (1- j)) (rs9 (1- j)) (div) (fnum)))))
      (1 (mv-nth 0 (mv-list 3 (iter3 (rp (1- j)) (rn (1- j)) (rs7 (1- j)) (div) (fnum))))))))

(defund rp (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rp-1)
    (case (mod j 3)
      (2 (mv-nth 1 (mv-list 5 (iter1 (rp (1- j)) (rn (1- j)) (div) (fnum)))))
      (0 (mv-nth 1 (mv-list 4 (iter2 (rp (1- j)) (rn (1- j)) (rs6 (1- j)) (rs9 (1- j)) (div) (fnum)))))
      (1 (mv-nth 1 (mv-list 3 (iter3 (rp (1- j)) (rn (1- j)) (rs7 (1- j)) (div) (fnum))))))))

(defund rn (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rn-1)
    (case (mod j 3)
      (2 (mv-nth 2 (mv-list 5 (iter1 (rp (1- j)) (rn (1- j)) (div) (fnum)))))
      (0 (mv-nth 2 (mv-list 4 (iter2 (rp (1- j)) (rn (1- j)) (rs6 (1- j)) (rs9 (1- j)) (div) (fnum)))))
      (1 (mv-nth 2 (mv-list 3 (iter3 (rp (1- j)) (rn (1- j)) (rs7 (1- j)) (div) (fnum))))))))

(defund rs6 (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (zp j)
      0
    (if (= (mod j 3) 2)
        (mv-nth 3 (mv-list 5 (iter1 (rp (1- j)) (rn (1- j)) (div) (fnum))))
      0)))

(defund rs9 (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (zp j)
      0
    (if (= (mod j 3) 2)
        (mv-nth 4 (mv-list 5 (iter1 (rp (1- j)) (rn (1- j)) (div) (fnum))))
      0)))

(defund rs7 (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (zp j)
      0
    (if (= (mod j 3) 0)
        (mv-nth 3 (mv-list 4 (iter2 (rp (1- j)) (rn (1- j)) (rs6 (1- j)) (rs9 (1- j)) (div) (fnum))))
      0)))

(defund qp (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (mv-nth 0 (mv-list 2 (nextquot (qp (1- j)) (qn (1- j)) (q j))))))

(defund qn (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (mv-nth 1 (mv-list 2 (nextquot (qp (1- j)) (qn (1- j)) (q j))))))
)

;; The constants (rp-3n1), etc., defined above are related to these functions as follows:

(defthm rp-3n1-rewrite
  (equal (rp-3n1) (rp (1+ (* 3 (n))))))

(defthm rn-3n1-rewrite
  (equal (rn-3n1) (rn (1+ (* 3 (n))))))

(defthm qp-3n1-rewrite
  (equal (qp-3n1) (qp (1+ (* 3 (n))))))

(defthm qn-3n1-rewrite
  (equal (qn-3n1) (qn (1+ (* 3 (n))))))


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

;; Formattede operands are in lower bits of inputs:

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

;; Prescaling multiplier, based on 3 MSBs of sigb:

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

;; Prescaled divisor and dividend:

(defund d () (* (mul) (sig (b)) 1/2))

(defund x ()
  (if (>= (sig (a)) (sig (b)))
      (* (mul) (sig (a)) 1/2)
    (* (mul) (sig (a)))))

(defthmd d-bounds
  (implies (not (specialp))
           (and (<= 63/64 (d))
	        (<= (d) 9/8))))

(defthmd x-bounds
  (implies (not (specialp))
           (and (<= (d) (x))
	        (< (x) (* 2 (d))))))

;; Partial quotients:

(defund quot (j)
  (if (zp j)
      0
    (+ (quot (1- j))
       (* (expt 4 (- 1 j)) (q j)))))

(defthmd int-quot
  (implies (natp j)
           (integerp (* (expt 4 (1- j)) (quot j)))))

;; Partial remainders:

(defund r (j)
  (* (expt 4 (1- j))
     (- (x) (* (d) (quot j)))))

;; Partial remainder recurrence relation:

(defthmd r0-rewrite
  (implies (not (specialp))
           (equal (r 0) (/ (x) 4))))

(defthmd r-recurrence
  (implies (and (not (specialp)) (natp j))
           (equal (r (+ 1 j))
                  (- (* 4 (r j))
                     (* (q (1+ j)) (d))))))

;; The final quotient and remainder:

(defund quotf () (quot (1+ (* 3 (n)))))

(defund rf () (r (1+ (* 3 (n)))))

;; Our objective in the selection of quotient digits is to ensure that |R_j| <= 2/3 * d.
;; This holds trivially for j = 0:

(defthmd r0-bound
  (implies (not (specialp))
           (< (abs (r 0)) (* 2/3 (d)))))

;; Invariance of the bound on the partial remainder is ensured by computing an approximation
;; a of 4*R_j and comparing it to a set of "selection constants":

(defun m (k)
  (case k (2 13/8) (1 4/8) (0 -3/8) (-1 -12/8)))

(defund maxk (a)
  (cond ((<= (m 2) a) 2)
        ((<= (m 1) a) 1)
        ((<= (m 0) a) 0)
        ((<= (m -1) a) -1)
        (t -2)))

(defthmd r-bound-inv
  (implies (and (not (specialp))
                (natp j)
                (<= (abs (r j)) (* 2/3 (d)))
                (rationalp approx)
                (integerp (* 8 approx))
                (< (abs (- approx (* 4 (r j)))) 1/8)
                (= (q (1+ j)) (maxk approx)))
	   (<= (abs (r (1+ j))) (* 2/3 (d)))))

;; The approximation of 4*R_j is given by the function approx, the definition of
;; which is not included here.  The following is proved by induction:

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
                (= (* (expt 4 (1- j)) (- (quot j) (q 1))) (- (qp j) (qn j))))))

;; Instantiating the above with j = 3*n+1 yields the following arror bound for the final quotient:

(defthmd q-error
  (implies (not (specialp))
           (<= (abs (- (/ (x) (d)) (quotf)))
	       (* 2/3 (expt 2 (- (* 6 (n))))))))

;;********************************************************************************************
;; Quotient Computation
;;********************************************************************************************

;; Truncated absolute value of quotient:

(defthmd qtrunc-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p))))))

(defthmd qtrunc-rewrite-divpow2
  (implies (and (not (specialp))
                (= (divpow2) 1))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (p)) (/ (x) (d)))) (expt 2 (p))))))

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

(defthmd stk-rewrite
  (implies (and (not (specialp))
                (= (divpow2) 0))
	   (equal (stk)
	          (if (integerp (* (expt 2 (p)) (/ (x) (d))))
		      0 1))))

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

(defthm fdiv64-main
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
    (mv-let (data flags) (fdiv64 (opa) (opb) (fnum) fzp dnp rmode)
      (mv-let (data-spec r-spec)
              (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) f)
        (and (equal data data-spec)
             (equal (logior (rin) flags) r-spec))))))

(defthm fdiv64-correct
  (implies (input-constraints opa opb fnum rin)
           (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (dnp (bitn rin 25))
                  (fzp (bitn rin 24))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fdiv64 opa opb fnum fzp dnp rmode)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-binary-spec 'div (bits opa (1- fmtw) 0) (bits opb (1- fmtw) 0) rin f)
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())
