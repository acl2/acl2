(in-package "RTL")

(include-book "final")

;; We impose the following constraints on the inputs of fsqrt64:

(defund input-constraints (opa fnum rin)
  (and (bvecp opa 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

(defthm fsqrt64-correct
  (implies (input-constraints opa fnum rin)
           (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (dnp (bitn rin 25))
                  (fzp (bitn rin 24))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fsqrt64 opa fnum fzp dnp rmode)
               (let ((r (logior rin flags)))
                 (mv-let (data-spec r-spec)
                         (arm-sqrt-spec (bits opa (1- fmtw) 0) rin f)
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())

;; In order to address the lack of modularity of the ACL2 code, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate (((opa) => *) ((fnum) => *) ((rin) => *))
  (local (defun opa () 0))
  (local (defun fnum () 0))
  (local (defun rin () 0))
  (defthm input-constraints-lemma
    (input-constraints (opa) (fnum) (rin))
    :rule-classes ()))

;; The following inputs of fsqrt64 are derived from the above:

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))
(defund f () (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))

;; In terms of these constants, we define constants corresponding to the local
;; variables of the top-level function, fsqrt64, culminating in the constants
;; (data) and (flags) corresponding to the outputs.

;; Operand components and updated flags computed by analyze:

(defund signa () (mv-nth 0 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund expa () (mv-nth 1 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund mana () (mv-nth 2 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund classa () (mv-nth 3 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund flags-a () (mv-nth 4 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))

;; Outputs in the event of a special case (zero, infinity, or NaN operand):

(defund data-special ()
  (mv-nth 0 (mv-list 2 (specialcase (signa) (opa) (classa) (fnum) (dnp) (flags-a)))))
(defund flags-special ()
  (mv-nth 1 (mv-list 2 (specialcase (signa) (opa) (classa) (fnum) (dnp) (flags-a)))))

;; Significand, adjusted exponent after normalization, and predicted result exponent:

(defund siga () (mv-nth 0 (mv-list 3 (normalize (expa) (mana) (fnum)))))
(defund expshft () (mv-nth 1 (mv-list 3 (normalize (expa) (mana) (fnum)))))
(defund expq () (mv-nth 2 (mv-list 3 (normalize (expa) (mana) (fnum)))))

;; Parity of adjusted exponent:

(defund expodd () (bitn (expshft) 0))

;; Initialization of expinc, which indicates that rewsult is rounded up to a power of 2:

(defund expinc-0 () (logand1 (log= (classa) 4) (log= (rmode) (rmodeup))))


;; Outputs in the event of a power-of-2 operand:

(defund d-sqrtpow2 () (mv-nth 0 (mv-list 2 (sqrtpow2 (expq) (expodd) (rmode) (fnum)))))
(defund flags-sqrtpow2 () (mv-nth 1 (mv-list 2 (sqrtpow2 (expq) (expodd) (rmode) (fnum)))))

;; Results of first iteration:

(defund rp-1 () (mv-nth 0 (mv-list 5 (firstiter (siga) (expodd)))))
(defund rn-1 () (mv-nth 1 (mv-list 5 (firstiter (siga) (expodd)))))
(defund qn-1 () (mv-nth 2 (mv-list 5 (firstiter (siga) (expodd)))))
(defund q-1 () (mv-nth 3 (mv-list 5 (firstiter (siga) (expodd)))))
(defund i-1 () (mv-nth 4 (mv-list 5 (firstiter (siga) (expodd)))))

(defund qp-1 () (bits 0 53 0))

(defund expinc-1 () (logand (expinc-0) (log= (qn-1) 0)))

;; Number of iterations, as determined by data format:

(defund n ()
  (case (fnum)
    (2 (bits 27 4 0))
    (1 (bits 13 4 0))
    (0 (bits 6 4 0))
    (t 0)))

;; Results of final iteration (outputs of the loop):

(defund q-n () (mv-nth 0 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund rp-n () (mv-nth 2 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund rn-n () (mv-nth 3 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund qp-n () (mv-nth 4 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund qn-n () (mv-nth 5 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund expinc-n () (mv-nth 6 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))

;; Exponent of rounded result:

(defund exprnd () (bits (if1 (expinc-n) (+ (expq) 1) (expq)) 10 0))

;; Shifted final root (required to match division):

(defund qp-shft ()
  (case (fnum)
    (0 (bits (qp-n) 53 42))
    (1 (bits (qp-n) 53 28))
    (t (qp-n))))

(defund qn-shft ()
  (case (fnum)
    (0 (bits (qn-n) 53 42))
    (1 (bits (qn-n) 53 28))
    (t (qn-n))))

;; Assimilated truncated root, incremented root, and sticky bit:

(defund qtrunc () (mv-nth 0 (mv-list 3 (computeq (qp-shft) (qn-shft) (rp-n) (rn-n) (fnum) (true$)))))
(defund qinc () (mv-nth 1 (mv-list 3 (computeq (qp-shft) (qn-shft) (rp-n) (rn-n) (fnum) (true$)))))
(defund stk () (mv-nth 2 (mv-list 3 (computeq (qp-shft) (qn-shft) (rp-n) (rn-n) (fnum) (true$)))))

;; Outputs of rounder:

(defund qrnd () (mv-nth 0 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))
(defund inx () (mv-nth 1 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))
(defund qrndden () (mv-nth 2 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))
(defund inxden () (mv-nth 3 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))

;; Final results derived from rounder outputs:

(defund data-final () (mv-nth 0 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) 0 (exprnd) (rmode) (fzp) (fnum) (flags-a)))))
(defund flags-final () (mv-nth 1 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) 0 (exprnd) (rmode) (fzp) (fnum) (flags-a)))))

;; Selection of final results:

(defund data ()
  (if1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                  (log= (classa) 2))
                         (log= (classa) 3))
                (signa))
       (data-special)
       (if1 (logand1 (log= (classa) 4) (log= (mana) 0))
            (d-sqrtpow2)
            (data-final))))

(defund flags ()
  (if1 (logior1 (logior1 (logior1 (logior1 (log= (classa) 0) (log= (classa) 1))
                                  (log= (classa) 2))
                         (log= (classa) 3))
                (signa))
       (flags-special)
       (if1 (logand1 (log= (classa) 4) (log= (mana) 0))
            (flags-sqrtpow2)
            (flags-final))))

;; The above constant definitions are based closely on the definition of fsqrt64 so that
;; the proof of the following is trivial:

(defthmd fsqrt64-lemma
  (mv-let (data flags) (fsqrt64 (opa) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

(defthm fsqrt64-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec)))))

;; The following will be an immediate consequence of the two preceding results:

(defthmd lemma-to-be-functionally-instantiated
  (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
         (fmtw (+ 1 (expw f) (sigw f)))
         (dnp (bitn (rin) 25))
         (fzp (bitn (rin) 24))
         (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fsqrt64 (opa) (fnum) fzp dnp rmode)
      (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) f)
        (and (equal data data-spec)
             (equal (logior (rin) flags) r-spec))))))

;; The desired theorem is then derived by functional instantiation.

;;--------------------------------------------------------------------------------------------

;; We also define sequences of values (q j), (rp j), (rn j), (qp j), and (qn j),
;; representing the root digits, partial remainders, and partial roots,
;; as a set of mutually recursive functions, as they are computed by fsqrt64-loop-0:

(mutual-recursion

(defund q (j)
  (declare (xargs :measure (* 2 (nfix j))))
  (if (or (zp j) (= j 1))
      (q-1)
    (nextdigit (rp (1- j)) (rn (1- j)) (i (1- j)) (1- j))))

(defund i (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (zp j)
      8
    (if (= j 1)
        (i-1)
      (if1 (log= (1- j) 1)
           (+ (i (1- j)) (q j))
	 (i (1- j))))))

(defund rp (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rp-1)
    (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (qp (1- j)) (qn (1- j)) (q j) (1- j) (fnum))))))

(defund rn (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rn-1)
    (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (qp (1- j)) (qn (1- j)) (q j) (1- j) (fnum))))))

(defund qp (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (qp-1)
    (mv-nth 0 (mv-list 2 (nextroot (qp (1- j)) (qn (1- j)) (q j) (1- j))))))

(defund qn (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (qn-1)
    (mv-nth 1 (mv-list 2 (nextroot (qp (1- j)) (qn (1- j)) (q j) (1- j))))))
)

(defund expinc (j)
  (if (or (zp j) (= j 1))
      (expinc-1)
    (logand (expinc (1- j))
            (if1 (log< (1- j) (- (n) 1))
                 (log= (q j) 0)
                 (if1 (log= (fnum) 1)
                      (log= (q j) -2)
                      (log= (q j) -1))))))

;; The constants (rp-n), etc., defined above are related to these functions as follows:

(defthm q-n-rewrite
  (equal (q-n) (q (n))))

(defthm qp-n-rewrite
  (equal (qp-n) (qp (n))))

(defthm qn-n-rewrite
  (equal (qn-n) (qn (n))))

(defthm rp-n-rewrite
  (equal (rp-n) (rp (n))))

(defthm rn-n-rewrite
  (equal (rn-n) (rn (n))))

(defthm expinc-n-rewrite
  (equal (expinc-n) (expinc (n))))


;;********************************************************************************************
;; Special Cases
;;********************************************************************************************

;; The special cases of a zero, infinity, NaN, or negative operand are handled separately:

(defund specialp ()
  (or (member (classa) '(0 1 2 3))
      (= (signa) 1)))

(defthm specialp-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) (f))
      (implies (specialp)
               (and (equal (data) data-spec)
                    (equal (logior (rin) (flags)) r-spec))))))


;;********************************************************************************************
;; Normalization of Operands
;;********************************************************************************************

;; Formatted operand is in lower bits of input:

(defund fmtw () (+ 1 (expw (f)) (sigw (f))))

(defund opaw () (bits (opa) (1- (fmtw)) 0))

;; Operand fields:

(defthmd spec-fields
  (implies (not (specialp))
           (and (equal (sgnf (opaw) (f)) (signa))
	        (equal (expf (opaw) (f)) (expa))
		(equal (manf (opaw) (f)) (mana)))))

;; Operand is either normal or denormal:

(defthm spec-class
  (implies (not (specialp))
           (or (normp (opaw) (f))
	       (denormp (opaw) (f))))
  :rule-classes ())

;; Operand value:

(defund a () (decode (opaw) (f)))

;; Precision:

(defund p () (prec (f)))

;; Leading zero counter used in normalization:

(defthmd clz-expo
  (implies (and (bvecp s 53) (> s 0))
           (equal (clz53 s) (- 52 (expo s)))))

;; Significand:

(defthmd siga-rewrite
  (implies (not (specialp))
	   (equal (siga) (* (expt 2 52) (sig (a))))))

;; Shifted exponent:

(defthmd si-expshft
  (implies (not (specialp))
	   (equal (si (expshft) 13)
	          (+ (expo (a)) (bias (f))))))

;; Predicted result exponent:

(defthmd expq-rewrite
  (implies (not (specialp))
           (equal (expq)
	          (fl (/ (+ (si (expshft) 13) (bias (f))) 2)))))


;;********************************************************************************************
;; Algorithm
;;********************************************************************************************

;; Prescaled radicand:

(defund x ()
  (if (specialp)
      1/4
      (if (evenp (si (expshft) 13))
          (/ (sig (a)) 2)
        (/ (sig (a)) 4))))

(defthm x-bounds
  (and (>= (x) 1/4)
       (< (x) 1))
  :rule-classes ())

(defthmd a-x
  (implies (not (specialp))
           (equal (a)
	          (* (expt 2 (* 2 (1+ (- (expq) (bias (f))))))
		     (x)))))

;; Partial roots:

(defund quot (j)
  (if (zp j)
      1
    (+ (quot (1- j))
       (* (expt 4 (- j)) (q j)))))

(defthmd int-quot
  (implies (natp j)
           (integerp (* (expt 4 j) (quot j)))))

;; Partial remainders:

(defund r (j)
  (* (expt 4 j)
     (- (x) (* (quot j) (quot j)))))

;; Partial remainder recurrence relation:

(defthmd r0-rewrite
  (equal (r 0) (1- (x)))
  :hints (("Goal" :in-theory (enable quot r))))

(defthmd r-recurrence
  (implies (natp j)
           (equal (r (+ 1 j))
                  (- (* 4 (r j))
                     (* (q (1+ j))
		        (+ (* 2 (quot j))
			   (* (expt 4 (- (1+ j)))
			      (q (1+ j)))))))))

;; The final quotient and remainder:

(defund quotf () (quot (n)))

(defund rf () (r (n)))

;; Remainder bounds:

(defund blo (j)
  (- (* 4/9 (expt 4 (- j)))
     (* 2 2/3 (quot j))))

(defund bhi (j)
  (+ (* 4/9 (expt 4 (- j)))
     (* 2 2/3 (quot j))))

;; Our objective in the selection of quotient digits is to ensure that |R_j| lies between
;; these bounds.  This holds trivially for j = 0:

(defthmd r0-bounds
  (and (<= (blo 0) (r 0))
       (>= (bhi 0) (r 0))))

;; The remainder bounds ensure convergence of partial roots:

(defthm r-bounds
  (implies (natp j)
           (iff (and (<= (expt (- (quot j) (* 2/3 (expt 4 (- j)))) 2)
                         (x))
                     (>= (expt (+ (quot j) (* 2/3 (expt 4 (- j)))) 2)
                         (x)))
                (and (<= (blo j) (r j))
		     (>= (bhi j) (r j)))))
  :rule-classes ())

;; Invariance of the bounds on the partial root is ensured by computing an approximation
;; a of 4*R_j and comparing it to a set of "selection constants".

;; The approximation:

(defund rp4 (j) (bits (ash (rp j) 2) 58 0))

(defund rn4 (j) (bits (ash (rn j) 2) 58 0))

(defund rs8 (j)
  (bits (+ (+ (bits (rp4 j) 58 51)
              (lognot (bits (rn4 j) 58 51)))
           (logior1 (bitn (rp4 j) 50)
                    (lognot1 (bitn (rn4 j) 50))))
        7 0))

(defund rs7 (j) (bits (rs8 j) 7 1))

(defund approx (j)
  (if (zp j)
      (* 4 (r 0))
    (* 1/8 (si (rs7 j) 7))))

;; The selection constants:

(defun digtab (i j k)
  (case i
    (0 (case k
         (2 12)
         (1 4)
         (0 -4)
         (-1 (if (= j 1) -11 -12))))
    (1 (case k
         (2 (if (= j 2) 15 13))
         (1 4)
         (0 -4)
         (-1 -13)))
    (2 (case k
         (2 15)
         (1 4)
         (0 -4)
         (-1 -15)))
    (3 (case k
         (2 16)
         (1 6)
         (0 -6)
         (-1 -16)))
    (4 (case k
         (2 18)
         (1 6)
         (0 -6)
         (-1 -18)))
    (5 (case k
         (2 20)
         (1 8)
         (0 -6)
         (-1 -20)))
    (6 (case k
         (2 20)
         (1 8)
         (0 -8)
         (-1 -20)))
    (7 (case k
         (2 22)
         (1 8)
         (0 -8)
         (-1 -22)))
    (8 (case k
         (2 24)
         (1 8)
         (0 -8)
         (-1 (if (= j 0) -20 -24))))))

(defun m (i j k)
  (/ (digtab i j k) 8))

;; The root digit (1 (1+ j)) is selected as the maximum k that dies not exceed
;; (approx j):

(defund maxk (a i j)
  (cond ((<= (m i j 2) a) 2)
        ((<= (m i j 1) a) 1)
        ((<= (m i j 0) a) 0)
        ((<= (m i j -1) a) -1)
        (t -2)))

;; The following invariant is established by induction:

(defund approx-bounds (j k)
  (and (implies (< (approx j) (m (i j) j k))
                (< (* 4 (r j)) (m (i j) j k)))
       (implies (>= (approx j) (m (i j) j k))
                (> (* 4 (r j)) (- (m (i j) j k) 1/32)))))

(defund approx-inv (j)
  (and (= (q (1+ j)) (maxk (approx j) (i j) j))
       (approx-bounds j 2)
       (approx-bounds j 1)
       (approx-bounds j 0)
       (approx-bounds j -1)))

(defund r-bnds-inv (j)
  (and (<= (blo j) (r j))
       (>= (bhi j) (r j))))

(defund quot-bnds-inv (j)
  (and (<= 1/2 (quot j))
       (>= 1 (quot j))))

(defund qpn-inv (j)
  (and (= (* (expt 2 54) (1- (quot j)))
          (- (qp j) (qn j)))
       (= (bits (qp j) (- 53 (* 2 j)) 0) 0)
       (= (bits (qn j) (- 53 (* 2 j)) 0) 0)))

(defund rpn-inv (j)
  (and (integerp (* (expt 2 55) (r j)))
       (= (mod (* (expt 2 55) (r j)) (expt 2 59))
          (mod (- (rp j) (rn j)) (expt 2 59)))
       (= (bits (rp j) (- 52 (p)) 0) 0)
       (= (bits (rn j) (- 52 (p)) 0) 0)))

(defund inv (j)
  (and (r-bnds-inv j)
       (quot-bnds-inv j)
       (or (zp j)
           (and (approx-inv (1- j))
                (qpn-inv j)
                (rpn-inv j)))))

(defthmd inv-lemma
  (implies (and (not (specialp))
                (natp j)
		(<= j (n)))
           (inv j)))


;;********************************************************************************************
;; Quotient Computation
;;********************************************************************************************

;; The rounder produces a rounding of the square root of x, which is related to the
;; desired result as follows:

(defthmd sqrt-a-x
  (implies (not (specialp))
           (equal (qsqrt (a) (1+ (* 2 (n))))
                  (* (expt 2 (1+ (- (expq) (bias (f)))))
                     (qsqrt (x) (1+ (* 2 (n))))))))

;; The erros bound for the final root is dereived by instanting the inductive invariant:

(defthmd quotf-error-a
  (implies (not (specialp))
           (and (<= (expt (- (quotf) (* 2/3 (expt 4 (- (n))))) 2)
	           (x))
                (>= (expt (+ (quotf) (* 2/3 (expt 4 (- (n))))) 2)
	           (x)))))

(defthmd quotf-error-b
  (implies (not (specialp))
           (< (abs (- (qsqrt (x) (1+ (* 2 (n))))
	              (quotf)))
	      (expt 2 (- (* 2 (n)))))))

;; Upper bounds on the square root and the final approximation:

(defthmd qsqrt-x-upper
  (implies (not (specialp))
           (< (qsqrt (x) (1+ (* 2 (n))))
	      (- 1 (expt 2 (- (1+ (p))))))))

(defthmd quotf-upper
  (implies (not (specialp))
	   (<= (quotf)
	       (- 1 (expt 2 (- (1+ (p))))))))

;; Truncated absolute value of quotient:

(defthmd qtrunc-rewrite
  (implies (not (specialp))
           (equal (mod (qtrunc) (expt 2 (p)))
	          (mod (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) (expt 2 (p))))))

;; Incremented absolute value of quotient:

(defthmd qinc-rewrite
  (implies (not (specialp))
           (equal (mod (qinc) (expt 2 (p)))
	          (mod (+ (fl (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n)))))) 2) (expt 2 (p))))))

;; Sticky bit:

(defthmd stk-rewrite
  (implies (not (specialp))
	   (equal (stk)
	          (if (integerp (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))))
		      0 1))))

;;********************************************************************************************
;; Rounding
;;********************************************************************************************

;; Rounding mode determined by the encoding rmode:

(defund mode ()
  (case (rmode)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

;; Exactness and rounding of square root of x:

(defthmd inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (exactp (qsqrt (x) (1+ (* 2 (n)))) (p))
		      0 1))))

(defthmd rnd-qsqrt-qrnd
  (implies (not (specialp))
           (equal (mod (rnd (* (expt 2 (1+ (p))) (qsqrt (x) (1+ (* 2 (n))))) (mode) (p)) (expt 2 (p)))
	          (* 2 (bits (qrnd) (- (p) 2) 0)))))

;; Equivalent conditions for rounding up to a power of 2:

(defthmd rnd-1-rup-xmax
  (implies (not (specialp))
           (iff (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	               1)
	        (and (equal (mode) 'rup)
                     (equal (x) (- 1 (expt 2 (- (p)))))))))

(defthmd rnd-1-rup-qmax
  (implies (not (specialp))
           (iff (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	               1)
	        (and (equal (mode) 'rup)
	             (equal (quotf) (- 1 (expt 2 (- (1+ (p))))))))))

(defthmd rup-expinc
  (implies (not (specialp))
           (equal (expinc (n))
	          (if (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	                     1)
	              1 0))))

;; Exponent of rounded result:

(defthmd exprnd-rewrite
  (implies (not (specialp))
           (equal (exprnd)
	          (if (equal (rnd (qsqrt (x) (1+ (* 2 (n)))) (mode) (p))
	                     1)
		      (1+ (expq))
		    (expq)))))

;; Exactness and rounding of square root of A:

(defthmd rnd-inx-rewrite
  (implies (not (specialp))
           (equal (inx)
	          (if (= (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
		         (qsqrt (a) (1+ (* 2 (n)))))
		      0 1))))

(defthmd rnd-qsqrt-a
  (implies (not (specialp))
           (equal (rnd (qsqrt (a) (1+ (* 2 (n)))) (mode) (p))
	          (* (expt 2 (- (exprnd) (+ (bias (f)) (1- (p)))))
		     (+ (expt 2 (1- (p))) (bits (qrnd) (- (p) 2) 0))))))


;;********************************************************************************************
;; Final Result
;;********************************************************************************************

(defthm fsqrt64-main
  (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
    (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) (f))
      (and (equal (data) data-spec)
           (equal (logior (rin) (flags)) r-spec)))))

(defthmd lemma-to-be-functionally-instantiated
  (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
         (fmtw (+ 1 (expw f) (sigw f)))
         (dnp (bitn (rin) 25))
         (fzp (bitn (rin) 24))
         (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fsqrt64 (opa) (fnum) fzp dnp rmode)
      (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) f)
        (and (equal data data-spec)
             (equal (logior (rin) flags) r-spec))))))

(defthm fsqrt64-correct
  (implies (input-constraints opa fnum rin)
           (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (dnp (bitn rin 25))
                  (fzp (bitn rin 24))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fsqrt64 opa fnum fzp dnp rmode)
               (let ((r (logior rin flags)))
                 (mv-let (data-spec r-spec)
                         (arm-sqrt-spec (bits opa (1- fmtw) 0) rin f)
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ())
