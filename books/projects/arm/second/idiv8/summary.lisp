(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "idiv8")

(local (include-book "post"))

;;*******************************************************************************
;; Objective
;;*******************************************************************************

;; We impose the following constraints on the inputs of fdiv64:

(defund input-constraints (opa opb int32 sgnd)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (bitp int32)
       (bitp sgnd)))

(defund opval (op int32 sgnd)
  (if1 int32
       (if1 sgnd
            (si (bits op 63 32) 32)
	  (bits op 63 32))
     (if1 sgnd
          (si op 64)
	op)))

(defund iquot (a b)
  (if (>= (/ a b) 0)
      (fl (/ a b))
    (cg (/ a b))))

(defund idiv-spec (opa opb int32 sgnd)
  (let* ((a (opval opa int32 sgnd))
         (b (opval opb int32 sgnd))
	 (i (iquot a b)))
    (if (= b 0)
        0
      (bits i 63 0))))

;; Our ultimate objective is the following theorem:

;; (defthm idiv8-correct
;;   (implies (input-constraints opa opb int32 sgnd)
;;            (equal (fdiv64 opa opb int32 sgnd)
;;                   (idiv-spec opa opb int32 sgnd))))

;; In order to address the lack of modularity of the ACL2 code, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate (((opa) => *) ((opb) => *) ((int32) => *) ((sgnd) => *))
  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun int32 () 0))
  (local (defun sgnd () 0))
  (defthm input-constraints-lemma
    (input-constraints (opa) (opb) (int32) (sgnd))
    :rule-classes ()))

;; In terms of the constrained constants, we shall define constants corresponding to 
;; the local variables of idiv8, culminating in the constant (data), corresponding 
;; to the output.

;; The constant definitions will be derived from that of idiv8 in such a way that 
;; the proof of the following will be trivial:

;; (defthm idiv8-lemma
;;   (equal (data) (idiv8 (opa) (opb) (int32) (sgnd))))

;; The real work will be the proof of the following theorem:

;; (defthm idiv8-main
;;   (equal (data) (idiv-spec (opa) (opb) (int32) (sgnd)))
;;   :rule-classes ())

;; The following is an immediate consequence of the two preceding results:

;; (defthmd lemma-to-be-functionally-instantiated
;;   (equal (idiv8 (opa) (opb) (int32) (sgnd))
;;          (idiv-spec (opa) (opb) (int32) (sgnd))))

;; The desired theorem can then be derived by functional instantiation.

;;*******************************************************************************
;; idiv8-lemma
;;*******************************************************************************

(defund sgna () (logand1 (sgnd) (bitn (opa) 63)))
(defund sgnb () (logand1 (sgnd) (bitn (opb) 63)))
(defund sgnq () (logxor (sgna) (sgnb)))

(defund bgta () (compareops (opa) (opb) (sgna) (sgnb) (int32)))

(defund mska () (if1 (int32) (setbits (opa) 64 31 0 0) (opa)))
(defund mskb () (if1 (int32) (setbits (opb) 64 31 0 0) (opb)))
(defund nega () (bits (+ (lognot (mska)) 1) 63 0))
(defund negb () (bits (+ (lognot (mskb)) 1) 63 0))
(defund absa () (bits (if1 (sgna) (nega) (mska)) 63 0))
(defund absb () (bits (if1 (sgnb) (negb) (mskb)) 63 0))

(defund clza () (clz64 (absa)))
(defund clzb () (clz64 (absb)))

(defund del () (- (clzb) (clza)))

(defund bitsmod6 () (rem (del) 6))

(defund c ()
  (if1 (log= (bitsmod6) 0)
       (floor (del) 6)
       (+ 1 (floor (del) 6))))

(defund only1iter () (log<= (del) 3))

(defund skipiter ()
  (logand1 (logand1 (lognot1 (only1iter))
                    (log< 0 (bitsmod6)))
           (log<= (bitsmod6) 3)))

(defund k ()
  (case (rem (del) 3)
    (0 0)
    (1 2)
    (2 1)
    (t 0)))

(defund div () (bits (ash (absb) (+ (clzb) 3)) 70 0))

(defund div2 () (bits (ash (div) 1) 70 0))

(defund div3 () (bits (+ (div) (div2)) 70 0))

(defund cmpconst () (computecmpconst (bits (div) 65 60)))

(defund rp-1 () (bits (ash (absa) (+ (clza) 3)) 70 0))

(defund rs10-0 () (bits (rp-1) 70 61))

(defund gep2 () (bits (+ (rs10-0) (ag 5 (cmpconst))) 10 0))

(defund q-1 () 
  (if1 (bitn (gep2) 10) 2 1))

(defund rn-1 () 
  (if1 (bitn (gep2) 10) (div2) (div)))

(defund quot-1 () 
  (if1 (sgnq) (bits (- (q-1)) 64 0) (bits (q-1) 64 0)))

(defund quotm-1 () 
  (if1 (sgnq) (bits (- (- (q-1)) 1) 64 0) (bits (- (q-1) 1) 64 0)))

(defund quotp-1 () (bits 0 64 0))

(defund rs10-1 ()
  (bits (+ (+ (bits (rp-1) 67 58)
              (lognot (bits (rn-1) 67 58)))
           1)
        9 0))

(defund rpf ()
  (mv-nth 5 (mv-list 11
    (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                   (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1)))))

(defund rnf ()
  (mv-nth 6 (mv-list 11
    (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                   (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1)))))

(defund quotf ()
  (mv-nth 8 (mv-list 11
    (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                   (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1)))))

(defund quotmf ()
  (mv-nth 9 (mv-list 11
    (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                   (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1)))))

(defund quotpf ()
  (mv-nth 10 (mv-list 11
    (idiv8-loop-1 1 (only1iter) (skipiter) (c) (cmpconst) (div) (div3) (int32) (sgnq) (k) (q-1) 0 0 0 0
                   (rp-1) (rn-1) (rs10-1) (quot-1) (quotm-1) (quotp-1)))))

(defund islost () (log<> (logand (si (quotf) 65) (- (ash 1 (k)) 1)) 0))

(defund quot0 () (bits (ash (si (quotf) 65) (- (k))) 63 0))

(defund quotm0 () (bits (ash (si (quotmf) 65) (- (k))) 63 0))

(defund quotp0 () (bits (ash (si (quotpf) 65) (- (k))) 63 0))

(defund rdiff () (bits (+ (+ (rpf) (lognot (rnf))) 1) 70 0))

(defund data ()
  (if1 (logior1 (log= (mskb) 0) (bgta))
       (bits 0 63 0)
     (if1 (ispow2 (mskb) (sgnb))
          (divpow2 (bits (if1 (sgnb) (nega) (mska)) 63 0) (sgnq) (bits (lognot (clzb)) 5 0))
        (if1 (log= (clza) (clzb))
             (bits (if1 (sgnq) 18446744073709551615 1) 63 0)
           (if1 (logand1 (sgnq) (logior1 (islost) (bitn (rdiff) 70)))
                (quotp0)
              (if1 (logand1 (logand1 (lognot1 (sgnq)) (lognot1 (islost))) (bitn (rdiff) 70))
                   (quotm0)
                 (quot0)))))))

(defthmd idiv8-lemma
  (equal (data) (idiv8 (opa) (opb) (int32) (sgnd)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(mska mskb sgna sgnb sgnq nega negb absa absb bgta clza clzb del bitsmod6 c only1iter skipiter
	                k div div2 div3 cmpconst rp-1 rn-1 rs10-0 rs10-1 gep2 q-1 quot-1 quotm-1 quotp-1 rpf rnf quotf 
			quotmf quotpf islost quot0 quotm0 quotp0 rdiff data idiv8))))


;;*******************************************************************************
;; Early Exit
;;*******************************************************************************

;; Operand values A and B and their quotient I:

(defund a () (opval (opa) (int32) (sgnd)))

(defund b () (opval (opb) (int32) (sgnd)))

(defund i () (iquot (a) (b)))

;; We replace A and B with 64-bit versions, which have the same quotient:

(defund a0 ()
  (if1 (sgnd)
       (si (mska) 64)
     (mska)))

(defund b0 ()
  (if1 (sgnd)
       (si (mskb) 64)
     (mskb)))

(defthmd i-rewrite
  (equal (i) (iquot (a0) (b0))))

;; Early exit occurs in the following cases:
;;  (1) B = 0
;;  (2) |B| > |A|
;;  (3) |B| is a power of 2
;;  (4) expo(A) = expo(B)

(defthmd b-mskb-0
  (iff (= (b) 0)
       (= (mskb) 0)))

(defthmd bgta-rewrite
  (equal (bgta)
         (if (> (abs (b)) (abs (a)))
             1 0)))

(defthmd ispow2-pow2
  (equal (ispow2 (mskb) (sgnb))
	 (if (or (= (b0) (expt 2 (expo (b0))))
	         (= (b0) (- (expt 2 (expo (b0))))))
	     1 0)))

(defthmd clza-rewrite
  (implies (not (= (a) 0))
           (equal (clza) (- 63 (expo (a0))))))

(defthmd clzb-rewrite
  (implies (not (= (b) 0))
           (equal (clzb) (- 63 (expo (b0))))))
	     
(defund earlyp ()
   (or (= (mskb) 0)
       (= (bgta) 1)
       (= (ispow2 (mskb) (sgnb)) 1)
       (= (clza) (clzb))))

(defthmd early-case
  (implies (earlyp)
           (equal (data)
	          (if (= (b) 0)
		      0
		    (bits (i) 63 0)))))

;;*******************************************************************************
;; idiv8-loop-1
;;*******************************************************************************

;; The number of SRT iterations: 

(defund n () (1+ (cg (/ (del) 3))))

;; Iteration j occurs as the first iteration of a cycle in the following cases:

(defund it1 (j)
  (and (> j 1)
       (or (= j (1- (n)))
	   (= (n) 2)
	   (and (< j (1- (n)))
		(= (mod j 2) 0)))))

;; We define the sequences of values (q j), (rp j), (rn j), (quot j), etc., as a
;; set of mutually recursive functions, as they are computed by idiv8-loop-1:

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
    (if (it1 j)
        (computers11 (rp (1- j)) (rn (1- j)) (q j) (divsigned j) (div3signed j))
      (rs11 (1- j)))))

(Defund rp (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rp-1)
    (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (bitn (rs10 (1- j)) 9) (q j) (divsigned j) (div3signed j) (int32))))))

(defund rn (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rn-1)
    (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (bitn (rs10 (1- j)) 9) (q j) (divsigned j) (div3signed j) (int32))))))

(defund rs10 (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (zp j)
      (rs10-0)
    (if (= j 1)
        (rs10-1)
      (if (it1 j)
          (bits (+ (+ (bits (rp j) 67 58) (lognot (bits (rn j) 67 58))) 1) 9 0)
        (computers10 (divsigned j) (div3signed j) (q j) (rs11 (1- j)))))))

(defund quot (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (quot-1)
    (mv-nth 0 (mv-list 2 (nextquot (sgnq) (q j) (quot (1- j)) (quotm (1- j)))))))

(defund quotm (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      (quotm-1)
    (mv-nth 1 (mv-list 2 (nextquot (sgnq) (q j) (quot (1- j)) (quotm (1- j)))))))

(defund qlast (j)
  (declare (xargs :measure (1+ (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (q j)
      (qlast (1- j)))))

(defund quotlast (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
	(quot (1- j))
      (quotlast (1- j)))))

(defund quotmlast (j)
  (declare (xargs :measure (* 3 (nfix j))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (quotm (1- j))
      (quotmlast (1- j)))))

(defund quotp (j)
  (declare (xargs :measure (+ 2 (* 3 (nfix j)))))
  (if (or (zp j) (= j 1))
      0
    (if (it1 j)
        (bits (+ (quot j) (ash 1 (k))) 64 0)
      (incquot (sgnq) (q j) (quot (1- j)) (quotm (1- j)) (qlast j) (quotlast j) (quotmlast j) (k)))))

)

;; The constants (rpf), etc., are related to the above functions as follows:

(defthmd rpf-rewrite
  (implies (not (earlyp))
           (equal (rpf) (rp (n)))))

(defthmd rnf-rewrite
  (implies (not (earlyp))
           (equal (rnf) (rn (n)))))

(defthmd quotf-rewrite
  (implies (not (earlyp))
           (equal (quotf) (quot (n)))))

(defthmd quotmf-rewrite
  (implies (not (earlyp))
           (equal (quotmf) (quotm (n)))))

(defthmd quotpf-rewrite
  (implies (not (earlyp))
           (equal (quotpf) (quotp (n)))))

;;*******************************************************************************
;; Instantiation of SRT Algorithm
;;*******************************************************************************

;; Normalized divisor and dividend:

(defund d () (* (expt 2 (- (clzb) 64)) (abs (b0))))

(defund x () (* (expt 2 (- (clza) 64)) (abs (a0))))

(defthmd d-sig-b
  (implies (not (earlyp))
	   (equal (d) (/ (sig (b0)) 2))))

(defthmd x-sig-a
  (implies (not (earlyp))
	   (equal (x) (/ (sig (a0)) 2))))

(defthmd d-bounds
  (implies (not (earlyp))
           (and (<= 1/2 (d))
	        (< (d) 1))))

(defthmd x-bounds
  (implies (not (earlyp))
           (and (<= 1/2 (x))
	        (< (x) 1))))

;; x and d are related to a0 and b0 as follows:

(defthmd quotient-x-d
  (implies (not (earlyp))
           (equal (abs (/ (a0) (b0)))
	          (* (expt 2 (del))
		     (/ (x) (d))))))

;; Now that x, d, and q_j are defined, the partial quotients and remainders are defined
;; as in Chapter 10:

(defund quotient (j)
  (if (zp j)
      0
    (+ (quotient (1- j))
       (* (expt 8 (- 1 j)) (q j)))))

(defund r (j)
  (* (expt 8 (1- j))
     (- (x) (* (d) (quotient j)))))
          
(defthmd r0-rewrite
  (equal (r 0) (/ (x) 8)))

(defthmd r-recurrence
  (implies (natp j)
           (equal (r (+ 1 j))
                  (- (* 8 (r j))
                     (* (q (1+ j)) (d))))))

(defthmd r0-bound
  (implies (not (earlyp))
           (< (abs (r 0)) (* 4/7 (d)))))

;; The function computecmpconst computes the comparison constants of Section 10.3:

(defun m (k i)
  (- (* 1/64 (si (ag (+ k 3) (computecmpconst i)) 10))))

(defthmd m-md8
  (implies (and (integerp k) (<= -3 k) (<= k 4)
                (bvecp i 6))
           (equal (m k i) (md8 k i))))

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

(defthmd maxk-select-digit-d8
  (implies (and (not (earlyp)) (rationalp a))
           (equal (maxk a) (select-digit-d8 a (i64 (d))))))

;; Approximation of the partial remainder:

(defund approx (j)
  (/ (si (rs10 j) 10) 64))

;; Precision of operands:

(defund p () (if1 (int32) 32 64))

;; The following is derived as a functional instance of the theorem of Section 10.3:

(defthmd r-bound-inv
  (implies (and (not (earlyp))
                (natp j)
                (<= (abs (r j)) (* 4/7 (d)))
                (rationalp approx)
                (integerp (* 64 approx))
                (< (abs (- approx (* 8 (r j)))) 1/64)
                (= (q (1+ j)) (maxk approx)))
	   (<= (abs (r (1+ j))) (* 4/7 (d)))))

;; The following is proved by induction:

(defthmd induction-result
  (implies (and (not (earlyp))
                (not (zp j))
		(<= j (n)))
           (and (= (q j) (maxk (approx (1- j))))
                (< (abs (- (approx (1- j)) (* 8 (r (1- j))))) 1/64)
                (<= (abs (r j)) (* 4/7 (d)))
                (bvecp (rp j) 71)
                (bvecp (rn j) 71)
                (= (mod (* (expt 2 67) (r j)) (expt 2 71)) (mod (- (rp j) (rn j)) (expt 2 71)))
                (= (bits (rp j) (- 63 (p)) 0) 0)
                (= (bits (rn j) (- 63 (p)) 0) 0))))

;; In particular, we have the following:

(defund qf () (quotient (n)))

(defund rf () (r (n)))

(in-theory (disable (qf) (rf)))

(defthmd rf-bound
  (implies (not (earlyp))
           (<= (abs (rf)) (* 4/7 (d)))))

(defthmd rf-rpf-rnf
  (implies (not (earlyp))
           (equal (mod (* (expt 2 67) (rf)) (expt 2 71))
   	          (mod (- (rpf) (rnf)) (expt 2 71)))))

(defthmd bvecp-rpf-rnf
  (implies (not (earlyp))
           (and (bvecp (rpf) 71)
	        (bvecp (rnf) 71))))

;; Quotient Computation

(defthmd quotf-pos
  (implies (and (not (earlyp))
		(= (sgnq) 0))
	   (and (bvecp (quotf) 65)
	        (bvecp (quotmf) 65)
                (equal (quotf) (* (expt 8 (1- (n))) (qf)))
		(equal (quotmf) (1- (quotf))))))

(defthmd quotf-neg
  (implies (and (not (earlyp))
		(= (sgnq) 1))
	   (and (bvecp (quotf) 65)
	        (bvecp (quotmf) 65)
                (equal (quotf) (- (expt 2 65) (* (expt 8 (1- (n))) (qf))))
		(equal (quotmf) (1- (quotf))))))

(defthmd quotpf-sgnq=0
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 0))
	   (equal (quotpf)
	          (+ (* (expt 8 (1- (n))) (qf))
		     (expt 2 (k))))))

(defthmd quotpf-sgnq=1
  (implies (and (not (earlyp))
                (> (n) 2)
		(= (sgnq) 1))
	   (equal (quotpf)
	          (+ (expt 2 65)
		     (- (* (expt 8 (1- (n))) (qf)))
		     (expt 2 (k))))))

;;*******************************************************************************
;; Post-Processing
;;*******************************************************************************

;; Error bound on final quotient:

(defthmd q-error
  (implies (not (earlyp))
           (<= (abs (- (/ (x) (d)) (qf)))
	       (* 4/7 (expt 8 (- (1- (n))))))))

;; Signed quotient:

(defund quotsgn () (if1 (sgnq) (- (qf)) (qf)))

;; Computed quotient, decremented quotient, and incremented quotient:

(defthmd si-quotf-rewrite
  (implies (not (earlyp))
           (equal (si (quotf) 65)
	          (* (expt 8 (1- (n))) (quotsgn)))))

(defthmd si-quotmf-rewrite
  (implies (not (earlyp))
           (equal (si (quotmf) 65)
	          (1- (si (quotf) 65)))))

(defthmd si-quotpf-rewrite
  (implies (and (not (earlyp))
                (not (= (qf) 1/2)))
           (equal (si (quotpf) 65)
	          (+ (expt 2 (k)) (si (quotf) 65)))))

;; Relationship between integer quotient and computed quotient:

(defthmd a-b-q-pos
  (implies (and (not (earlyp))
                (= (sgnq) 0))
	   (equal (i)
	          (if (and (integerp (* (expt 2 (del)) (qf)))
		           (< (rf) 0))
		      (1- (fl (* (expt 2 (del)) (quotsgn))))
		    (fl (* (expt 2 (del)) (quotsgn)))))))

(defthmd a-b-q-neg
  (implies (and (not (earlyp))
                (= (sgnq) 1))
	   (equal (i)
	          (if (and (integerp (* (expt 2 (del)) (qf)))
		           (>= (rf) 0))
		      (fl (* (expt 2 (del)) (quotsgn)))
		    (1+ (fl (* (expt 2 (del)) (quotsgn))))))))

;; Final result:

(defthmd idiv8-main
  (equal (data) (idiv-spec (opa) (opb) (int32) (sgnd))))

(defthmd lemma-to-be-functionally-instantiated
  (equal (idiv8 (opa) (opb) (int32) (sgnd))
         (idiv-spec (opa) (opb) (int32) (sgnd))))

(defthmd idiv8-correct
  (implies (input-constraints opa opb int32 sgnd)
           (equal (idiv8 opa opb int32 sgnd)
                  (idiv-spec opa opb int32 sgnd))))




