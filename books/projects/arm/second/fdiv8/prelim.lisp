(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)|
                          |(mod (+ x (mod a b)) y)| simplify-products-gather-exponents-equal mod-cancel-*-const
			  cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)| |(equal x (if a b c))|
			  |(equal (if a b c) x)| |(logior 1 x)| MOD-THEOREM-ONE-B |(mod (- x) y)|))

(include-book "fdiv8")

;; We impose the following constraints on the inputs of fdiv8:

(defund input-constraints (opa opb fnum rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

;; (defthm fdiv8-correct
;;   (implies (input-constraints opa opb fnum rin)
;;            (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
;;                   (fmtw (+ 1 (expw f) (sigw f)))
;;                   (dnp (bitn rin 25))
;;                   (fzp (bitn rin 24))
;;                   (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (fdiv8 opa opb fnum fzp dnp rmode)
;;                (let ((r (logior rin flags)))         
;;                  (mv-let (data-spec r-spec)
;;                          (arm-binary-spec 'div (bits opa (1- fmtw) 0) (bits opb (1- fmtw) 0) rin f)
;;                    (and (equal data data-spec)
;;                         (equal r r-spec))))))))

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

(defthmd fnum-vals
  (member (fnum) '(0 1 2))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))
(defund f () (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))

;; In terms of these constants, we shall define constants corresponding to the local 
;; variables of fdiv8, culminating in the constants (data) and (flags), corresponding to
;; the outputs.

;; The constant definitions will be derived from that of fdiv8 in such a way that 
;; the proof of the following will be trivial:

;; (defthm fdiv8-lemma
;;   (mv-let (data flags) (fdiv8 (opa) (opb) (fnum) (fz) (dn) (rmode))
;;     (and (equal (data) data)
;;          (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

;; (defthm fdiv8-main
;;   (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
;;     (mv-let (data-spec r-spec)
;;             (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
;;       (and (equal (data) data-spec)
;;            (equal (logior (rin) (flags)) r-spec)))
;;   :rule-classes ())

;; The following is an immediate consequence of the two preceding results:

;; (defthmd lemma-to-be-functionally-instantiated
;;   (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
;;          (fmtw (+ 1 (expw (f)) (sigw (f))))
;;          (dnp (bitn (rin) 25))
;;          (fzp (bitn (rin) 24))
;;          (rmode (bits (rin) 23 22)))
;;     (mv-let (data flags) (fdiv8 (opa) (opb) (fnum) fzp dnp rmode)
;;       (let ((r (logior (rin) flags)))         
;;         (mv-let (data-spec r-spec)
;;                 (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
;;           (and (equal data data-spec)
;;                (equal r r-spec)))))))

;; The desired theorem can then be derived by functional instantiation.

;; In this book, we'll define the constants and prove the above fdiv8-lemma.  We'll also 
;; define analogous constants and prove analogous lemmas about the auxiliary functions.

;;*******************************************************************************
;; fdiv8
;;*******************************************************************************

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

(defund sign () (logxor (signa) (signb)))

(defund data-special ()
  (mv-nth 0 (mv-list 2 (specialcase (sign) (opa) (opb) (classa) (classb) (fnum) (dnp) (flags-b)))))
(defund flags-special ()
  (mv-nth 1 (mv-list 2 (specialcase (sign) (opa) (opb) (classa) (classb) (fnum) (dnp) (flags-b)))))

(defund divpow2 () (logand1 (logand1 (log= (classa) 4) (log= (classb) 4)) (log= (manb) 0)))

(defund siga () (mv-nth 0 (mv-list 3 (normalize (expa) (expb) (mana) (manb) (fnum)))))
(defund sigb () (mv-nth 1 (mv-list 3 (normalize (expa) (expb) (mana) (manb) (fnum)))))
(defund expdiff () (mv-nth 2 (mv-list 3 (normalize (expa) (expb) (mana) (manb) (fnum)))))

(defund div () (BITS (ASH (SIGB) 14) 70 0))
(defund div2 () (BITS (ASH (DIV) 1) 70 0))
(defund div3 () (BITS (+ (DIV) (DIV2)) 70 0))

(defund cmpconst () (computecmpconst (bits (div) 65 60)))

(defund sigcmp () (bits (+ (sigb) (bits (lognot (siga)) 52 0)) 53 0))
(defund sigaltsigb () (bitn (sigcmp) 53))

(defund rp-1 ()
  (if1 (sigaltsigb)
       (bits (ash (siga) 15) 70 0)
     (bits (ash (siga) 14) 70 0)))

(defund expq ()
  (if1 (sigaltsigb)
       (bits (- (si (expdiff) 13) 1) 12 0)
     (expdiff)))

(defund rs10-0 () (bits (rp-1) 70 61))

(defund gep2 () (bits (+ (rs10-0) (ag 5 (cmpconst))) 10 0))

(defund q-1 () 
  (if1 (bitn (gep2) 10) 2 1))

(defund quot-1 () 
  (if1 (bitn (gep2) 10) (bits 2 64 0) (bits 1 64 0)))

(defund quotm1-1 () 
  (if1 (bitn (gep2) 10) (bits 1 64 0) (bits 0 64 0)))

(defund rn-1 () 
  (if1 (bitn (gep2) 10) (div2) (div)))

(defund rs10-1 ()
  (bits (+ (+ (bits (rp-1) 67 58)
              (lognot (bits (rn-1) 67 58)))
           1)
        9 0))

(defund c ()
  (case (fnum)
    (2 (bits 9 4 0))
    (1 (bits 4 4 0))
    (0 (bits 2 4 0))
    (t 0)))

(defund lsbis2 () (log<> (fnum) 1))

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

(defund qrnd () (mv-nth 0 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund inx () (mv-nth 1 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund qrndden () (mv-nth 2 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))
(defund inxden () (mv-nth 3 (mv-list 4 (rounder (qtrunc) (qinc) (stk) (sign) (expq) (rmode) (fnum)))))

(defund data-final () (mv-nth 0 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) (sign) (expq) (rmode) (fzp) (fnum) (flags-b)))))
(defund flags-final () (mv-nth 1 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) (sign) (expq) (rmode) (fzp) (fnum) (flags-b)))))

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

(defthmd fdiv8-lemma
  (mv-let (data flags) (fdiv8 (opa) (opb) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(signa expa mana classa flags-a signb expb manb classb flags-b data-special flags-special divpow2 siga
	                sigb expdiff div div2 div3 cmpconst sigcmp sigaltsigb rp-1 rn-1 expq rs10-0 rs10-1 gep2 q-1 rpf
			rnf quotf c	quotm1f quotpf quotm1pf qinc qtrunc stk sign qrnd inx qrndden inxden data-final
			quot-1 quotm1-1 lsbis2 flags-final data flags fdiv8))))

;; It's usually a good idea to disable the executable counterpart of any function that depends
;; on a constrained function:

(in-theory (disable (input-constraints) (signa) (expa) (mana) (classa) (flags-a) (signb) (expb) (manb) (classb) (flags-b)
                    (data-special) (flags-special) (divpow2) (siga) (sigb) (expdiff) (div) (div2) (div3) (cmpconst) (sigcmp)
		    (sigaltsigb) (rp-1) (rn-1) (expq) (rs10-0) (rs10-1) (gep2) (q-1) (c) (rpf) (rnf) (quotpf)
		    (quotm1pf) (quotf) (quotm1f) (qinc) (qtrunc) (stk) (sign) (qrnd) (inx) (qrndden) (inxden)
		    (quot-1) (quotm1-1) (lsbis2) (data-final) (flags-final) (data) (flags) (dnp) (fzp) (rmode) (f)))

;; Let's also disable all the functions defined by the model and enable them only as needed:

(in-theory (disable analyze clz53-loop-0 clz53-loop-1 clz53-loop-2 clz53 computeq rshft64 rounder final specialcase
                    normalize computecmpconst nextdigit nextrem nextquot incquot fdiv8-loop-0 fdiv8-loop-1 computers11
		    computers10 fdiv8
                    (analyze) (clz53-loop-0) (clz53-loop-1) (clz53-loop-2) (clz53) (computeq) (rshft64) (rounder) (final)
		    (specialcase) (normalize) (computecmpconst) (nextdigit) (nextrem) (nextquot) (incquot) (fdiv8-loop-0)
		    (fdiv8-loop-1) (computers11) (computers10) (fdiv8)))


;;*******************************************************************************
;; fdiv8-loop-1
;;*******************************************************************************

;; We define the sequences of values (q j), (rp j), (rn j), (quotp j), (quotm1p j),
;; (quot j), and (quotm1 j) as a set of mutually recursive functions, as they are 
;; computed by fdiv8-loop-1, and prove that the constants (rpf), etc., defined 
;; above are related to these functions as follows:
;;   (equal (rpf) (rp (1+ (* 2 (c)))
;;   (equal (rnf) (rn (1+ (* 2 (c)))
;;   (equal (quotf) (quot (1+ (* 2 (c)))
;;   (equal (quotm1f) (quotm1 (1+ (* 2 (c)))
;;   (equal (quotpf) (quotp (1+ (* 2 (c)))
;;   (equal (quotm1pf) (quotm1p (1+ (* 2 (c)))
;; 

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

(in-theory (disable (q) (divsigned) (div3signed) (rs11) (rp) (rn) (rs10) (quot) (quotm1) (qlast) (quotlast) (quotm1last)
                    (quotp) (quotm1p)))

(defthmd fdiv8-loop-1-1
  (implies (and (natp i)
                (natp j)
                (natp n)
		(<= i n)
		(= (mod j 2) 1))
	   (equal (fdiv8-loop-1 i n (cmpconst) (div) (div3) (fnum) (lsbis2) (q j) (qlast j) (quotlast j) (quotm1last j)
	                         (rs11 j) (rp j) (rn j) (rs10 j) (quotp j) (quotm1p j) (quot j) (quotm1 j))
	          (fdiv8-loop-1 (1+ i) n (cmpconst) (div) (div3) (fnum) (lsbis2) (q (+ 2 j)) (qlast (+ 2 j)) (quotlast (+ 2 j))
		                 (quotm1last (+ 2 j)) (rs11 (+ 2 j)) (rp (+ 2 j)) (rn (+ 2 j)) (rs10 (+ 2 j)) (quotp (+ 2 j))
				 (quotm1p (+ 2 j)) (quot (+ 2 j)) (quotm1 (+ 2 j)))))
  :hints (("Goal" :expand ((fdiv8-loop-1 i n (cmpconst) (div) (div3) (fnum) (lsbis2) (q j) (qlast j) (quotlast j) (quotm1last j)
	                                  (rs11 j) (rp j) (rn j) (rs10 j) (quotp j) (quotm1p j) (quot j) (quotm1 j))
                           (:free (j cmpconst div div3 fnum lsbis2 q qlast quotlast quotm1last rs11
                                   rp rn rs10 quotp quotm1p quot quotm1)
                                  (fdiv8-loop-0 j cmpconst div div3 fnum lsbis2 q qlast quotlast quotm1last rs11
                                                 rp rn rs10 quotp quotm1p quot quotm1))
                           (:free (k) (q (+ k j)))
                           (:free (k) (divsigned (+ k j)))
                           (:free (k) (div3signed (+ k j)))
			   (:free (k) (rp (+ k j)))
			   (:free (k) (rn (+ k j)))
			   (:free (k) (quot (+ k j)))
			   (:free (k) (quotm1 (+ k j)))
			   (:free (k) (quotp (+ k j)))
			   (:free (k) (quotm1p (+ k j)))
			   (:free (k) (qlast (+ k j)))
			   (:free (k) (quotlast (+ k j)))
			   (:free (k) (quotm1last (+ k j)))
			   (:free (k) (rs10 (+ k j)))
			   (:free (k) (rs11 (+ k j))))
		  :use ((:instance mod-sum (a 1) (b j) (n 2))
		        (:instance mod-sum (a 2) (b j) (n 2))))))

(defthmd fdiv8-loop-1-2
  (implies (and (not (zp i)) (<= i (1+ (c))))
           (equal (fdiv8-loop-1 i (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q (1- (* 2 i))) (qlast (1- (* 2 i)))
	                         (quotlast (1- (* 2 i))) (quotm1last (1- (* 2 i))) (rs11 (1- (* 2 i))) (rp (1- (* 2 i)))
				 (rn (1- (* 2 i))) (rs10 (1- (* 2 i))) (quotp (1- (* 2 i))) (quotm1p (1- (* 2 i)))
				 (quot (1- (* 2 i))) (quotm1 (1- (* 2 i))))
                  (list (q (1+ (* 2 (c)))) (qlast (1+ (* 2 (c)))) (quotlast (1+ (* 2 (c)))) (quotm1last (1+ (* 2 (c))))
		        (rs11 (1+ (* 2 (c)))) (rp (1+ (* 2 (c)))) (rn (1+ (* 2 (c)))) (rs10 (1+ (* 2 (c)))) (quotp (1+ (* 2 (c))))
			(quotm1p (1+ (* 2 (c)))) (quot (1+ (* 2 (c)))) (quotm1 (1+ (* 2 (c)))))))
  :hints (("Goal" :in-theory (enable fdiv8-loop-1-1 fdiv8-loop-1))))

(defthmd fdiv8-loop-1-lemma
  (equal (fdiv8-loop-1 1 (c) (cmpconst) (div) (div3) (fnum) (lsbis2) (q-1) 0 0 0 0 (rp-1) (rn-1) (rs10-1) 0 0 (quot-1) (quotm1-1))
         (list (q (1+ (* 2 (c)))) (qlast (1+ (* 2 (c)))) (quotlast (1+ (* 2 (c)))) (quotm1last (1+ (* 2 (c))))
	       (rs11 (1+ (* 2 (c)))) (rp (1+ (* 2 (c)))) (rn (1+ (* 2 (c)))) (rs10 (1+ (* 2 (c)))) (quotp (1+ (* 2 (c))))
	       (quotm1p (1+ (* 2 (c)))) (quot (1+ (* 2 (c)))) (quotm1 (1+ (* 2 (c))))))
  :hints (("Goal" :in-theory (enable q rs11 rp rn rs10 qlast quot quotm1 quotp quotm1p quotlast quotm1last)
                  :use ((:instance fdiv8-loop-1-2 (i 1))))))

(defthmd rpf-rewrite
  (equal (rpf) (rp (1+ (* 2 (c)))))
  :hints (("Goal" :use (fdiv8-loop-1-lemma)  
                  :in-theory (enable rpf))))

(defthmd rnf-rewrite
  (equal (rnf) (rn (1+ (* 2 (c)))))
  :hints (("Goal" :use (fdiv8-loop-1-lemma)  
                  :in-theory (enable rnf))))

(defthmd quotf-rewrite
  (equal (quotf) (quot (1+ (* 2 (c)))))
  :hints (("Goal" :use (fdiv8-loop-1-lemma)  
                  :in-theory (enable quotf))))

(defthmd quotm1f-rewrite
  (equal (quotm1f) (quotm1 (1+ (* 2 (c)))))
  :hints (("Goal" :use (fdiv8-loop-1-lemma)  
                  :in-theory (enable quotm1f))))

;; The values of (quotpf) = (quotp (1+ (* 2 (c)))) and (quotm1pf) = (quotm1p (1+ (* 2 (c)))) are computed
;; by the function incquot.  (The values of (quotp j) and (quotm1p j) for other values of j are uninteresting.)

(defthmd quotpf-rewrite
  (equal (quotpf)
         (mv-nth 0 (mv-list 2 (incquot (q (1+ (* 2 (c)))) (quot (* 2 (c))) (quotm1 (* 2 (c)))
	                               (q (* 2 (c))) (quot (1- (* 2 (c)))) (quotm1 (1- (* 2 (c))))
				       (lsbis2)))))
  :hints (("Goal" :use (fdiv8-loop-1-lemma fnum-vals)  
                  :in-theory (enable quotpf quotp qlast quotlast quotm1last c))))

(defthmd quotm1pf-rewrite
  (equal (quotm1pf)
         (mv-nth 1 (mv-list 2 (incquot (q (1+ (* 2 (c)))) (quot (* 2 (c))) (quotm1 (* 2 (c)))
	                               (q (* 2 (c))) (quot (1- (* 2 (c)))) (quotm1 (1- (* 2 (c))))
				       (lsbis2)))))
  :hints (("Goal" :use (fdiv8-loop-1-lemma fnum-vals)  
                  :in-theory (enable quotm1pf quotm1p qlast quotlast quotm1last c))))
