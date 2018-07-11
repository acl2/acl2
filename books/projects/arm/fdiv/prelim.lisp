(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| ACL2::|(logior 1 x)|))

(include-book "fdiv64")

;; We impose the following constraints on the inputs of fdiv64:

(defund input-constraints (opa opb fnum rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

;; (defthm fdiv64-correct
;;   (implies (input-constraints opa opb fmt rin)
;;            (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 dp)))
;;                   (fmtw (+ 1 (expw (f)) (sigw (f))))
;;                   (dnp (bitn rin 25))
;;                   (fzp (bitn rin 24))
;;                   (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (fdiv64  opa opb fmt fz dn rmode)
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

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))
(defund f () (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))

;; In terms of these constants, we shall define constants corresponding to the local 
;; variables of fdiv64, culminating in the constants (data) and (flags), corresponding to
;; the outputs.

;; The constant definitions will be derived from that of fdiv64 in such a way that 
;; the proof of the following will be trivial:

;; (defthm fdiv64-lemma
;;   (mv-let (data flags) (fdiv64 (opa) (opb) (fnum) (fz) (dn) (rmode))
;;     (and (equal (data) data)
;;          (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

;; (defthm fdiv64-main
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
;;     (mv-let (data flags) (fdiv64 (opa) (opb) (fnum) fzp dnp rmode)
;;       (let ((r (logior (rin) flags)))         
;;         (mv-let (data-spec r-spec)
;;                 (arm-binary-spec 'div (bits (opa) (1- fmtw) 0) (bits (opb) (1- fmtw) 0) (rin) (f))
;;           (and (equal data data-spec)
;;                (equal r r-spec)))))))

;; The desired theorem can then be derived by functional instantiation.

;; In this book, we'll define the constants and prove the above fdiv64-lemma.  We'll also 
;; define analogous constants and prove analogous lemmas about the auxiliary functions.

;;*******************************************************************************
;; fdiv64
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

(defund div () (mv-nth 0 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund rp-1 () (mv-nth 1 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund rn-1 () (mv-nth 2 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund expq () (mv-nth 3 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))
(defund q-1 () (mv-nth 4 (mv-list 5 (prescale (siga) (sigb) (expdiff)))))

(defund n ()
  (if1 (divpow2)
       (bits 0 4 0)
       (case (fnum) (2 (bits 9 4 0))
                      (1 (bits 4 4 0))
                      (0 (bits 2 4 0))
                      (t 0))))

(defund rp-3n1 () (mv-nth 1 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))
(defund rn-3n1 () (mv-nth 2 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))
(defund qp-3n1 () (mv-nth 3 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))
(defund qn-3n1 () (mv-nth 4 (mv-list 5 (fdiv64-loop-0 0 (n) (div) (fnum) (q-1) (rp-1) (rn-1) (bits 0 53 0) (bits 0 53 0)))))

(defund qinc ()
  (if1 (divpow2)
       0
     (mv-nth 1 (mv-list 3 (computeq (qp-3n1) (qn-3n1) (rp-3n1) (rn-3n1) (fnum) (false$))))))

(defund qtrunc ()
  (if1 (divpow2)
       (bits (ash (mana) 1) 52 0)
     (mv-nth 0 (mv-list 3 (computeq (qp-3n1) (qn-3n1) (rp-3n1) (rn-3n1) (fnum) (false$))))))

(defund stk ()
  (if1 (divpow2)
       0
     (mv-nth 2 (mv-list 3 (computeq (qp-3n1) (qn-3n1) (rp-3n1) (rn-3n1) (fnum) (false$))))))

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

(defthmd fdiv64-lemma
  (mv-let (data flags) (fdiv64 (opa) (opb) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(signa expa mana classa flags-a signb expb manb classb flags-b data-special flags-special divpow2 siga sigb
	                expdiff div rp-1 rn-1 expq q-1 n rp-3n1 rn-3n1 qp-3n1 qn-3n1 qinc qtrunc stk sign qrnd inx qrndden inxden
			data-final flags-final data flags fdiv64))))

;; It's usually a good idea to disable the executable counterpart of any function that depends
;; on a constrained function:

(in-theory (disable (input-constraints) (signa) (expa) (mana) (classa) (flags-a) (signb) (expb) (manb) (classb) (flags-b) (data-special)
                    (flags-special) (divpow2) (siga) (sigb) (expdiff) (div) (rp-1) (rn-1) (expq) (q-1) (n) (rp-3n1) (rn-3n1) (qp-3n1)
		    (qn-3n1) (qinc) (qtrunc) (stk) (sign) (qrnd) (inx) (qrndden) (inxden) (data-final) (flags-final) (data) (flags)
		    (dnp) (fzp) (rmode) (f)))

;; Let's also disable all the functions defined by the model and enable them only as needed:

(in-theory (disable analyze clz53-loop-0 clz53-loop-1 clz53-loop-2 clz53 computeq rshft64 rounder final specialcase
                    normalize prescale nextdigit nextrem nextquot iter1 iter2 iter3 fdiv64-loop-0 fdiv64
                    (analyze) (clz53-loop-0) (clz53-loop-1) (clz53-loop-2) (clz53) (computeq) (rshft64) (rounder) (final)
		    (specialcase) (normalize) (prescale) (nextdigit) (nextrem) (nextquot) (iter1) (iter2) (iter3) (fdiv64-loop-0)
		    (fdiv64)))


;;*******************************************************************************
;; fdiv64-loop-0
;;*******************************************************************************

;; We define the sequences of values (q j), (rp j), (rn j), (qp j), and (qn j),
;; as a set of mutually recursive functions, as they are computed by fdiv64-loop-0,
;; and prove that the constants (rp-3n1), etc., defined above are related to these
;; functions as follows:
;;   (equal (rp-3n1) (rp (1+ (* 3 (n)))
;;   (equal (rn-3n1) (rn (1+ (* 3 (n)))
;;   (equal (qp-3n1) (qp (1+ (* 3 (n)))
;;   (equal (qn-3n1) (qn (1+ (* 3 (n)))

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

(in-theory (disable (q) (rp) (rn) (rs6) (rs7) (rs9) (qp) (qn)))

(defthmd fdiv64-loop-0-sublemma
  (implies (and (natp i)
                (natp j)
                (natp n)
		(< i n)
		(= (mod j 3) 1))
	   (equal (fdiv64-loop-0 i n (div) (fnum) (q j) (rp j) (rn j) (qp j) (qn j))
	          (fdiv64-loop-0 (1+ i) n (div) (fnum) (q (+ 3 j)) (rp (+ 3 j)) (rn (+ 3 j)) (qp (+ 3 j)) (qn (+ 3 j)))))
  :hints (("Goal" :expand ((fdiv64-loop-0 i n (div) (fnum) (q j) (rp j) (rn j) (qp j) (qn j))
                           (:free (k) (q (+ k j)))
			   (:free (k) (rp (+ k j)))
			   (:free (k) (rn (+ k j)))
			   (:free (k) (qp (+ k j)))
			   (:free (k) (qn (+ k j)))
			   (:free (k) (rs6 (+ k j)))
			   (:free (k) (rs9 (+ k j)))
			   (:free (k) (rs7 (+ k j))))			   
		  :use ((:instance mod-sum (a 1) (b j) (n 3))
		        (:instance mod-sum (a 2) (b j) (n 3))
		        (:instance mod-sum (a 3) (b j) (n 3))))))

(defthmd fdiv64-loop-0-lemma
  (implies (and (natp i) (<= i (n)))
           (equal (fdiv64-loop-0 i (n) (div) (fnum) (q (1+ (* 3 i)))
	                          (rp (1+ (* 3 i))) (rn (1+ (* 3 i))) (qp (1+ (* 3 i))) (qn (1+ (* 3 i))))
                  (list (q (1+ (* 3 (n)))) (rp (1+ (* 3 (n)))) (rn (1+ (* 3 (n))))
		        (qp (1+ (* 3 (n)))) (qn (1+ (* 3 (n)))))))
  :hints (("Goal" :in-theory (enable fdiv64-loop-0-sublemma fdiv64-loop-0))))

(defthmd fnum-vals
  (member (fnum) '(0 1 2))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm rp-3n1-rewrite
  (equal (rp-3n1) (rp (1+ (* 3 (n)))))
  :hints (("Goal" :use (fnum-vals (:instance fdiv64-loop-0-lemma (i 0)))
                  :in-theory (enable n rp-3n1 q rp rn qp qn))))

(defthm rn-3n1-rewrite
  (equal (rn-3n1) (rn (1+ (* 3 (n)))))
  :hints (("Goal" :use (fnum-vals (:instance fdiv64-loop-0-lemma (i 0)))
                  :in-theory (enable n rn-3n1 q rp rn qp qn))))

(defthm qp-3n1-rewrite
  (equal (qp-3n1) (qp (1+ (* 3 (n)))))
  :hints (("Goal" :use (fnum-vals (:instance fdiv64-loop-0-lemma (i 0)))
                  :in-theory (enable n qp-3n1 q rp rn qp qn))))

(defthm qn-3n1-rewrite
  (equal (qn-3n1) (qn (1+ (* 3 (n)))))
  :hints (("Goal" :use (fnum-vals (:instance fdiv64-loop-0-lemma (i 0)))
                  :in-theory (enable n qn-3n1 q rp rn qp qn))))


;;*******************************************************************************

;;*******************************************************************************


