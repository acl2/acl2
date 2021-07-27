(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| MOD-THEOREM-ONE-B))

(include-book "fsqrt4")

;; We impose the following constraints on the inputs of execute:

(defund input-constraints (opa fnum rin)
  (and (bvecp opa 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

;; (defthm fsqrt4-correct
;;   (implies (input-constraints opa fnum rin)
;;            (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
;;                   (fmtw (+ 1 (expw f) (sigw f)))
;;                   (dnp (bitn rin 25))
;;                   (fzp (bitn rin 24))
;;                   (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (execute opa fnum fzp dnp rmode)
;;                (let ((r (logior rin flags)))         
;;                  (mv-let (data-spec r-spec)
;;                          (arm-fsqrt-spec (bits opa (1- fmtw) 0) rin f)
;;                    (and (equal data data-spec)
;;                         (equal r r-spec))))))))
;;                         (equal r r-spec))))))))

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

(defund dnp () (bitn (rin) 25))
(defund fzp () (bitn (rin) 24))
(defund rmode () (bits (rin) 23 22))
(defund f () (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))

;; In terms of these constants, we shall define constants corresponding to the local 
;; variables of fdiv64, culminating in the constants (d) and (flags), corresponding to
;; the outputs.

;; The constant definitions will be derived from that of fsqrt4 in such a way that 
;; the proof of the following will be trivial:

;; (defthm execute-lemma
;;   (mv-let (d flags) (execute (opa) (fnum) (fzp) (dnp) (rmode))
;;     (and (equal (d) d)
;;          (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

;; (defthm fsqrt4-main
;;   (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
;;     (mv-let (d-spec r-spec) (arm-sqrt-spec (opa) (rin) (fpfmt))
;;       (and (equal (d) d-spec)
;;            (equal (r) r-spec))))

;; The following is an immediate consequence of the two preceding results:

;; (defthmd lemma-to-be-functionally-instantiated
;;   (let* ((f (case (fnum) (0 (hp)) (1 (sp)) (2 (dp))))
;;          (fmtw (+ 1 (expw f) (sigw f)))
;;          (dnp (bitn (rin) 25))
;;          (fzp (bitn (rin) 24))
;;          (rmode (bits (rin) 23 22)))
;;     (mv-let (data flags) (execute (opa) (fnum) fzp dnp rmode)
;;       (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) f)
;;         (and (equal data data-spec)
;;              (equal (logior (rin) flags) r-spec))))))

;; The desired theorem can then be derived by functional instantiation.

;; In this book, we'll define the constants and prove execute-lemma.

;;*******************************************************************************
;; fdiv64
;;*******************************************************************************

(defund signa () (mv-nth 0 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund expa () (mv-nth 1 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund mana () (mv-nth 2 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund classa () (mv-nth 3 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))
(defund flags-a () (mv-nth 4 (mv-list 5 (analyze (opa) (fnum) (fzp) (bits 0 7 0)))))

(defund data-special ()
  (mv-nth 0 (mv-list 2 (specialcase (signa) (opa) (classa) (fnum) (dnp) (flags-a)))))
(defund flags-special ()
  (mv-nth 1 (mv-list 2 (specialcase (signa) (opa) (classa) (fnum) (dnp) (flags-a)))))

(defund expinc-0 () (logand1 (log= (classa) 4) (log= (rmode) 1)))

(defund siga () (mv-nth 0 (mv-list 3 (normalize (expa) (mana) (fnum)))))
(defund expshft () (mv-nth 1 (mv-list 3 (normalize (expa) (mana) (fnum)))))
(defund expq () (mv-nth 2 (mv-list 3 (normalize (expa) (mana) (fnum)))))

(defund expodd () (bitn (expshft) 0))

(defund d-sqrtpow2 () (mv-nth 0 (mv-list 2 (sqrtpow2 (expq) (expodd) (rmode) (fnum)))))
(defund flags-sqrtpow2 () (mv-nth 1 (mv-list 2 (sqrtpow2 (expq) (expodd) (rmode) (fnum)))))

(defund rp-1 () (mv-nth 0 (mv-list 6 (firstiter (siga) (expodd)))))
(defund rn-1 () (mv-nth 1 (mv-list 6 (firstiter (siga) (expodd)))))
(defund root-1 () (mv-nth 2 (mv-list 6 (firstiter (siga) (expodd)))))
(defund rootm1-1 () (mv-nth 3 (mv-list 6 (firstiter (siga) (expodd)))))
(defund q-1 () (mv-nth 4 (mv-list 6 (firstiter (siga) (expodd)))))
(defund i-1 () (mv-nth 5 (mv-list 6 (firstiter (siga) (expodd)))))

(defund expinc-1 () (logand (expinc-0) (log= (q-1) 0)))

(defund n ()
  (case (fnum)
    (2 (bits 27 4 0))
    (1 (bits 13 4 0))
    (0 (bits 6 4 0))
    (t 0)))

(defund lsbis2 () (log= (fnum) 1))

(defund rpf ()
  (mv-nth 5 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))
(defund rnf ()
  (mv-nth 6 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))
(defund rootpf ()
  (mv-nth 7 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))
(defund rootm1pf ()
  (mv-nth 8 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))
(defund rootf ()
  (mv-nth 9 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))
(defund rootm1f ()
  (mv-nth 10 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))
(defund expincf ()
  (mv-nth 11 (mv-list 12 (fsqrt4-loop-0 1 (lsbis2) (n) (fnum) (q-1) 0 0 0 (i-1) (rp-1) (rn-1) 0 0 (root-1) (rootm1-1) (expinc-1)))))

(defund exprnd () (bits (if1 (expincf) (+ (expq) 1) (expq)) 10 0))

(defund rootshft ()
  (case (fnum)
    (0 (bits (rootf) 54 42))
    (1 (bits (rootf) 54 28))
    (2 (rootf))
    (t 0)))

(defund rootm1shft ()
  (case (fnum)
    (0 (bits (rootm1f) 54 42))
    (1 (bits (rootm1f) 54 28))
    (2 (rootm1f))
    (t 0)))

(defund rootpshft ()
  (case (fnum)
    (0 (bits (rootpf) 54 42))
    (1 (bits (rootpf) 54 28))
    (2 (rootpf))
    (t 0)))

(defund rootm1pshft ()
  (case (fnum)
    (0 (bits (rootm1pf) 54 42))
    (1 (bits (rootm1pf) 54 28))
    (2 (rootm1pf))
    (t 0)))

(defund qtrunc () (mv-nth 0 (mv-list 3 (computeq (rootshft) (rootm1shft) (rootpshft) (rootm1pshft) (rpf) (rnf) (lsbis2)))))
(defund qinc () (mv-nth 1 (mv-list 3 (computeq (rootshft) (rootm1shft) (rootpshft) (rootm1pshft) (rpf) (rnf) (lsbis2)))))
(defund stk () (mv-nth 2 (mv-list 3 (computeq (rootshft) (rootm1shft) (rootpshft) (rootm1pshft) (rpf) (rnf) (lsbis2)))))

(defund qrnd () (mv-nth 0 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))
(defund inx () (mv-nth 1 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))
(defund qrndden () (mv-nth 2 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))
(defund inxden () (mv-nth 3 (mv-list 4 (rounder (qtrunc) (qinc) (stk) 0 (exprnd) (rmode) (fnum)))))

(defund data-final () (mv-nth 0 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) 0 (exprnd) (rmode) (fzp) (fnum) (flags-a)))))
(defund flags-final () (mv-nth 1 (mv-list 2 (final (qrnd) (inx) (qrndden) (inxden) 0 (exprnd) (rmode) (fzp) (fnum) (flags-a)))))

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
                                          
(defthmd fsqrt4-lemma
  (mv-let (data flags) (fsqrt4 (opa) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(signa expa mana classa flags-a data-special flags-special expinc-0 siga expshft expq expodd d-sqrtpow2
	                flags-sqrtpow2 rp-1 rn-1 root-1 rootm1-1 q-1 i-1 expinc-1 n lsbis2 rpf rnf
			rootpf rootm1pf rootf rootm1f expincf exprnd rootshft rootm1shft rootpshft rootm1pshft
			qtrunc qinc stk qrnd inx qrndden inxden data-final flags-final data flags fsqrt4))))

;; It's usually a good idea to disable the executable counterpart of any function that depends
;; on a constrained function:

(in-theory (disable (input-constraints) (signa) (expa) (mana) (classa) (flags-a) (data-special) (flags-special) (expinc-0) (siga)
                    (expshft) (expq) (expodd) (d-sqrtpow2) (flags-sqrtpow2) (rp-1) (rn-1) (root-1) (rootm1-1) (q-1) (i-1) (expinc-1)
		    (n) (lsbis2) (rpf) (rnf) (rootpf) (rootm1pf) (rootf) (rootm1f) (expincf)
		    (exprnd) (rootshft) (rootm1shft) (rootpshft) (rootm1pshft) (qtrunc) (qinc) (stk) (qrnd) (inx) (qrndden) (inxden)
		    (data-final) (flags-final) (data) (flags) (dnp) (fzp) (rmode) (f)))

;; Let's also disable all the functions defined by the model and enable them only as needed:

(in-theory (disable analyze clz53-loop-0 clz53-loop-1 clz53-loop-2 clz53 computeq rshft64 rounder final specialcase
                    normalize sqrtpow2 firstiter nextdigit nextrem nextroot fsqrt4-loop-0 fsqrt4 incroot (incroot)
                    (analyze) (clz53-loop-0) (clz53-loop-1) (clz53-loop-2) (clz53) (computeq) (rshft64) (rounder) (final)
		    (specialcase) (normalize) (sqrtpow2) (firstiter) (nextdigit) (nextrem) (nextroot) (fsqrt4-loop-0) (fsqrt4)))


;;*******************************************************************************
;; fsqrt4-loop-0
;;*******************************************************************************

;; We define the sequences of values (q j), (i j), (rp j), (rn j), (root j), (rootm1 j),
;; and (expinc j) as a set of mutually recursive functions, as they are computed by 
;; fsqrt4-loop-0:

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
    (mv-nth 0 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (root (1- j)) (rootm1 (1- j)) (q j) (1- j) (fnum))))))

(defund rn (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rn-1)
    (mv-nth 1 (mv-list 2 (nextrem (rp (1- j)) (rn (1- j)) (root (1- j)) (rootm1 (1- j)) (q j) (1- j) (fnum))))))

(defund root (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (root-1)
    (mv-nth 0 (mv-list 2 (nextroot (root (1- j)) (rootm1 (1- j)) (q j) (1- j))))))

(defund rootm1 (j)
  (declare (xargs :measure (1+ (* 2 (nfix j)))))
  (if (or (zp j) (= j 1))
      (rootm1-1)
    (mv-nth 1 (mv-list 2 (nextroot (root (1- j)) (rootm1 (1- j)) (q j) (1- j))))))
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

(defund qlast (j)
  (if (or (zp j) (= j 1))
      0
    (if1 (log= (1- j) (- (n) 2))
         (q j)
       (qlast (1- j)))))

(defund rootlast (j)
  (if (or (zp j) (= j 1))
      0
    (if1 (log= (1- j) (- (n) 2))
         (root (1- j))
       (rootlast (1- j)))))

(defund rootm1last (j)
  (if (or (zp j) (= j 1))
      0
    (if1 (log= (1- j) (- (n) 2))
         (rootm1 (1- j))
       (rootm1last (1- j)))))

(defund rootp (j)
  (if (or (zp j) (= j 1))
      0
    (if1 (log= (1- j) (- (n) 1))
         (mv-nth 0 (mv-list 2 (incroot (q j) (root (1- j)) (rootm1 (1- j)) (qlast j) (rootlast j) (rootm1last j) (lsbis2) (n))))
       (rootp (1- j)))))

(defund rootm1p (j)
  (if (or (zp j) (= j 1))
      0
    (if1 (log= (1- j) (- (n) 1))
         (mv-nth 1 (mv-list 2 (incroot (q j) (root (1- j)) (rootm1 (1- j)) (qlast j) (rootlast j) (rootm1last j) (lsbis2) (n))))
       (rootm1p (1- j)))))
  
(in-theory (disable (q) (i) (rp) (rn) (root) (rootm1) (expinc) (qlast) (rootlast) (rootm1last) (rootp) (rootm1p)))

(defthmd fsqrt4-loop-0-lemma
  (implies (and (not (zp j)) (<= j (n)))
           (equal (fsqrt4-loop-0 j (lsbis2) (n) (fnum) (q j) (qlast j) (rootlast j) (rootm1last j) (i j) (rp j) (rn j) (rootp j)
	                            (rootm1p j) (root j) (rootm1 j) (expinc j))
                  (list (q (n)) (qlast (n)) (rootlast (n)) (rootm1last (n)) (i (n)) (rp (n)) (rn (n)) (rootp (n)) (rootm1p (n)) (root (n))
		        (rootm1 (n)) (expinc (n)))))
  :hints (("Goal" :in-theory (enable fsqrt4-loop-0 q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthmd fnum-vals
  (member (fnum) '(0 1 2))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm rpf-rewrite
  (equal (rpf) (rp (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n rpf q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthm rnf-rewrite
  (equal (rnf) (rn (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n rnf q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthm rootf-rewrite
  (equal (rootf) (root (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n rootf q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthm rootm1f-rewrite
  (equal (rootm1f) (rootm1 (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n rootm1f q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthm expincf-rewrite
  (equal (expincf) (expinc (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n expincf q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthm rootpf-rewrite
  (equal (rootpf)
         (mv-nth 0 (mv-list 2 (incroot (q (n)) (root (1- (n))) (rootm1 (1- (n))) (q (1- (n))) (root (- (n) 2)) (rootm1 (- (n) 2)) (lsbis2) (n)))))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n rootpf q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))

(defthm rootm1pf-rewrite
  (equal (rootm1pf)
         (mv-nth 1 (mv-list 2 (incroot (q (n)) (root (1- (n))) (rootm1 (1- (n))) (q (1- (n))) (root (- (n) 2)) (rootm1 (- (n) 2)) (lsbis2) (n)))))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt4-loop-0-lemma (j 1)))
                  :in-theory (enable n rootm1pf q qlast rootlast rootm1last i rp rn rootp rootm1p root rootm1 expinc))))
