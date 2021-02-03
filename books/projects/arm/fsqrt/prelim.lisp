(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| MOD-THEOREM-ONE-B))

(include-book "fsqrt64")

;; We impose the following constraints on the inputs of fsqrt64:

(defund input-constraints (opa fnum rin)
  (and (bvecp opa 64)
       (member fnum '(0 1 2))
       (bvecp rin 32)
       (= (bitn rin 15) 0)
       (= (bits rin 12 8) 0)))

;; Our ultimate objective is the following theorem:

;; (defthm fsqrt64-correct
;;   (implies (input-constraints opa fnum rin)
;;            (let* ((f (case fnum (0 (hp)) (1 (sp)) (2 (dp))))
;;                   (fmtw (+ 1 (expw f) (sigw f)))
;;                   (dnp (bitn rin 25))
;;                   (fzp (bitn rin 24))
;;                   (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (fsqrt64 opa fnum fzp dnp rmode)
;;                (let ((r (logior rin flags)))
;;                  (mv-let (data-spec r-spec)
;;                          (arm-fsqrt-spec (bits opa (1- fmtw) 0) rin f)
;;                    (and (equal data data-spec)
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

;; The constant definitions will be derived from that of fsqrt64 in such a way that
;; the proof of the following will be trivial:

;; (defthm fsqrt64-lemma
;;   (mv-let (d flags) (fsqrt64 (opa) (fnum) (fzp) (dnp) (rmode))
;;     (and (equal (d) d)
;;          (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

;; (defthm fsqrt64-main
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
;;     (mv-let (data flags) (fsqrt64 (opa) (fnum) fzp dnp rmode)
;;       (mv-let (data-spec r-spec) (arm-sqrt-spec (bits (opa) (1- fmtw) 0) (rin) f)
;;         (and (equal data data-spec)
;;              (equal (logior (rin) flags) r-spec))))))

;; The desired theorem can then be derived by functional instantiation.

;; In this book, we'll define the constants and prove fsqrt64-lemma.

;;*******************************************************************************
;; fsqrt64
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

(defund expinc-0 () (logand1 (log= (classa) 4) (log= (rmode) (rmodeup))))

(defund siga () (mv-nth 0 (mv-list 3 (normalize (expa) (mana) (fnum)))))
(defund expshft () (mv-nth 1 (mv-list 3 (normalize (expa) (mana) (fnum)))))
(defund expq () (mv-nth 2 (mv-list 3 (normalize (expa) (mana) (fnum)))))

(defund expodd () (bitn (expshft) 0))

(defund d-sqrtpow2 () (mv-nth 0 (mv-list 2 (sqrtpow2 (expq) (expodd) (rmode) (fnum)))))
(defund flags-sqrtpow2 () (mv-nth 1 (mv-list 2 (sqrtpow2 (expq) (expodd) (rmode) (fnum)))))

(defund rp-1 () (mv-nth 0 (mv-list 5 (firstiter (siga) (expodd)))))
(defund rn-1 () (mv-nth 1 (mv-list 5 (firstiter (siga) (expodd)))))
(defund qn-1 () (mv-nth 2 (mv-list 5 (firstiter (siga) (expodd)))))
(defund q-1 () (mv-nth 3 (mv-list 5 (firstiter (siga) (expodd)))))
(defund i-1 () (mv-nth 4 (mv-list 5 (firstiter (siga) (expodd)))))

(defund qp-1 () (bits 0 53 0))

(defund expinc-1 () (logand (expinc-0) (log= (qn-1) 0)))

(defund n ()
  (case (fnum)
    (2 (bits 27 4 0))
    (1 (bits 13 4 0))
    (0 (bits 6 4 0))
    (t 0)))

(defund q-n () (mv-nth 0 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund rp-n () (mv-nth 2 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund rn-n () (mv-nth 3 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund qp-n () (mv-nth 4 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund qn-n () (mv-nth 5 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))
(defund expinc-n () (mv-nth 6 (mv-list 7 (fsqrt64-loop-0 1 (n) (fnum) (q-1) (i-1) (rp-1) (rn-1) (qp-1) (qn-1) (expinc-1)))))

(defund exprnd () (bits (if1 (expinc-n) (+ (expq) 1) (expq)) 10 0))

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

(defund qtrunc () (mv-nth 0 (mv-list 3 (computeq (qp-shft) (qn-shft) (rp-n) (rn-n) (fnum) (true$)))))
(defund qinc () (mv-nth 1 (mv-list 3 (computeq (qp-shft) (qn-shft) (rp-n) (rn-n) (fnum) (true$)))))
(defund stk () (mv-nth 2 (mv-list 3 (computeq (qp-shft) (qn-shft) (rp-n) (rn-n) (fnum) (true$)))))

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

(defthmd fsqrt64-lemma
  (mv-let (data flags) (fsqrt64 (opa) (fnum) (fzp) (dnp) (rmode))
    (and (equal (data) data)
         (equal (flags) flags)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(signa expa mana classa flags-a data-special flags-special expinc-0 siga expshft expq expodd d-sqrtpow2
	                flags-sqrtpow2 rp-1 rn-1 qn-1 q-1 i-1 qp-1 expinc-1 n q-n rp-n rn-n qp-n qn-n expinc-n exprnd qp-shft
			qn-shft qtrunc qinc stk qrnd inx qrndden inxden data-final flags-final data flags fsqrt64))))

;; It's usually a good idea to disable the executable counterpart of any function that depends
;; on a constrained function:

(in-theory (disable (input-constraints) (signa) (expa) (mana) (classa) (flags-a) (data-special) (flags-special) (expinc-0) (siga)
                    (expshft) (expq) (expodd) (d-sqrtpow2) (flags-sqrtpow2) (rp-1) (rn-1) (qn-1) (q-1) (i-1) (qp-1) (expinc-1)
		    (n) (q-n) (rp-n) (rn-n) (qp-n) (qn-n) (expinc-n) (exprnd) (qp-shft) (qn-shft) (qtrunc) (qinc) (stk) (qrnd)
		    (inx) (qrndden) (inxden) (data-final) (flags-final) (data) (flags) (dnp) (fzp) (rmode) (f)))

;; let's also disable all the functions defined by the model and enable them only as needed:

(in-theory (disable analyze clz53-loop-0 clz53-loop-1 clz53-loop-2 clz53 computeq rshft64 rounder final specialcase
                    normalize sqrtpow2 firstiter nextdigit nextrem nextroot fsqrt64-loop-0 fsqrt64
                    (analyze) (clz53-loop-0) (clz53-loop-1) (clz53-loop-2) (clz53) (computeq) (rshft64) (rounder) (final)
		    (specialcase) (normalize) (sqrtpow2) (firstiter) (nextdigit) (nextrem) (nextroot) (fsqrt64-loop-0) (fsqrt64)))


;;*******************************************************************************
;; fsqrt64-loop-0
;;*******************************************************************************

;; We define the sequences of values (q j), (i j), (rp j), (rn j), (qp j), (qn j),
;; and (expinc j) as a set of mutually recursive functions, as they are computed by
;; fsqrt64-loop-0, and prove that the constants (rp-n), etc., defined above are
;; related to these functions as follows:
;;   (equal (rp-n) (rp (n)))
;;   (equal (rn-n) (rn (n)))
;;   (equal (qp-n) (qp (n)))
;;   (equal (qn-n) (qn (n)))
;;   (equal (expinc-n) (expinc (n)))

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

(in-theory (disable (q) (i) (rp) (rn) (qp) (qn) (expinc)))

(defthmd fsqrt64-loop-0-lemma
  (implies (and (not (zp j)) (<= j (n)))
           (equal (fsqrt64-loop-0 j (n) (fnum) (q j) (i j) (rp j) (rn j) (qp j) (qn j) (expinc j))
                  (list (q (n)) (i (n)) (rp (n)) (rn (n)) (qp (n)) (qn (n)) (expinc (n)))))
  :hints (("Goal" :in-theory (enable fsqrt64-loop-0 q i rp rn qp qn expinc))))

(defthmd fnum-vals
  (member (fnum) '(0 1 2))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm q-n-rewrite
  (equal (q-n) (q (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt64-loop-0-lemma (j 1)))
                  :in-theory (enable n q-n q i rp rn qp qn expinc))))

(defthm qp-n-rewrite
  (equal (qp-n) (qp (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt64-loop-0-lemma (j 1)))
                  :in-theory (enable n qp-n q i rp rn qp qn expinc))))

(defthm qn-n-rewrite
  (equal (qn-n) (qn (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt64-loop-0-lemma (j 1)))
                  :in-theory (enable n qn-n q i rp rn qp qn expinc))))

(defthm rp-n-rewrite
  (equal (rp-n) (rp (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt64-loop-0-lemma (j 1)))
                  :in-theory (enable n rp-n q i rp rn qp qn expinc))))

(defthm rn-n-rewrite
  (equal (rn-n) (rn (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt64-loop-0-lemma (j 1)))
                  :in-theory (enable n rn-n q i rp rn qp qn expinc))))

(defthm expinc-n-rewrite
  (equal (expinc-n) (expinc (n)))
  :hints (("Goal" :use (fnum-vals (:instance fsqrt64-loop-0-lemma (j 1)))
                  :in-theory (enable n expinc-n q i rp rn qp qn expinc))))


;;*******************************************************************************

;;*******************************************************************************

