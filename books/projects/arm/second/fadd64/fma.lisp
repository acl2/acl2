(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "../fmul64/fmul64")
(in-theory (disable fmul64 (fmul64)))

;; We need the lemma fmul64-fused-correct from "../fmul64/summary":

(local (encapsulate ()

(local (include-book "../fmul64/summary"))

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

;; The main theorem:

(defthm fmul64-fused-correct
  (implies (input-constraints opa opb scale rin 1 0)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb scale fzp dnp rmode 1 0)
               (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
  :rule-classes ())

))

(include-book "fadd64")
(local (include-book "comp"))

(local (include-book "arithmetic-5/top" :dir :system))

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

;; Our ultimate objective:

;; (defthm fma64-correct
;;   (implies (and (bvecp opa 64)
;;                 (bvecp opb 64)
;;                 (bvecp opc 64)
;;                 (bvecp rin 32))
;; 	   (let ((fma 1) (fzp (bitn (rin) 24)) (dnp (bitn (rin) 25)) (rmode (bits (rin) (23 22))))
;; 	     (mv-let (opd mulexcps piz inz expovfl) (fmul64 opb opc fzp dnp rmode fma)
;; 	       (mv-let (d flags) (fadd64 opa opd fzp dnp rmode fma inz piz expovfl mulexcps)
;; 	         (mv-let (d-spec r-spec) (arm-fma-spec 'add opa opb opc rin (dp))
;;                  (and (equal d d-spec)
;;                       (equal (logior rin flags) r-spec)))))))
;;   :rule-classes ())

;; In order to address the lack of modularity of the ACL2 code, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(local-defund fma-constraints (opa opb opc scale rin fma fscale)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (bvecp opc 64)
       (bvecp scale 64)
       (bvecp rin 32)
       (= fma 1)
       (= fscale 0)
       (equal (bits rin 12 8) 0)
       (equal (bitn rin 15) 0)))

(local (encapsulate (((opa) => *) ((opb) => *) ((opc) => *) ((scale) => *) ((rin) => *) ((fma) => *) ((fscale) => *))
  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun opc () 0))
  (local (defun scale () 0))
  (local (defun fma () 1))
  (local (defun fscale () 0))
  (local (defun rin () 0))
  (defthmd fma-constraints-lemma (fma-constraints (opa) (opb) (opc) (scale) (rin) (fma) (fscale)))))

(local-defthmd bvecp-opa (bvecp (opa) 64) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthmd bvecp-opb (bvecp (opb) 64) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthmd bvecp-opc (bvecp (opc) 64) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthmd bvecp-scale (bvecp (scale) 64) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthmd bvecp-rin (bvecp (rin) 32) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthm bitn-rin-15 (equal (bitn (rin) 15) 0) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthm bits-rin-12-8 (equal (bits (rin) 12 8) 0) :hints (("Goal" :in-theory (enable fma-constraints) :use (fma-constraints-lemma))))
(local-defthm bitn-rin-12 (equal (bitn (rin) 12) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 4))))))
(local-defthm bitn-rin-11 (equal (bitn (rin) 11) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 3))))))
(local-defthm bitn-rin-10 (equal (bitn (rin) 10) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 2))))))
(local-defthm bitn-rin-9 (equal (bitn (rin) 9) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 1))))))
(local-defthm bitn-rin-8 (equal (bitn (rin) 8) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 0))))))

(local-defund a () (if (and (= (bitn (rin) 24) 1) (= (expf (opa) (dp)) 0)) 0 (decode (opa) (dp))))
(local-defund b () (if (and (= (bitn (rin) 24) 1) (= (expf (opb) (dp)) 0)) 0 (decode (opb) (dp))))
(local-defund c () (if (and (= (bitn (rin) 24) 1) (= (expf (opc) (dp)) 0)) 0 (decode (opc) (dp))))
(local-in-theory (disable (a) (b) (c)))

;; Then we define constants representing the outputs of fmul64:

(local-defund fzp () (bitn (rin) 24))
(local-defund dnp () (bitn (rin) 25))
(local-defund rmode () (bits (rin) 23 22))

(local-defund opd () (mv-nth 0 (mv-list 5 (fmul64 (opb) (opc) (scale) (fzp) (dnp) (rmode) 1 0))))
(local-defund mulexcps () (mv-nth 1 (mv-list 5 (fmul64 (opb) (opc) (scale) (fzp) (dnp) (rmode) 1 0))))
(local-defund piz () (mv-nth 2 (mv-list 5 (fmul64 (opb) (opc) (scale) (fzp) (dnp) (rmode) 1 0))))
(local-defund inz () (mv-nth 3 (mv-list 5 (fmul64 (opb) (opc) (scale) (fzp) (dnp) (rmode) 1 0))))
(local-defund expovfl () (mv-nth 4 (mv-list 5 (fmul64 (opb) (opc) (scale) (fzp) (dnp) (rmode) 1 0))))

(local-in-theory (disable (fzp) (dnp) (rmode) (opd) (mulexcps) (piz) (inz) (expovfl)))

;; From the theorem fmul64-fused-correct, we derive the following:

(local-defthm fmul64-result
  (fmul64-fused-spec (opb) (opc) (fzp) (dnp) (opd) (mulexcps) (piz) (inz) (expovfl))
  :hints (("Goal" :use ((:instance fmul64-fused-correct (opa (opb)) (opb (opc)) (scale (scale)) (rin (rin))))
                  :in-theory (enable rmode input-constraints bvecp-opb bvecp-opc bvecp-scale bvecp-rin fzp dnp opd mulexcps piz inz expovfl)))
  :rule-classes ())

;; In terms of these constants, we shall define constants corresponding to the local
;; variables of fadd64, culminating in the constants (data) and (flags), corresponding to
;; the outputs.

;; The constant definitions will be derived from that of fadd64 in such a way that
;; the proof of the following will be trivial:

;; (defthmd equivalence-lemma
;;   (mv-let (d flags)
;;           (fadd64 (opa) (opd) (fzp) (dnp) (rmode) (fma) (inz) (piz) (expovfl) (mulexcps))
;;     (and (equal (d) d)
;;          (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

;; (defthm fma-main
;;   (mv-let (data-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
;;     (and (equal (d) data-spec)
;;          (equal (logior (rin) (flags)) r-spec))))

;; The following are immediate consequences of the preceding results:

;; (defthm lemma-to-be-functionally-instantiated
;;   (let ((fma 1) (dnp (bitn (rin) 25)) (fzp (bitn (rin) 24)) (rmode (bits (rin) 23 22)))
;;     (mv-let (opd mulexcps piz inz expovfl) (fmul64 (opb) (opc) fzp dnp rmode fma)
;; 	 (mv-let (d flags) (fadd64 (opa) opd fzp dnp rmode fma inz piz expovfl mulexcps)
;; 	   (mv-let (d-spec r-spec) (arm-fma-spec 'add (opa) (opb) (opc) (rin) (dp))
;;           (and (equal d d-spec)
;;                (equal (logior rin flags) r-spec))))))
;;   :rule-classes ())

;; The desired theorem can then be derived by functional instantiation.


;;*******************************************************************************
;; Formulation and proof of equivalence-lemma
;;*******************************************************************************

(local-defund opblong () (logand1 (fma) (lognot1 (inz))))

(local-defund mulovfl () (logand1 (opblong) (expovfl)))

(local-defund piz-1 () (logand1 (fma) (piz)))

(local-defund mulstk () (logand1 (bitn (mulexcps) 4) (opblong)))

(local-defund flags-1 ()
  (if1 (fma)
       (let ((flags (mulexcps)))
         (setbitn flags 8 4
                  (logand1 (bitn flags 4)
                           (lognot1 (opblong)))))
     (bits 0 7 0)))

(local-defund opax () (setbits (bits 0 116 0) 117 116 53 (opa)))

(local-defund opaz ()
  (mv-let (opaz r) (checkdenorm (opax) (flags-1) (fzp))
    (declare (ignore r))
    opaz))

(local-defund flags-2 ()
  (mv-let (opaz r) (checkdenorm (opax) (flags-1) (fzp))
    (declare (ignore opaz))
    r))

(local-defund opbz ()
  (if1 (lognot1 (fma))
       (mv-let (opbz flags) (checkdenorm (opd) (flags-2) (fzp))
         (declare (ignore flags))
         opbz)
       (opd)))

(local-defund flags-3 ()
  (if1 (lognot1 (fma))
       (mv-let (opb flags) (checkdenorm (opd) (flags-2) (fzp))
         (declare (ignore opb))
         flags)
       (flags-2)))

(local-defund isspecial ()
  (mv-let (isspecial d flags) (checkspecial (opaz) (opbz) (fzp) (dnp) (rmode) (opblong) (mulovfl) (piz-1) (mulstk) (flags-3))
    (declare (ignore d flags))
    isspecial))

(local-defund d-1 ()
  (mv-let (isspecial d flags) (checkspecial (opaz) (opbz) (fzp) (dnp) (rmode) (opblong) (mulovfl) (piz-1) (mulstk) (flags-3))
    (declare (ignore isspecial flags))
    d))

(local-defund flags-4 ()
  (mv-let (isspecial d flags) (checkspecial (opaz) (opbz) (fzp) (dnp) (rmode) (opblong) (mulovfl) (piz-1) (mulstk) (flags-3))
    (declare (ignore isspecial d))
    flags))

(local-defund usa () (log<> (sign (opaz)) (sign (opbz))))

(local-defund far () (isfar (expnt (opaz)) (expnt (opbz)) (usa)))

(local-defund sum ()
  (mv-let (sum stk signl) (add (opaz) (opbz) (far) (usa) (mulstk))
    (declare (ignore stk signl))
    sum))

(local-defund stk ()
  (mv-let (sum stk signl) (add (opaz) (opbz) (far) (usa) (mulstk))
    (declare (ignore sum signl))
    stk))

(local-defund signl ()
  (mv-let (sum stk signl) (add (opaz) (opbz) (far) (usa) (mulstk))
    (declare (ignore sum stk))
     signl))

(local-defund lshift ()
  (mv-let (lshift expshft) (computelshift (opaz) (opbz) (far) (usa))
    (declare (ignore expshft))
    lshift))

(local-defund expshft ()
  (mv-let (lshift expshft) (computelshift (opaz) (opbz) (far) (usa))
    (declare (ignore lshift))
    expshft))

(local-defund sumshft () (bits (ash (sum) (lshift)) 107 0))

(local-defund signout () (if1 (mulovfl) (sign (opd)) (signl)))

(local-defund rnddir () (computernddir (rmode) (signout)))

(local-defund incovfl ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incnorm inxovfl inxnorm))
    incovfl))

(local-defund incnorm ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incovfl inxovfl inxnorm))
    incnorm))

(local-defund inxovfl ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incovfl incnorm inxnorm))
    inxovfl))

(local-defund inxnorm ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incovfl incnorm inxovfl))
    inxnorm))

(local-defund sumunrnd () (bits (sumshft) 107 54))

(local-defund sumnorm () (bits (+ (sumunrnd) (incnorm)) 53 0))

(local-defund sumovfl () (bits (+ (bits (sumunrnd) 53 1) (incovfl)) 53 0))

(local-defund tiny () (logand1 (lognot1 (bitn (sumunrnd) 53)) (lognot1 (bitn (sumunrnd) 52))))

(local-defund ovfl2 () (logand1 (log= (bits (sumunrnd) 53 1) (- (ash 1 53) 1)) (incovfl)))

(local-defund ovfl () (bitn (sumnorm) 53))

(local-defund informax ()
  (logior1 (logior1 (logior1 (logand1 (log= (expshft) 2046)
                                      (logior1 (ovfl) (ovfl2)))
                             (logand1 (log= (expshft) 2045) (ovfl2)))
                    (logand1 (log= (expshft) 2047) (opblong)))
           (mulovfl)))

(local-defund expout ()
  (if1 (informax)
       (if1 (log= (rnddir) 1)
            (bits 2046 10 0)
            (bits 2047 10 0))
       (if1 (tiny)
            (if1 (fzp)
                 (bits 0 10 0)
                 (if1 (bitn (sumnorm) 52)
                      (bits 1 10 0)
                      (bits (expshft) 10 0)))
            (if1 (ovfl2)
                 (bits (+ (expshft) 2) 10 0)
                 (if1 (ovfl)
                      (bits (if1 (log= (expshft) 0) 2 (+ (expshft) 1)) 10 0)
                      (bits (if1 (logand1 (log= (expshft) 0) (bitn (sumnorm)
                                                                   52)) 1 (expshft)) 10 0))))))

(local-defund fracout ()
  (if1 (informax)
       (if1 (log= (rnddir) 1)
            (bits 4503599627370495 51 0)
            (bits 0 51 0))
       (if1 (tiny)
            (if1 (fzp)
                 (bits 0 51 0)
                 (if1 (bitn (sumnorm) 52)
                      (bits 0 51 0)
                      (bits (sumnorm) 51 0)))
            (if1 (ovfl2)
                 (bits 0 51 0)
                 (if1 (ovfl)
                      (bits (sumovfl) 51 0)
                      (bits (sumnorm) 51 0))))))

(local-defund flags-5 ()
  (if1 (informax)
       (setbitn (setbitn (flags-4) 8 2 1) 8 4 1)
       (if1 (tiny)
            (if1 (fzp)
                 (setbitn (flags-4) 8 3 1)
                 (if1 (bitn (sumnorm) 52)
                      (setbitn (setbitn (flags-4) 8 3 1) 8 4 1)
                      (if1 (inxnorm)
                           (setbitn (setbitn (flags-4) 8 3 1) 8 4 1)
                           (flags-4))))
            (if1 (ovfl2)
                 (setbitn (flags-4) 8 4 (logior1 (bitn (flags-4) 4) (inxovfl)))
                 (if1 (ovfl)
                      (setbitn (flags-4) 8 4 (logior1 (bitn (flags-4) 4) (inxovfl)))
                      (setbitn (flags-4) 8 4 (logior1 (bitn (flags-4) 4) (inxnorm))))))))

(local-defund d ()
  (if1 (isspecial)
       (d-1)
       (setbits (setbits (setbitn (d-1) 64 63 (signout)) 64 62 52 (expout)) 64 51 0
                (fracout))))

(local-defun flags ()
  (if1 (isspecial)
       (flags-4)
       (flags-5)))

(local-defthmd equivalence-lemma
  (mv-let (d flags)
          (fadd64 (opa) (opd) (bitn (rin) 24) (bitn (rin) 25) (bits (rin) 23 22)
                  (fma) (inz) (piz) (expovfl) (mulexcps))
    (and (equal (d) d)
         (equal (flags) flags)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(fzp dnp rmode opblong mulovfl piz-1 mulstk flags-1 opax
                        opaz flags-2 opbz flags-3 isspecial d-1 flags-4 usa far sum stk signl signout
                        lshift expshft sumshft rnddir incovfl incnorm inxovfl inxnorm
                        sumunrnd sumnorm sumovfl ovfl2 ovfl informax tiny expout
                        fracout flags-5 d flags fadd64))))

;; It's usually a good idea to disable the executable counterpart of any function that depends
;; on a constrained function:

(local-in-theory (disable (comp-constraints) (opblong) (mulovfl) (piz-1) (fzp) (dnp) (rmode)
                    (mulstk) (flags-1) (opax) (opaz) (flags-2) (opbz) (flags-3) (isspecial) (d-1) (flags-4) (usa)
                    (far) (sum) (stk) (signl) (signout) (lshift) (expshft) (sumshft) (rnddir) (incovfl) (incnorm)
                    (inxovfl) (inxnorm) (sumunrnd) (sumnorm) (sumovfl) (tiny) (ovfl2) (ovfl)
                    (informax) (expout) (fracout) (flags-5) (d) (flags)))

;; let's also disable all the functions defined by the model and enable them only as needed:

(local-in-theory (disable (computernddir) (gag) (sign) (expnt) (frac) (checkdenorm) (checkspecial)
                    (isfar) (add) (clz128) (lza128) (computelza) (computelshift) (rndinfo) (fadd64)
                    computernddir gag sign expnt frac checkdenorm checkspecial isfar
                    add clz128 lza128 computelza computelshift rndinfo fadd64))

;;*******************************************************************************
;; Operand components
;;*******************************************************************************

(local-defund signa () (sign (opaz)))

(local-defund signb () (sign (opbz)))

(local-defund expa () (expnt (opaz)))

(local-defund expb () (expnt (opbz)))

(local-defund fraca () (frac (opaz)))

(local-defund fracb () (frac (opbz)))

(local-in-theory (disable (signa) (signb) (expa) (expb) (fraca) (fracb)))

(local-defthm signa-0-1
  (member (signa) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signa))))

(local-defthmd bvecp-expa
  (bvecp (expa) 11)
  :hints (("Goal" :in-theory (enable cat-0 expa expnt))))

(local-defthm natp-expa
  (natp (expa))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-expa)))

(local-defthmd bvecp-fraca
  (bvecp (fraca) 105)
  :hints (("Goal" :in-theory (enable fraca frac opax opaz checkdenorm))))

(local-defthm natp-fraca
  (natp (fraca))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-fraca)))

(local-defthmd fraca-low
  (equal (bits (fraca) 52 0) 0)
  :hints (("Goal" :in-theory (enable fraca frac opax opaz checkdenorm))))

(local-defthm signb-0-1
  (member (signb) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signb))))

(local-defthmd bvecp-expb
  (bvecp (expb) 11)
  :hints (("Goal" :in-theory (enable expb expnt))))

(local-defthm natp-expb
  (natp (expb))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-expb)))

(local-defthmd bvecp-fracb
  (bvecp (fracb) 105)
  :hints (("Goal" :in-theory (enable fracb frac opbz checkdenorm))))

(local-defthm natp-fracb
  (natp (fracb))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-fracb)))


;;*******************************************************************************
;; checkSpecial
;;*******************************************************************************

(local-defund opazero () (logand1 (log= (expa) 0) (log= (fraca) 0)))

(local-defund opainf () (logand1 (log= (expa) 2047) (log= (fraca) 0)))

(local-defund opanan () (logand1 (log= (expa) 2047) (log<> (fraca) 0)))

(local-defund opaqnan () (logand1 (opanan) (bitn (fraca) 104)))

(local-defund opasnan () (logand1 (opanan) (lognot1 (bitn (fraca) 104))))

(local-defund opbzero () (logand1 (logand1 (logand1 (log= (expb) 0) (log= (fracb) 0)) (lognot1 (mulovfl))) (lognot1 (mulstk))))

(local-defund opbinf () (logand1 (logand1 (log= (expb) 2047) (log= (fracb) 0)) (lognot1 (opblong))))

(local-defund opbnan () (logand1 (logand1 (log= (expb) 2047) (log<> (fracb) 0)) (lognot1 (opblong))))

(local-defund opbqnan () (logand1 (opbnan) (bitn (fracb) 104)))

(local-defund opbsnan () (logand1 (opbnan) (lognot1 (bitn (fracb) 104))))

(local-defund isspecial* ()
  (if1 (opasnan)
       1
       (if1 (piz-1)
            1
            (if1 (opbsnan)
                 1
                 (if1 (opaqnan)
                      1
                      (if1 (opbqnan)
                           1
                           (if1 (opainf)
                                1
                                (if1 (opbinf)
                                     1
                                     (if1 (logand1 (logand1 (opazero) (opbzero))
                                                   (log= (signa) (signb)))
                                          1
                                          (if1 (logand1 (logand1 (logand1 (logand1 (log= (expa) (expb))
                                                                                   (log= (fraca) (fracb)))
									  (lognot1 (mulovfl)))
                                                                 (lognot1 (mulstk)))
                                                        (log<> (signa) (signb)))
                                               1
                                               0))))))))))

(local-defund flags-4* ()
  (if1 (opasnan)
       (setbitn (flags-3) 8 0 1)
       (if1 (piz-1)
            (flags-3)
            (if1 (opbsnan)
                 (setbitn (flags-3) 8 0 1)
                 (if1 (opaqnan)
                      (flags-3)
                      (if1 (opbqnan)
                           (flags-3)
                           (if1 (opainf)
                                (if1 (logand1 (opbinf) (log<> (signa) (signb)))
                                     (setbitn (flags-3) 8 0 1)
                                     (flags-3))
                                (if1 (opbinf)
                                     (flags-3)
                                     (if1 (logand1 (logand1 (opazero) (opbzero))
                                                   (log= (signa) (signb)))
                                          (flags-3)
                                          (if1 (logand1 (logand1 (logand1 (logand1 (log= (expa) (expb))
                                                                                   (log= (fraca) (fracb)))
									  (lognot1 (mulovfl)))
                                                                 (lognot1 (mulstk)))
                                                        (log<> (signa) (signb)))
                                               (flags-3)
                                               (flags-3)))))))))))

(local-defund d-1* ()
  (if1 (opasnan)
       (bits (if1 (dnp) (defnan) (gag (bits (opaz) 116 53))) 63 0)
       (if1 (piz-1)
            (defnan)
            (if1 (opbsnan)
                 (bits (if1 (dnp) (defnan) (gag (bits (opbz) 116 53))) 63 0)
                 (if1 (opaqnan)
                      (bits (if1 (dnp) (defnan) (bits (opaz) 116 53)) 63 0)
                      (if1 (opbqnan)
                           (bits (if1 (dnp) (defnan) (bits (opbz) 116 53)) 63 0)
                           (if1 (opainf)
                                (if1 (logand1 (opbinf) (log<> (signa) (signb)))
                                     (defnan)
                                     (bits (opaz) 116 53))
                                (if1 (opbinf)
                                     (bits (opbz) 116 53)
                                     (if1 (logand1 (logand1 (opazero) (opbzero))
                                                   (log= (signa) (signb)))
                                          (setbitn (bits 0 63 0) 64 63 (signa))
                                          (if1 (logand1 (logand1 (logand1 (logand1 (log= (expa) (expb))
                                                                                   (log= (fraca) (fracb)))
									  (lognot1 (mulovfl)))
                                                                 (lognot1 (mulstk)))
                                                        (log<> (signa) (signb)))
                                               (IF1 (log= (rmode) 2)
                                                    (setbitn (bits 0 63 0) 64 63 1)
                                                    (bits 0 63 0))
                                               (bits 0 63 0)))))))))))

(local-in-theory (disable (opazero) (opainf) (opanan) (opasnan) (opaqnan) (opbzero) (opbinf) (opbnan)
                    (opbsnan) (opbqnan) (isspecial*) (flags-4*) (d-1*)))

(local-defthmd checkspecial-lemma
  (and (equal (isspecial) (isspecial*))
       (equal (flags-4) (flags-4*))
       (equal (d-1) (d-1*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(opazero opainf opanan opasnan opaqnan opbzero opbinf opbnan
                        opbsnan opbqnan isspecial* flags-4* d-1* isspecial flags-4 d-1 checkspecial expa expb
                        fraca fracb signa signb))))

;;*******************************************************************************
;; Computational Case
;;*******************************************************************************

(local-defund p () (* (b) (c)))
(local-in-theory (disable (p)))

(local-defund specialp ()
  (or (nanp (opa) (dp))
      (infp (opa) (dp))
      (nanp (opb) (dp))
      (infp (opb) (dp))
      (nanp (opc) (dp))
      (infp (opc) (dp))
      (= (+ (a) (p)) 0)))

(local-in-theory (disable (specialp)))

(local-defthm fzerp-b-0
  (iff (or (zerp (opb) (dp)) (fzerp (opb) (fzp)))
       (= (b) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable b sgnf sigf manf expf dp bias zerp fzp decode ddecode ndecode denormp encodingp bvecp-opb))))

(local-defthm fzerp-c-0
  (iff (or (zerp (opc) (dp)) (fzerp (opc) (fzp)))
       (= (c) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable c sgnf sigf manf expf dp bias zerp fzp decode ddecode ndecode denormp encodingp bvecp-opc))))

(local-defthm specialp-fused-specialp
  (implies (not (specialp))
           (or (not (fmul64-fused-special-p (opb) (opc) (fzp)))
	       (= (p) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p specialp fmul64-fused-special-p)
                  :use (fzerp-b-0 fzerp-c-0))))

(local-defthmd p-0-1
  (implies (and (not (specialp))
                (fmul64-fused-special-p (opb) (opc) (fzp)))
	   (and (equal (p) 0)
                (equal (piz) 0)
		(equal (inz) 1)
                (equal (bitn (mulexcps) 1) 0)
                (equal (bitn (mulexcps) 3) 0)
                (equal (bitn (mulexcps) 2) 0)
                (equal (bitn (mulexcps) 4) 0)
                (equal (bitn (mulexcps) 7)
                       (if (or (fzerp (opb) (fzp)) (fzerp (opc) (fzp))) 1 0))
                (equal (bitn (mulexcps) 0) 0)
                (equal (expovfl) 0)
                (equal (opd) (ash (zencode (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp))) (dp)) 53))))
 :hints (("Goal" :in-theory (enable specialp fmul64-fused-spec fmul64-fused-special inf-times-zero fmul64-fused-spec-special-val
                                    snanp qnanp)
		 :use (specialp-fused-specialp fmul64-result))))

(local-defthmd p-0-2
  (implies (and (not (specialp))
                (fmul64-fused-special-p (opb) (opc) (fzp)))
	   (equal (opd)
	          (if (= (bitn (opb) 63) (bitn (opc) 63))
		      0 (ash 1 116))))
 :hints (("Goal" :in-theory (enable p-0-1 zencode sgnf ash cat dp)
                 :use ((:instance bitn-0-1 (x (opb)) (n 63))
		       (:instance bitn-0-1 (x (opc)) (n 63))))))

(local-defthm fma-1
  (equal (fma) 1)
  :hints (("Goal" :use (fma-constraints-lemma) :in-theory (enable fma-constraints))))

(local-defthm fscale-0
  (equal (fscale) 0)
  :hints (("Goal" :use (fma-constraints-lemma) :in-theory (enable fma-constraints))))

(local-in-theory (disable analyze specialcase clz53-loop-0 clz53-loop-1 clz53-loop-2 clz53 compress computeproduct-loop-0 computeproduct
                    rightshft-loop-0 rightshft leftshft fmul64 (analyze) (specialcase) (clz53-loop-0) (clz53-loop-1)
		    (clz53-loop-2) (clz53) (compress) (computeproduct-loop-0) (computeproduct) (rightshft-loop-0) (rightshft)
		    (leftshft) (fmul64)))

(local-defthm bvecp-mulexcps
  (bvecp (mulexcps) 8)
  :hints (("Goal" :in-theory (enable mulexcps analyze specialcase fmul64))))

(local-defthm rin-12-10
  (equal (bits (rin) 12 10) 0)
  :hints (("Goal" :use ((:instance bits-bits (x (rin)) (i 12) (j 8) (k 4) (l 2)))
                  :in-theory (disable bits-bits))))

(local-defthmd expa-bound
  (implies (not (specialp))
           (< (expf (opa) (dp)) 2047))
  :hints (("Goal" :in-theory (enable specialp nanp infp expf expw manf dp encodingp unsupp bvecp-opa)
                  :use ((:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(local-defthmd comp-1
  (implies (not (fmul64-fused-special-p (opb) (opc) (fzp)))
	   (not (equal (p) 0)))
 :hints (("Goal" :use (fzerp-b-0 fzerp-c-0)
                 :in-theory (enable fmul64-fused-special-p p))))

(local-defthm bvecp-opd
  (bvecp (opd) 117)
  :hints (("Goal" :in-theory (enable opd specialcase fmul64))))

(local-defthmd comp-2
  (implies (not (fmul64-fused-special-p (opb) (opc) (fzp)))
	   (and (equal (b) (decode (opb) (dp)))
	        (equal (c) (decode (opc) (dp)))))
 :hints (("Goal" :use (fmul64-result comp-1 bvecp-opb bvecp-opc)
                 :in-theory (enable dp prec sgnf sigf expf decode ddecode encodingp denormp fzp fmul64-fused-special-p b c fzerp))))

(local-defthm bvecp-expovfl
  (bvecp (expovfl) 1)
  :hints (("Goal" :in-theory (enable expovfl analyze specialcase fmul64))))

(local-defthmd a+p<>0
  (implies (not (specialp))
           (not (= (+ (a) (p)) 0)))
  :hints (("Goal" :in-theory (enable specialp))))

(local-defthm bitn-set-flag
  (implies (and (natp k)
                (natp b)
		(natp r))
           (equal (bitn (set-flag b r) k)
	          (if (= k b) 1 (bitn r k))))
  :hints (("Goal" :use ((:instance bitn-logior (x (expt 2 b)) (y r) (n k)))
                  :in-theory (enable bitn-expt bitn-expt-0 set-flag))))

(local-defthm natp-set-flag
  (implies (and (natp r) (natp b))
           (natp (set-flag b r)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable set-flag))))

(local-defthm bvecp-expt-2
  (implies (and (natp n)
                (natp b)
		(< b n))
	   (bvecp (expt 2 b) n))
  :hints (("Goal" :in-theory (enable bvecp))))

(local-defthm bvecp-set-flag
  (implies (and (natp n)
                (bvecp r n)
		(natp b)
		(< b n))
	   (bvecp (set-flag b r) n))
   :hints (("Goal" :in-theory (enable set-flag))))

(local-defund rz ()
  (if (and (= (bitn (rin) (fz)) 1)
           (or (denormp (opa) (dp)) (denormp (opb) (dp)) (denormp (opc) (dp))))
      (set-flag 7 (rin))
    (rin)))

(local-in-theory (disable (rz)))

(local-defthm rz-fz
  (implies (and (natp k) (not (= k 7)))
           (equal (bitn (rz) k)
                  (bitn (rin) k)))
  :hints (("Goal" :in-theory (enable rz)
                  :use (bvecp-rin))))

(local-defthm bvecp-rz
  (bvecp (rz) 32)
  :hints (("Goal" :in-theory (enable rz)
                  :use (bvecp-rin))))

(local-defthm bits-rz-12-10
  (equal (bits (rz) 12 10) 0)
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (rz)) (n 12) (m 10))
                        (:instance bitn-plus-bits (x (rz)) (n 11) (m 10))
			(:instance bitn-plus-bits (x (rin)) (n 12) (m 10))
                        (:instance bitn-plus-bits (x (rin)) (n 11) (m 10))))))

(local-defthm bits-rz-23-22
  (equal (bits (rz) 23 22) (bits (rin) 23 22))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (rz)) (n 23) (m 22))
			(:instance bitn-plus-bits (x (rin)) (n 23) (m 22))))))

(local-defthmd p-0-3
  (implies (and (not (specialp))
                (fmul64-fused-special-p (opb) (opc) (fzp)))
	   (comp-constraints (opa) (opd) (rz) (fma) (inz) (piz) (expovfl) (mulexcps) (p)))
 :hints (("Goal" :use (expa-bound specialp-fused-specialp)
                 :in-theory (enable specialp p-0-1 p-0-2 a c comp-constraints bvecp-rin bvecp-opa bvecp-opb bvecp-opc))))

(local-defthmd comp-3
  (implies (and (not (specialp))
                (= (expovfl) 1)
                (not (fmul64-fused-special-p (opb) (opc) (fzp))))
	   (comp-constraints (opa) (opd) (rz) (fma) (inz) (piz) (expovfl) (mulexcps) (p)))
 :hints (("Goal" :use (fmul64-result comp-1 expa-bound)
                 :in-theory (enable comp-2 p a fmul64-fused-comp fmul64-fused-spec comp-constraints bvecp-rin bvecp-opa bvecp-opb
		                    chop val absval specialp bvecp-opc))))

(local-defthmd comp-4
  (implies (and (not (specialp))
                (not (= (expovfl) 1))
		(> (bits (opd) 115 105) 0)
                (not (fmul64-fused-special-p (opb) (opc) (fzp))))
	   (comp-constraints (opa) (opd) (rz) (fma) (inz) (piz) (expovfl) (mulexcps) (p)))
 :hints (("Goal" :use (fmul64-result comp-1 expa-bound)
                 :in-theory (enable comp-2 p a fmul64-fused-comp fmul64-fused-spec comp-constraints bvecp-rin bvecp-opa bvecp-opb
		                    chop val absval specialp bvecp-opc))))

(local-defthm integerp-opd
  (integerp (opd))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable opd specialcase fmul64))))

(local-defthmd comp-5
  (equal (chop (* 2 (bits (opd) 104 0)) -53)
         (* (expt 2 53) (bits (opd) 104 52)))
 :hints (("Goal" :in-theory (enable chop bits))))

(local-defthmd comp-6
  (implies (and (not (specialp))
                (not (= (expovfl) 1))
		(= (bits (opd) 115 105) 0)
                (not (fmul64-fused-special-p (opb) (opc) (fzp))))
	   (comp-constraints (opa) (opd) (rz) (fma) (inz) (piz) (expovfl) (mulexcps) (p)))
 :hints (("Goal" :use (fmul64-result comp-1 expa-bound
                       (:instance bits-shift-up-2 (x (BITS (OPD) 104 0)) (k 1) (i 51)))
                 :in-theory (enable comp-2 p a fmul64-fused-comp fmul64-fused-spec comp-constraints bvecp-rin bvecp-opa bvecp-opb
		                    comp-5 val absval specialp bvecp-opc))))

(local-defthmd fma-comp-constraints
  (implies (not (specialp))
	   (comp-constraints (opa) (opd) (rz) (fma) (inz) (piz) (expovfl) (mulexcps) (p)))
 :hints (("Goal" :use (p-0-3 bvecp-expovfl comp-3 comp-4 comp-6)
                 :in-theory (e/d (bvecp) (bvecp-expovfl)))))

(local-defthm fma-comp
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (p)) (rz) (dp))
             (and (equal (d) d-spec)
                  (equal (bitn (logior (rz) (flags)) 4) (bitn r-spec 4))
                  (equal (bitn (logior (rz) (flags)) 3) (bitn r-spec 3))
                  (equal (bitn (logior (rz) (flags)) 2) (bitn r-spec 2)))))
  :rule-classes ()
  :hints (("Goal" :use (fma-comp-constraints
                        (:instance fadd64-comp (opa (opa)) (opb (opd)) (rin (rz)) (fma (fma)) (inz (inz))
                                               (piz (piz)) (expovfl (expovfl)) (mulexcps (mulexcps)) (b (p))))
		  :in-theory (enable a equivalence-lemma))))

(local-defthm zerp-fzerp-b
  (iff (or (zerp (opb) (dp)) (fzerp (opb) (fzp)))
       (and (not (nanp (opb) (dp)))
            (not (infp (opb) (dp)))
            (= (b) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable nanp infp b sgnf sigf manf expf dp bias zerp fzp decode ddecode ndecode denormp
                              encodingp bvecp-opb))))

(local-defthm zerp-fzerp-c
  (iff (or (zerp (opc) (dp)) (fzerp (opc) (fzp)))
       (and (not (nanp (opc) (dp)))
            (not (infp (opc) (dp)))
            (= (c) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable nanp infp c sgnf sigf manf expf dp bias zerp fzp decode ddecode ndecode denormp
                              encodingp bvecp-opc))))

(local-defthmd fmul-special-val
  (implies (fmul64-fused-special-p (opb) (opc) (fzp))
           (equal (opd)
	          (cond ((or (and (infp (opb) (dp)) (or (zerp (opc) (dp)) (fzerp (opc) (fzp))))
		             (and (infp (opc) (dp)) (or (zerp (opb) (dp)) (fzerp (opb) (fzp))))
			     (and (= (dnp) 1) (or (nanp (opb) (dp)) (nanp (opc) (dp)))))
                         (cat (indef (dp)) 64 0 53))
			((snanp (opb) (dp))
                         (cat (opb) 64 0 53))
                        ((snanp (opc) (dp))
                         (cat (opc) 64 0 53))
                        ((qnanp (opb) (dp))
                         (cat (opb) 64 0 53))
                        ((qnanp (opc) (dp))
                         (cat (opc) 64 0 53))
                        ((or (infp (opb) (dp)) (infp (opc) (dp)))
                         (cat (iencode (logxor (bitn (opb) 63) (bitn (opc) 63)) (dp)) 64 0 53))
                        (t
                         (cat (zencode (logxor (bitn (opb) 63) (bitn (opc) 63)) (dp)) 64 0 53)))))
  :hints (("Goal" :in-theory (enable fmul64-fused-spec-special-val fmul64-fused-special fmul64-fused-spec sgnf dp prec expw
                                     inf-times-zero cat ash)
                  :use (fmul64-result bvecp-opc bvecp-opb
		        (:instance bitn-0-1 (x (opb)) (n 63)) (:instance bitn-0-1 (x (opc)) (n 63))))))

(local-defthm nanp-infp
  (implies (nanp x (dp))
           (and (not (infp x (dp)))
	        (not (denormp x (dp)))))
  :hints (("Goal" :in-theory (enable dp sigw expw encodingp denormp nanp infp))))

(local-defthm infp-denormp
  (implies (infp x (dp))
           (not (denormp x (dp))))
  :hints (("Goal" :in-theory (enable dp sigw expw encodingp denormp nanp infp))))

(local-defthmd piz-rewrite
  (equal (piz)
         (if (or (and (infp (opb) (dp)) (or (zerp (opc) (dp)) (fzerp (opc) (fzp))))
		 (and (infp (opc) (dp)) (or (zerp (opb) (dp)) (fzerp (opb) (fzp)))))
	     1 0))
  :hints (("Goal" :in-theory (enable fmul64-fused-spec-special-val fmul64-fused-special fmul64-fused-special-p fmul64-fused-spec
                                     snanp qnanp fmul64-fused-comp inf-times-zero)
		  :use (fmul64-result))))

(local-defthmd inz-rewrite
  (equal (inz)
         (if (or (infp (opb) (dp)) (nanp (opb) (dp))
	         (infp (opc) (dp)) (nanp (opc) (dp))
		 (= (b) 0) (= (c) 0))
	     1 0))
  :hints (("Goal" :in-theory (enable fmul64-fused-special fmul64-fused-special-p fmul64-fused-spec
                                     fmul64-fused-comp)
		  :use (fmul64-result zerp-fzerp-b zerp-fzerp-c))))

(local-in-theory (enable opbz))

(local-defthm inz-special-p
  (implies (not (= (inz) 0))
           (fmul64-fused-special-p (opb) (opc) (fzp)))
  :hints (("Goal" :in-theory (enable fmul64-fused-special fmul64-fused-spec fmul64-fused-comp)
		  :use (fmul64-result))))

(local-defthmd inz-0-1
  (bitp (inz))
  :hints (("Goal" :in-theory (enable fmul64-fused-special fmul64-fused-spec fmul64-fused-comp)
		  :use (fmul64-result))))

(local-defthm opd-low
  (implies (not (= (inz) 0))
           (equal (bits (opd) 52 0) 0))
  :hints (("Goal" :in-theory (enable bits-cat fmul-special-val))))

(local-defthmd opbnan-nanp-1
  (equal (opbnan)
         (if (and (= (inz) 1) (nanp (bits (opd) 116 53) (dp)))
	     1 0))
  :hints (("Goal" :in-theory (enable nanp opbnan expf dp expb encodingp unsupp expnt opblong fracb
                                     manf frac)
	          :use (inz-0-1 (:instance bits-plus-bits (x (opd)) (n 104) (p 53) (m 0))))))

(local-defthm nanp-bits-iencode
  (not (nanp (bits (iencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp iencode nanp encodingp expf manf cat))))

(local-defthm nanp-bits-zencode
  (not (nanp (bits (zencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp zencode nanp encodingp expf manf cat))))

(local-defthm nanp-bits-indef
  (nanp (bits (indef (dp)) 63 0) (dp))
  :hints (("Goal" :in-theory (enable unsupp dp zencode nanp encodingp expf manf cat))))

(local-in-theory (disable iencode zencode))

(local-defthmd opbnan-nanp
  (equal (opbnan)
         (if (or (and (infp (opb) (dp)) (or (zerp (opc) (dp)) (fzerp (opc) (fzp))))
		 (and (infp (opc) (dp)) (or (zerp (opb) (dp)) (fzerp (opb) (fzp))))
		 (nanp (opb) (dp))
		 (nanp (opc) (dp)))
	     1 0))
  :hints (("Goal" :in-theory (enable snanp qnanp inz-rewrite bits-cat bvecp-opb bvecp-opc opbnan-nanp-1 fmul-special-val))))

(local-defthmd opbsnan-nanp-1
  (equal (opbsnan)
         (if (and (= (inz) 1) (snanp (bits (opd) 116 53) (dp)))
	     1 0))
  :hints (("Goal" :in-theory (enable snanp opbsnan nanp opbnan expf dp expb encodingp unsupp opbz expnt checkdenorm
                                     bitn-bits opblong fracb manf frac)
	          :use ((:instance bits-plus-bits (x (opd)) (n 104) (p 53) (m 0))))))

(local-defthm snanp-bits-iencode
  (not (snanp (bits (iencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp iencode nanp snanp encodingp expf manf cat))))

(local-defthm snanp-bits-zencode
  (not (snanp (bits (zencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp zencode nanp snanp encodingp expf manf cat))))

(local-defthm snanp-bits-indef
  (not (snanp (bits (indef (dp)) 63 0) (dp)))
  :hints (("Goal" :in-theory (enable unsupp dp zencode nanp snanp encodingp expf manf cat))))

(local-defthm qnanp-bits-iencode
  (not (qnanp (bits (iencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp iencode nanp qnanp encodingp expf manf cat))))

(local-defthm qnanp-bits-zencode
  (not (qnanp (bits (zencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp zencode nanp qnanp encodingp expf manf cat))))

(local-defthm qnanp-bits-indef
  (qnanp (bits (indef (dp)) 63 0) (dp))
  :hints (("Goal" :in-theory (enable unsupp dp zencode nanp qnanp encodingp expf manf cat))))

(local-defthmd snanp-nanp
  (equal (nanp x (dp))
         (or (snanp x (dp)) (qnanp x (dp))))
  :hints (("Goal" :in-theory (enable snanp qnanp))))

(local-in-theory (disable fzerp))

(local-defthmd opbsnan-nanp
  (equal (opbsnan)
         (if (and (not (and (infp (opb) (dp)) (or (zerp (opc) (dp)) (fzerp (opc) (fzp)))))
	    	  (not (and (infp (opc) (dp)) (or (zerp (opb) (dp)) (fzerp (opb) (fzp)))))
		  (not (= (dnp) 1))
		  (or (snanp (opb) (dp))
	   	      (snanp (opc) (dp))))
	     1 0))
  :hints (("Goal" :in-theory (enable snanp-nanp inz-rewrite bits-cat bvecp-opb bvecp-opc opbsnan-nanp-1 fmul-special-val))))

(local-defthmd opbqnan-nanp-1
  (equal (opbqnan)
         (if (and (= (inz) 1) (qnanp (bits (opd) 116 53) (dp)))
	     1 0))
  :hints (("Goal" :in-theory (enable qnanp opbqnan nanp opbnan expf dp expb encodingp unsupp opbz expnt checkdenorm
                                     bitn-bits opblong fracb manf frac)
	          :use ((:instance bits-plus-bits (x (opd)) (n 104) (p 53) (m 0))))))

(local-defthmd snan-qnan
  (implies (snanp x (dp))
           (not (qnanp x (dp))))
  :hints (("Goal" :in-theory (enable snanp qnanp))))

(local-defthmd opbqnan-nanp
  (equal (opbqnan)
         (if (or (and (infp (opb) (dp)) (or (zerp (opc) (dp)) (fzerp (opc) (fzp))))
	    	 (and (infp (opc) (dp)) (or (zerp (opb) (dp)) (fzerp (opb) (fzp))))
		 (and (= (dnp) 1) (or (nanp (opb) (dp)) (nanp (opc) (dp))))
		 (and (not (snanp (opb) (dp)))
		      (not (snanp (opc) (dp)))
		      (or (qnanp (opb) (dp))
	   	          (qnanp (opc) (dp)))))
	     1 0))
  :hints (("Goal" :in-theory (enable snan-qnan snanp-nanp inz-rewrite bits-cat bvecp-opb bvecp-opc opbqnan-nanp-1 fmul-special-val))))

(local-defthmd opbinf-infp-1
  (equal (opbinf)
         (if (and (= (inz) 1) (infp (bits (opd) 116 53) (dp)))
	     1 0))
  :hints (("Goal" :in-theory (enable infp opbinf expf dp expb encodingp unsupp opbz expnt checkdenorm opblong fracb
                                     manf frac)
	          :use ((:instance bits-plus-bits (x (opd)) (n 104) (p 53) (m 0))))))

(local-defthm infp-bits-iencode
  (infp (bits (iencode s (dp)) 63 0) (dp))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp iencode infp encodingp expf manf cat))))

(local-defthm infp-bits-zencode
  (not (infp (bits (zencode s (dp)) 63 0) (dp)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x s) (n 0))) :in-theory (enable unsupp dp zencode infp encodingp expf manf cat))))

(local-defthm infp-bits-indef
  (not (infp (bits (indef (dp)) 63 0) (dp)))
  :hints (("Goal" :in-theory (enable unsupp dp zencode infp encodingp expf manf cat))))

(local-defthmd opbinf-infp
  (equal (opbinf)
         (if (and (not (and (infp (opb) (dp)) (or (zerp (opc) (dp)) (fzerp (opc) (fzp)))))
	    	  (not (and (infp (opc) (dp)) (or (zerp (opb) (dp)) (fzerp (opb) (fzp)))))
		  (not (nanp (opb) (dp)))
		  (not (nanp (opc) (dp)))
		  (or (infp (opb) (dp))
		      (infp (opc) (dp))))
	     1 0))
  :hints (("Goal" :in-theory (enable snan-qnan snanp-nanp inz-rewrite bits-cat bvecp-opb bvecp-opc opbinf-infp-1 fmul-special-val))))

(local-defthm shift-53-115-105
  (implies (integerp x)
           (equal (bits (* 9007199254740992 x) 115 105)
	          (bits x 62 52)))
  :hints (("Goal" :use ((:instance bits-shift-up-1 (k 53) (i 115) (j 105))))))

(local-defthm shift-53-116-105
  (implies (integerp x)
           (equal (bits (* 9007199254740992 x) 116 105)
	          (bits x 63 52)))
  :hints (("Goal" :use ((:instance bits-shift-up-1 (k 53) (i 116) (j 105))))))

(local-defthm shift-105-115-105
  (implies (integerp x)
           (equal (bits (* 40564819207303340847894502572032 x) 115 105)
	          (bits x 10 0)))
  :hints (("Goal" :use ((:instance bits-shift-up-1 (k 105) (i 115) (j 105))))))

(local-defthm shift-105-104-0
  (implies (integerp x)
           (equal (bits (* 40564819207303340847894502572032 x) 104 0)
	          0))
  :hints (("Goal" :use ((:instance bits-shift-up-1 (k 105) (i 104) (j 0))))))

(local-defthm shift-53-104-0
  (implies (integerp x)
           (equal (bits (* 9007199254740992 x) 104 0)
	          (* 9007199254740992 (bits x 51 0))))
  :hints (("Goal" :use ((:instance bits-shift-up-2 (k 53) (i 51))))))

(local-defthm shift-53-104
  (implies (integerp x)
           (equal (bitn (* 9007199254740992 x) 104)
	          (bitn x 51)))
  :hints (("Goal" :use ((:instance bitn-shift-up (k 53) (n 51))))))

(local-defthm shift-53-116
  (implies (integerp x)
           (equal (bitn (* 9007199254740992 x) 116)
	          (bitn x 63)))
  :hints (("Goal" :use ((:instance bitn-shift-up (k 53) (n 63))))))

(local-defthm int-opa
  (integerp (opa))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (bvecp-opa))))

(local-defthmd opanan-nanp
  (equal (opanan)
         (if (nanp (opa) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable nanp opanan expf dp expa encodingp unsupp opaz expnt checkdenorm fraca
                                     bvecp-opa cat opax manf frac))))

(local-defthmd opasnan-nanp
  (equal (opasnan)
         (if (snanp (opa) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable snanp opasnan nanp opanan expf dp expa encodingp unsupp opaz expnt checkdenorm
                                     bvecp-opa cat opax bitn-bits fraca manf frac))))

(local-defthmd opaqnan-nanp
  (equal (opaqnan)
         (if (qnanp (opa) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable qnanp opaqnan nanp opanan expf dp expa encodingp unsupp opaz expnt checkdenorm
                                     bvecp-opa cat opax bitn-bits fraca manf frac))))

(local-defthmd opainf-infp
  (equal (opainf)
         (if (infp (opa) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable infp opainf expf dp expa encodingp unsupp opaz expnt checkdenorm fraca
                                     bvecp-opa cat opax manf frac))))

(local-defthmd opazero-zerop
  (equal (opazero)
         (if (= (a) 0)
	     1 0))
  :hints (("Goal" :in-theory (enable zerop opazero expf dp expa encodingp unsupp opaz expnt checkdenorm fraca
                                     cat opax fzp sigf sgnf decode ndecode ddecode a manf frac))))

(local-defthmd opbzero-zerop-1
  (implies (and (fmul64-fused-special-p (opb) (opc) (fzp))
                (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0))
           (equal (opd)
                  (cat (zencode (logxor (bitn (opb) 63) (bitn (opc) 63)) (dp)) 64 0 53)))
  :hints (("Goal" :in-theory (enable snanp-nanp fmul-special-val opbqnan-nanp opbsnan-nanp opbinf-infp piz-rewrite piz-1))))

(local-defthmd opbzero-zerop-2
  (implies (and (fmul64-fused-special-p (opb) (opc) (fzp))
                (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0))
           (member (opd) (list 0 (expt 2 116))))
  :hints (("Goal" :in-theory (enable explicitp dp expw sigw opbzero-zerop-1 cat zencode)
                  :use ((:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance bitn-0-1 (x (opc)) (n 63))))))

(local-defthm special-mulstk-mulovfl
  (implies (fmul64-fused-special-p (opb) (opc) (fzp))
           (and (equal (mulovfl) 0)
	        (equal (mulstk) 0)))
  :hints (("Goal" :use (fmul64-result)
                  :in-theory (enable fmul64-fused-spec fmul64-fused-special mulovfl mulstk))))

(local-defthmd opbzero-zerop-3
  (implies (and (fmul64-fused-special-p (opb) (opc) (fzp))
                (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0))
           (equal (opbzero) 1))
  :hints (("Goal" :in-theory (enable opbzero frac fracb expb expf expnt dp)
                  :use (opbzero-zerop-2))))

(local-defthmd opbzero-zerop-4
  (implies (and (fmul64-fused-special-p (opb) (opc) (fzp))
                (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0))
           (equal (opbzero)
	          (if (= (p) 0)
	              1 0)))
  :hints (("Goal" :use (opbzero-zerop-3 zerp-fzerp-b zerp-fzerp-c)
                  :in-theory (enable piz-1 piz-rewrite opbqnan-nanp opbinf-infp opbsnan-nanp snanp-nanp fmul64-fused-special-p p))))

(local-defthmd opbzero-zerop-5
  (implies (not (fmul64-fused-special-p (opb) (opc) (fzp)))
           (equal (opbzero) 0))
  :hints (("Goal" :use (fmul64-result comp-1 comp-2
			(:instance bitn-0-1 (x (opb)) (n 63))
			(:instance bitn-0-1 (x (opc)) (n 63))
                        (:instance bits-plus-bits (x (opd)) (n 104) (p 52) (m 0)))
                  :in-theory (e/d (inz-rewrite zencode cat sgnf expw sigw prec dp snanp qnanp opblong mulovfl mulstk expnt p fmul64-fused-comp fmul64-fused-spec opbzero frac fracb expb)
		                  (fmul64-fused-special-p)))))

(local-defthmd opbzero-zerop
  (implies (and (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0))
           (equal (opbzero)
                  (if (= (p) 0)
                      1 0)))
  :hints (("Goal" :use (opbzero-zerop-4 opbzero-zerop-5 comp-1))))

(local-defthmd sum-0-1
  (iff (equal (a) 0)
       (and (equal (expa) 0)
            (equal (fraca) 0)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode opaz sigw expw dp fraca frac checkdenorm expnt expf opax expa a
                              sigf cat fzp))))

(local-defthm sum-0-2
  (implies (and (fmul64-fused-special-p (opb) (opc) (fzp))
                (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0))
           (iff (= (+ (a) (p)) 0)
                (if (= (signa) (signb))
                    (and (= (a) 0) (= (p) 0))
                  (and (= (mulovfl) 0)
		       (= (mulstk) 0)
		       (= (expa) (expb))
                       (= (fraca) (fracb))))))
  :rule-classes ()
  :hints (("Goal" :use (sum-0-1 opbzero-zerop-3 opbzero-zerop-4)
                  :in-theory (enable opbzero))))

(local-defthmd sum-0-3
  (implies (not (= (a) 0))
           (equal (signa)
	          (if (< (a) 0) 1 0)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode a opaz opax sigw expw dp fraca frac
                              bitn-bits sigf manf sgnf checkdenorm expnt expf expb b fzp sign signa))))

(local-defthmd sum-0-4
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (not (= (p) 0)))
           (equal (signb)
	          (if (< (p) 0) 1 0)))
  :hints (("Goal" :in-theory (enable comp-2 sign fmul64-fused-spec fmul64-fused-comp p signb)
                  :use (fmul64-result))))

(local-defthm sum-0-5
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (signa) (signb)))
           (iff (= (+ (a) (p)) 0)
	        (and (= (a) 0) (= (p) 0))))
  :rule-classes ()
  :hints (("Goal" :use (sum-0-2 sum-0-3 sum-0-4))))

(local-in-theory (disable bvecp-expovfl))

(local-defthmd sum-0-6
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 1))
           (>= (abs (p)) (expt 2 1025)))
  :hints (("Goal" :in-theory (enable bvecp comp-2 mulovfl fmul64-fused-spec fmul64-fused-comp p signb)
                  :use (bvecp-expovfl fmul64-result))))

(local-defthmd sum-0-7
  (implies (and (not (nanp (opa) (dp)))
                (not (infp (opa) (dp))))
	   (< (bits (opa) 62 52) 2047))
  :hints (("Goal" :in-theory (enable dp nanp infp expf expw manf encodingp unsupp bvecp-opa)
                  :use ((:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(local-defthmd sum-0-8
  (implies (and (not (nanp (opa) (dp)))
                (not (infp (opa) (dp))))
	   (< (abs (a)) (expt 2 1024)))
  :hints (("Goal" :in-theory (enable dp sigf decode a ndecode ddecode expf expw manf encodingp unsupp bvecp-opa)
                  :use (sum-0-7 (:instance bits-bounds (x (opa)) (i 51) (j 0)))
		  :nonlinearp t)))

(local-defthmd sum-0-9
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (not (nanp (opa) (dp)))
                (not (infp (opa) (dp)))
		(= (mulovfl) 1))
           (> (abs (+ (a) (p))) (expt 2 1024)))
  :hints (("Goal" :use (sum-0-6 sum-0-8))))

(local-defund siga ()
  (if (= (expa) 0)
      (* 2 (fraca))
    (+ (expt 2 106) (* 2 (fraca)))))

(local-defund sigb ()
  (if (= (expb) 0)
      (* 2 (fracb))
    (+ (expt 2 106) (* 2 (fracb)))))

(local-in-theory (disable (siga) (sigb)))

(local-defthmd sum-0-10
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(> (expb) 0))
           (and (equal (abs (p)) (absval (expb) (sigb)))
	  	(equal (mulstk) 0)))
  :hints (("Goal" :in-theory (enable absval sigb expb bvecp comp-2 mulovfl mulstk opblong fmul64-fused-spec fmul64-fused-comp
                                     frac fracb expnt expf p signb)
                  :use (bvecp-expovfl fmul64-result))))

(local-defthmd sum-0-11
  (equal (abs (a))
         (absval (expa) (siga)))
  :hints (("Goal" :in-theory (enable sign signa bitn-bits sigf manf sgnf sigw expw decode ddecode ndecode opaz sigw
                              siga absval cat expw dp fraca frac checkdenorm expnt expf opax expa a fzp))))

(local-defthmd sum-0-12
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(= (expb) 0))
           (and (<= (* (expt 2 (- -52 (1- (expt 2 10))))
		       (bits (opd) 104 52))
                    (abs (p)))
	        (< (abs (p))
	           (* (expt 2 (- -52 (1- (expt 2 10))))
	              (1+ (bits (opd) 104 52))))
	        (iff (= (* (expt 2 (- -52 (1- (expt 2 10))))
	                   (bits (opd) 104 52))
	                (abs (p)))
	             (and (equal (bits (opd) 51 0) 0)
	                  (equal (mulstk) 0)))))
  :hints (("Goal" :in-theory (enable absval sigb expb bvecp comp-2 mulovfl mulstk opblong fmul64-fused-spec fmul64-fused-comp
                                     frac fracb expnt expf p signb)
                  :use (bvecp-expovfl fmul64-result))))

(local-defthmd sum-0-13
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (and (equal (bits (opd) 51 0) 0)
	             (equal (mulstk) 0))))
	   (not (integerp (* (expt 2 1075) (abs (p))))))
  :hints (("Goal" :nonlinearp t
                  :use (sum-0-12))))

(local-defthmd sum-0-14
  (integerp (* (expt 2 1075) (abs (a))))
  :hints (("Goal" :in-theory (enable sign signa bitn-bits sigf manf sgnf sigw expw decode ddecode ndecode opaz sigw
                              siga absval cat expw dp fraca frac checkdenorm expnt expf opax expa a fzp))))

(local-defthmd sum-0-15
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (and (equal (bits (opd) 51 0) 0)
	             (equal (mulstk) 0))))
	   (not (equal (abs (a)) (abs (p)))))
  :hints (("Goal" :use (sum-0-13 sum-0-14))))

(local-defthmd sum-0-16
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (and (equal (bits (opd) 51 0) 0)
	             (equal (mulstk) 0))))
	   (not (equal (+ (a) (p)) 0)))
  :hints (("Goal" :use (sum-0-15))))

(local-defthmd sum-0-17
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(= (expb) 0)
		(not (equal (bits (opd) 51 0) 0)))
	   (not (equal (fraca) (fracb))))
  :hints (("Goal" :in-theory (enable cat opax opaz checkdenorm frac fraca fracb)
                  :use ((:instance bits-plus-bits (x (opd)) (n 104) (p 52) (m 0))
		        (:instance bits-plus-bitn (x (opd)) (n 104) (m 52))
			(:instance bits-bounds (x (opd)) (i 51) (j 0))
			(:instance bitn-0-1 (x (opd)) (n 52))))))

(local-defthmd sum-0-18
  (implies (and (not (fmul64-fused-special-p (opb) (opc) (fzp)))
                (= (mulovfl) 0)
		(= (expb) 0)
		(equal (bits (opd) 51 0) 0)
	        (equal (mulstk) 0))
	   (equal (abs (p))
	          (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-12 (:instance bits-plus-bits (x (opd)) (n 104) (p 52) (m 0)))
                  :in-theory (enable absval sigb frac fracb))))

(local-defthmd bvecp-frac
  (and (bvecp (fraca) 105)
       (bvecp (fracb) 105))
  :hints (("Goal" :in-theory (enable frac fraca fracb))))

(local-defthmd sum-0-19
  (and (implies (not (= (expa) 0)) (> (* 2 (siga)) (sigb)))
       (implies (not (= (expb) 0)) (> (* 2 (sigb)) (siga))))
  :hints (("Goal" :in-theory (enable siga sigb) :use (bvecp-frac))))

(local-defthmd sum-0-20
  (and (implies (and (not (= (expa) 0)) (= (expb) 0)) (> (siga) (sigb)))
       (implies (and (not (= (expb) 0)) (= (expa) 0)) (> (sigb) (siga))))
  :hints (("Goal" :in-theory (enable siga sigb) :use (bvecp-frac))))

(local-defthmd hack-1
  (implies (not (zp n))
           (>= (expt 2 n) 2)))

(local-defthmd sum-0-21
  (implies (< (expa) (expb))
           (>= (expt 2 (- (expb) (expa))) 2))
  :hints (("Goal" :use ((:instance hack-1 (n (- (expb) (expa))))))))

(local-defthmd sum-0-22
  (implies (< (expa) (expb))
           (< (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-19 sum-0-20 sum-0-21) :in-theory (enable absval) :nonlinearp t)))

(local-defthmd hack-2
  (implies (not (zp n))
           (<= (expt 2 (- n)) 1/2)))

(local-defthmd sum-0-23
  (implies (> (expa) (expb))
           (<= (expt 2 (- (expb) (expa))) 1/2))
  :hints (("Goal" :use ((:instance hack-2 (n (- (expa) (expb))))))))

(local-defthmd sum-0-24
  (implies (and (> (expa) (expb)) (= (expb) 0))
           (> (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-19 sum-0-20 sum-0-23) :in-theory (enable absval) :nonlinearp t)))

(local-defthmd sum-0-25
  (implies (> (expa) (expb))
           (> (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-19 sum-0-20 sum-0-23) :in-theory (enable absval) :nonlinearp t)))

(local-defthm hack-3
  (implies (and (rationalp x) (rationalp z) (not (= z 0))
                (= (* x z) 0))
	   (= x 0))
  :hints (("Goal" :nonlinearp t))
  :rule-classes ())

(local-defthm hack-4
  (implies (and (rationalp x) (rationalp y) (rationalp z) (not (= z 0))
                (= (* x z) (* y z)))
	   (= x y))
  :hints (("Goal" :use ((:instance hack-3 (x (- x y))))))
  :rule-classes ())

(local-defthmd sum-0-26
  (implies (and (= (expa) (expb))
                (= (absval (expa) (siga)) (absval (expb) (sigb))))
           (equal (fraca) (fracb)))
  :hints (("Goal" :in-theory (enable absval siga sigb)
                  :use ((:instance hack-4 (x (fraca)) (y (fracb)) (z (expt 2 (+ -1128 (expa)))))))))

(local-defthmd sum-0-27
  (implies (= (absval (expa) (siga)) (absval (expb) (sigb)))
              (and (equal (expa) (expb))
                   (equal (fraca) (fracb))))
  :hints (("Goal" :use (sum-0-26 sum-0-25 sum-0-22))))

(local-defthmd sum-0-28
  (iff (= (absval (expa) (siga)) (absval (expb) (sigb)))
       (and (equal (expa) (expb))
            (equal (fraca) (fracb))))
  :hints (("Goal" :use (sum-0-27) :in-theory (enable siga sigb))))

(local-defthm sum-0-29
  (implies (and (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0)
                (not (nanp (opa) (dp)))
                (not (infp (opa) (dp))))
           (iff (= (+ (a) (p)) 0)
                (if (= (signa) (signb))
                    (and (= (a) 0) (= (p) 0))
                  (and (= (expa) (expb))
                       (= (fraca) (fracb))
	               (= (mulstk) 0)
	               (= (mulovfl) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (sum-0-3 sum-0-4 sum-0-10 sum-0-16 sum-0-17 sum-0-18 sum-0-2 sum-0-9 sum-0-7 sum-0-11 sum-0-28)
                  :in-theory (enable mulovfl mulstk))))

(local-defthm sum-0
  (implies (and (= (opbsnan) 0)
                (= (piz-1) 0)
                (= (opbqnan) 0)
                (= (opbinf) 0)
                (= (opasnan) 0)
                (= (opaqnan) 0)
                (= (opainf) 0))
           (iff (= (+ (a) (p)) 0)
                (if (= (signa) (signb))
                    (and (= (a) 0) (= (p) 0))
                  (and (= (expa) (expb))
                       (= (fraca) (fracb))
	               (= (mulstk) 0)
	               (= (mulovfl) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (sum-0-29)
                  :in-theory (enable opasnan-nanp opaqnan-nanp opainf-infp qnanp snanp))))

(local-defthmd isspecial-specialp
  (equal (isspecial)
         (if (specialp) 1 0))
  :hints (("Goal" :in-theory (enable checkspecial-lemma specialp isspecial* opaqnan-nanp opasnan-nanp opbqnan-nanp opbsnan-nanp
                                     piz-1  piz-rewrite qnanp snanp opainf-infp opbinf-infp opazero-zerop opbzero-zerop)
		  :use (sum-0))))

(local-defthmd isspecial-0-flags
  (implies (= (isspecial) 0)
           (equal (flags-4) (flags-3)))
  :hints (("Goal" :in-theory (enable checkspecial-lemma specialp flags-4* isspecial* opaqnan-nanp opasnan-nanp opbqnan-nanp opbsnan-nanp
                                     piz-1 qnanp snanp opainf-infp opbinf-infp opazero-zerop opbzero-zerop))))

(local-defthm flags-1-0
  (and (equal (bitn (flags-1) 1) 0)
       (equal (bitn (flags-1) 2) 0)
       (equal (bitn (flags-1) 3) 0)
       (equal (bitn (flags-1) 4) 0)
       (equal (bitn (flags-1) 5) 0)
       (equal (bitn (flags-1) 6) 0))
  :hints (("Goal" :in-theory (enable flags-1 opblong bitn-bits fmul64-fused-comp fmul64-fused-special fmul64-fused-spec)
                  :use (fmul64-result))))

(local-defthmd flags-1-1
  (implies (not (fmul64-fused-special-p (opb) (opc) (fzp)))
           (and (not (snanp (opb) (dp)))
	        (not (snanp (opc) (dp)))
	        (not (fzerp (opb) (fzp)))
	        (not (fzerp (opc) (fzp)))
                (not (inf-times-zero (opb) (opc) (fzp)))))
  :hints (("Goal" :in-theory (enable snanp fmul64-fused-special-p inf-times-zero))))

(local-defthm flags-1-2
  (equal (bitn (flags-1) 0)
         (if (or (snanp (opb) (dp))
	         (snanp (opc) (dp))
		 (inf-times-zero (opb) (opc) (fzp)))
	     1 0))
  :hints (("Goal" :in-theory (enable bitn-bits flags-1 inf-times-zero fmul64-fused-spec fmul64-fused-special fmul64-fused-comp)
                  :use (fmul64-result flags-1-1))))

(local-defthm flags-1-3
  (equal (bitn (flags-1) 7)
         (if (or (fzerp (opb) (fzp))
	         (fzerp (opc) (fzp)))
	     1 0))
  :hints (("Goal" :in-theory (enable bitn-bits flags-1 inf-times-zero fmul64-fused-spec fmul64-fused-special fmul64-fused-comp)
                  :use (fmul64-result flags-1-1))))

(local-defthm flags-1-4
  (implies (and (natp k)
                (>= k 8))
           (equal (bitn (flags-1) k) 0))
  :hints (("Goal" :in-theory (enable flags-1))))

(local-defthm bvecp-flags-1
  (bvecp (flags-1) 8)
  :hints (("Goal" :in-theory (enable flags-1))))

(local-defthmd flags-1-vals
  (member (flags-1) '(0 1 128 129
                      32 33 160 161
		      64 65 192 193
		      96 97 224 225))
  :hints (("Goal" :use (flags-1-0 (:instance bvecp-member (x (flags-1)) (n 8)))
                  :in-theory (disable flags-1-0))))

(local-defthmd flags-3-rewrite-1
  (implies (and (natp k) (< k 8))
           (equal (bitn (flags-3) k)
	         (if (and (= k 7)
		          (= (fzp) 1)
			  (= (bits (opa) 62 52) 0)
			  (not (= (bits (opa) 51 0) 0)))
		     1
		   (bitn (flags-1) k))))
  :hints (("Goal" :in-theory (enable flags-2 flags-3 checkdenorm opaz expnt expf expa opax fzp frac fraca
                                     bvecp bitn-bits cat)
		  :use (flags-1-vals (:instance bvecp-member (x k) (n 3))))))

(local-defthmd flags-3-rewrite-2
  (implies (and (natp k) (>= k 8))
           (equal (bitn (flags-3) k)
		  (bitn (flags-1) k)))
  :hints (("Goal" :in-theory (enable flags-2 flags-3 checkdenorm opaz expnt expf expa opax fzp frac fraca
                                     bvecp bitn-bits cat)
		  :use (flags-1-vals (:instance bitn-expt-0 (i 7) (n k))))))

(local-defthmd flags-3-rewrite-3
  (implies (natp k)
           (equal (bitn (flags-3) k)
	         (if (and (= k 7)
		          (= (fzp) 1)
			  (= (bits (opa) 62 52) 0)
			  (not (= (bits (opa) 51 0) 0)))
		     1
		   (bitn (flags-1) k))))
  :hints (("Goal" :use (flags-3-rewrite-1 flags-3-rewrite-2))))

(local-defthmd flags-3-rewrite-4
  (iff (denormp (opa) (dp))
       (and (= (bits (opa) 62 52) 0)
	    (not (= (bits (opa) 51 0) 0))))
  :hints (("Goal" :use (bvecp-opa)
                  :in-theory (enable sigf denormp encodingp dp expw sigw expnt expf manf))))

(local-defthmd flags-3-rewrite
  (implies (natp k)
           (equal (bitn (flags-3) k)
	         (if (and (= k 7)
		          (= (fzp) 1)
			  (denormp (opa) (dp)))
		     1
		   (bitn (flags-1) k))))
  :hints (("Goal" :use (flags-3-rewrite-3 flags-3-rewrite-4))))

(local-defthmd flags-5-rewrite
  (implies (member k '(0 1 5 6 7))
           (equal (bitn (flags-5) k)
	          (bitn (flags-4) k)))
  :hints (("Goal" :in-theory (enable flags-5 bitn-cat bitn-bits))))

(local-defund opad ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opa) (dp)))
      (zencode (sgnf (opa) (dp)) (dp))
     (opa)))

(local-defund opbd ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opb) (dp)))
      (zencode (sgnf (opb) (dp)) (dp))
     (opb)))

(local-defund opcd ()
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opc) (dp)))
      (zencode (sgnf (opc) (dp)) (dp))
     (opc)))

(local-in-theory (disable (opad) (opbd) (opcd)))

(local-defthmd arm-fma-spec-rewrite
  (equal (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
         (let ((d (arm-fma-pre-comp-val (opad) (opbd) (opcd) (rz) (dp)))
               (r (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp))))
	   (if d (mv d r)
	       (arm-fma-comp (opad) (opbd) (opcd) r (dp)))))
  :hints (("Goal" :in-theory (enable dp hp opad opbd opcd rz))))

(local-in-theory (disable arm-fma-spec))

(local-defthmd nanp-infp-zencode
  (and (not (nanp (zencode (sgnf x (dp)) (dp)) (dp)))
       (not (infp (zencode (sgnf x (dp)) (dp)) (dp))))
  :hints (("Goal" :in-theory (enable encodingp unsupp expf manf sgnf manf cat dp expw sigw zencode infp nanp)
                  :use ((:instance bitn-0-1 (n 63))))))

(local-defthmd final-1
  (implies (not (specialp))
           (equal (arm-fma-pre-comp-val (opad) (opbd) (opcd) (rz) (dp))
                  ()))
  :hints (("Goal" :in-theory (enable opad opbd opcd snanp qnanp specialp fma-undefined-p)
                  :use ((:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opb)))
		        (:instance nanp-infp-zencode (x (opc)))))))

(local-defthmd final-2
  (implies (not (specialp))
           (equal (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp))
                  (rz)))
  :hints (("Goal" :in-theory (enable opad opbd opcd specialp snanp qnanp fma-undefined-p)
                  :use ((:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opb)))
		        (:instance nanp-infp-zencode (x (opc)))))))

(local-defthmd final-3
  (implies (not (specialp))
           (equal (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
                  (arm-fma-comp (opad) (opbd) (opcd) (rz) (dp))))
  :hints (("Goal" :in-theory (enable arm-fma-spec-rewrite)
                  :use (final-1 final-2))))

(local-in-theory (disable arm-post-comp (arm-post-comp) arm-fma-spec (arm-fma-spec)))

(local-defthmd final-4
  (implies (not (specialp))
           (and (equal (decode (opad) (dp)) (a))
	        (equal (decode (opbd) (dp)) (b))
	        (equal (decode (opcd) (dp)) (c))))
  :hints (("Goal" :in-theory (enable expw sigw encodingp sigf sgnf denormp decode ddecode expf a b c opad opbd opcd
                                     specialp bvecp-opa bvecp-opb bvecp-opc zencode bitn-bits dp prec bias))))

(local-defthmd final-5
  (implies (not (specialp))
           (equal (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
                  (arm-post-comp (+ (a) (* (b) (c))) (rz) (dp))))
  :hints (("Goal" :in-theory (enable p opad opbd opcd specialp final-3)
                  :use (final-4
		        (:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opb)))
		        (:instance nanp-infp-zencode (x (opc)))))))

(local-defthm final-6
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (bitn (logior (rz) (flags)) 4) (bitn r-spec 4))
                  (equal (bitn (logior (rz) (flags)) 3) (bitn r-spec 3))
                  (equal (bitn (logior (rz) (flags)) 2) (bitn r-spec 2)))))
  :rule-classes ()
  :hints (("Goal" :use (fma-comp)
                  :in-theory (enable p final-5))))

(local-defthm final-7
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (bitn (logior (rin) (flags)) 4) (bitn r-spec 4))
                  (equal (bitn (logior (rin) (flags)) 3) (bitn r-spec 3))
                  (equal (bitn (logior (rin) (flags)) 2) (bitn r-spec 2)))))
  :rule-classes ()
  :hints (("Goal" :use (final-6 bvecp-rin bvecp-rz)
                  :in-theory (e/d (bitn-logior) (bvecp-rz)))))

(local-defthmd flags-other
  (implies (and (not (specialp)) (member k '(0 1 5 6 7)))
           (equal (bitn (flags) k)
	          (if (and (= k 7)
		           (= (fzp) 1)
			   (or (denormp (opa) (dp))
			       (denormp (opb) (dp))
			       (denormp (opc) (dp))))
		      1
		    0)))
  :hints (("Goal" :in-theory (enable fzerp qnanp snanp specialp inf-times-zero fzp isspecial-0-flags flags flags-3-rewrite flags-5-rewrite isspecial-specialp flags-1-0))))

(local-defthmd post-comp-bitn-other
  (implies (and (natp k) (not (member k '(2 3 4))))
           (equal (bitn (mv-nth 1 (arm-post-comp (+ (a) (* (b) (c))) (rz) (dp))) k)
	          (bitn (rz) k)))
  :hints (("Goal" :in-theory (e/d (arm-post-comp) (bvecp-rz bvecp-set-flag))
                  :use (bvecp-rz))))

(local-defthmd r-spec-bitn-other
  (implies (and (not (specialp)) (natp k) (not (member k '(2 3 4))))
           (equal (bitn (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))) k)
	          (bitn (rz) k)))
  :hints (("Goal" :in-theory (enable final-5)
                  :use (post-comp-bitn-other))))

(local-defthmd bitn-rz
  (implies (natp k)
           (equal (bitn (rz) k)
	          (if (and (= k 7)
		           (= (fzp) 1)
			   (or (denormp (opa) (dp))
			       (denormp (opb) (dp))
			       (denormp (opc) (dp))))
		      1
		    (bitn (rin) k))))
  :hints (("Goal" :in-theory (enable bvecp-opa bvecp-opb bvecp-opc fzp denormp rz sigw expw encodingp prec dp explicitp sigf expf)
                  :use (bvecp-rin))))

(local-defthmd bvecp-flags
  (bvecp (flags) 8)
  :hints (("Goal" :in-theory (enable checkdenorm flags-5 flags-1 flags-2 flags-3 flags-4* checkspecial-lemma flags))))

(local-defthmd bvecp-logior-flags
  (bvecp (logior (rin) (flags)) 32)
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-rin bvecp-flags (:instance logior-bvecp (n 32) (x (flags)) (y (rin)))))))

(local-defthmd bvecp-r-spec
  (bvecp (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))) 32)
  :hints (("Goal" :in-theory (enable arm-post-comp arm-fma-spec-rewrite))))

(local-defthmd final-8
  (implies (and (not (specialp)) (natp k) (< k 32) (not (member k '(2 3 4))))
           (equal (bitn (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))) k)
	          (bitn (logior (rin) (flags)) k)))
  :hints (("Goal" :in-theory (e/d (bvecp bitn-logior r-spec-bitn-other bitn-rz flags-other) (flags))
                  :use (bvecp-flags final-7 bvecp-rin (:instance bvecp-member (x k) (n 5))))))

(local-defthmd final-9
  (implies (and (not (specialp)) (natp k))
           (equal (bitn (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))) k)
	          (bitn (logior (rin) (flags)) k)))
  :hints (("Goal" :in-theory (enable bvecp) :use (final-8 final-7 bvecp-r-spec bvecp-logior-flags))))

(local-defthmd final-10
  (implies (not (specialp))
           (equal (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))
	          (logior (rin) (flags))))
  :hints (("Goal" :use (bvecp-r-spec bvecp-logior-flags
                        (:instance bit-diff-diff (x (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))))
                                                 (y (logior (rin) (flags))))
			(:instance final-9 (k (bit-diff (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))
			                                (logior (rin) (flags)))))))))

(local-defthm comp-case
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :rule-classes ()
  :hints (("Goal" :use (final-7 final-10))))


;;*******************************************************************************
;; Special Case
;;*******************************************************************************

(local-defthmd opaz-opad
  (equal (opaz) (* (expt 2 53) (opad)))
  :hints (("Goal" :use (bvecp-opa
                        (:instance bitn-plus-bits (x (opa)) (n 63) (m 52))
                        (:instance bits-shift-up-2 (x (opa)) (k 53) (i 63)))
                  :in-theory (enable bits-bits expnt expf cat denormp encodingp dp sigf frac bits-cat opaz checkdenorm
		                     zencode sgnf opad opax fzp))))

(local-defthmd bvecp-opad
  (bvecp (opad) 64)
  :hints (("Goal" :use (bvecp-opa)
                  :in-theory (enable bits-bits expnt expf cat encodingp dp sigf frac bits-cat opaz
		                     bvecp zencode sgnf opad opax fzp))))


(local-defthmd bits-opaz-opad
  (equal (bits (opaz) 116 53) (opad))
  :hints (("Goal" :use (bvecp-opad
                        (:instance bits-shift-up-1 (x (opad)) (k 53) (i 116) (j 53)))
                  :in-theory (enable opaz-opad))))

(local-defthmd zerp-zencode
  (zerp (zencode (sgnf x (dp)) (dp)) (dp))
  :hints (("Goal" :in-theory (enable zerp encodingp unsupp expf manf sgnf manf cat dp expw sigw zencode infp nanp)
                  :use ((:instance bitn-0-1 (n 63))))))

(local-defthmd piz-1-rewrite
  (equal (piz-1)
         (if (or (and (infp (opbd) (dp)) (zerp (opcd) (dp)))
		 (and (infp (opcd) (dp)) (zerp (opbd) (dp))))
	     1 0))
  :hints (("Goal" :in-theory (enable zerp-zencode nanp-infp-zencode fzp fzerp piz-1 piz-rewrite opbd opcd))))

(local-defthmd opa-opad
  (and (iff (snanp (opad) (dp)) (snanp (opa) (dp)))
       (iff (qnanp (opad) (dp)) (qnanp (opa) (dp)))
       (iff (infp (opad) (dp)) (infp (opa) (dp)))
       (implies (or (snanp (opa) (dp)) (qnanp (opa) (dp)) (infp (opa) (dp)))
                (equal (opad) (opa))))
  :hints (("Goal" :in-theory (enable nanp-infp-zencode snanp qnanp opad))))

(local-defthmd opb-opbd
  (and (iff (snanp (opbd) (dp)) (snanp (opb) (dp)))
       (iff (qnanp (opbd) (dp)) (qnanp (opb) (dp)))
       (iff (infp (opbd) (dp)) (infp (opb) (dp)))
       (implies (or (snanp (opb) (dp)) (qnanp (opb) (dp)) (infp (opb) (dp)))
                (equal (opbd) (opb))))
  :hints (("Goal" :in-theory (enable nanp-infp-zencode snanp qnanp opbd))))

(local-defthmd opc-opcd
  (and (iff (snanp (opcd) (dp)) (snanp (opc) (dp)))
       (iff (qnanp (opcd) (dp)) (qnanp (opc) (dp)))
       (iff (infp (opcd) (dp)) (infp (opc) (dp)))
       (implies (or (snanp (opc) (dp)) (qnanp (opc) (dp)) (infp (opc) (dp)))
                (equal (opcd) (opc))))
  :hints (("Goal" :in-theory (enable nanp-infp-zencode snanp qnanp opcd))))

(local-defthm final-11
  (equal (BITS (* 9007199254740992 (OPA)) 116 53)
         (opa))
  :hints (("Goal" :use (bvecp-opa (:instance bits-shift-up-1 (x (opa)) (k 53) (i 116) (j 53))))))

(local-defthm nanp-zerp
  (implies (nanp x (dp))
           (and (not (zerp x (dp)))
	        (not (fzerp x (fzp)))))
  :hints (("Goal" :in-theory (enable dp sigw expw encodingp nanp denormp zerp fzerp))))

(local-defthm infp-zerp
  (implies (infp x (dp))
           (and (not (zerp x (dp)))
	        (not (fzerp x (fzp)))))
  :hints (("Goal" :in-theory (enable dp sigw expw encodingp infp denormp zerp fzerp))))

(local-defthm undef-val
  (EQUAL (INDEF (DP)) 9221120237041090560)
  :hints (("Goal" :in-theory (enable indef dp))))

(local-defthmd zerp-opcd
  (equal (zerp (opcd) (dp))
         (or (zerp (opc) (dp)) (fzerp (opc) (fzp))))
  :hints (("Goal" :in-theory (enable zerp-zencode fzp fzerp opcd))))

(local-defthmd zerp-opbd
  (equal (zerp (opbd) (dp))
         (or (zerp (opb) (dp)) (fzerp (opb) (fzp))))
  :hints (("Goal" :in-theory (enable zerp-zencode fzp fzerp opbd))))

(local-defthm z-
  (EQUAL (BINARY-CAT 1 1 0 (+ (EXPW (DP)) (SIGW (DP))))
         9223372036854775808)
  :hints (("Goal" :in-theory (enable dp cat expw sigw))))

(local-defthm expw-dp
  (equal (expw (dp)) 11)
  :hints (("Goal" :in-theory (enable dp cat expw sigw))))

(local-defthm sigw-dp
  (equal (sigw (dp)) 52)
  :hints (("Goal" :in-theory (enable dp cat expw sigw))))

(local-defthmd final-14
  (implies (specialp)
           (equal (d)
                  (if (snanp (opa) (dp))
	              (if1 (dnp) (defnan) (gag (opa)))
                    (if (snanp (opb) (dp))
                        (if1 (dnp) (defnan) (gag (opb)))
                      (if (snanp (opc) (dp))
                          (if1 (dnp) (defnan) (gag (opc)))
			(if (or (and (infp (opb) (dp)) (zerp (opcd) (dp)))
	  	                (and (infp (opc) (dp)) (zerp (opbd) (dp))))
			    (defnan)
                          (if (qnanp (opa) (dp))
                              (if1 (dnp) (defnan) (opa))
                            (if (qnanp (opb) (dp))
                                (if1 (dnp) (defnan) (opb))
                              (if (qnanp (opc) (dp))
                                  (if1 (dnp) (defnan) (opc))
                                (if (infp (opa) (dp))
                                    (if (and (or (infp (opb) (dp)) (infp (opc) (dp)))
				             (not (= (signa) (signb))))
                                        (defnan)
                                      (opa))
                                  (if (or (infp (opb) (dp)) (infp (opc) (dp)))
		                      (bits (iencode (logxor (bitn (opb) 63) (bitn (opc) 63)) (dp)) 63 0)
                                    (if (and (= (a) 0) (= (p) 0) (= (signa) (signb)))
                                        (zencode (signa) (dp))
                                      (if (= (+ (a) (p)) 0)
                                          (if (= (rmode) 2)
                                              (zencode 1 (dp))
		                            (zencode 0 (dp)))
			                0)))))))))))))
  :hints (("Goal" :in-theory (enable checkspecial-lemma d-1* d isspecial-specialp opbsnan-nanp opasnan-nanp opbqnan-nanp opaqnan-nanp
                                     opa-opad opb-opbd opc-opcd opainf-infp opbinf-infp piz-1-rewrite bvecp-opa zencode gag snanp qnanp
				     zerp-opbd zerp-opcd fmul-special-val fmul64-fused-special-p specialp opazero-zerop opbzero-zerop
				     bits-opaz-opad p bits-logior)
		  :use (bvecp-opa bvecp-opb bvecp-opc signa-0-1 signb-0-1 sum-0))))

(local-defthm final-15
  (implies (and (specialp)
                (not (snanp (opb) (dp)))
                (not (snanp (opc) (dp)))
                (not (qnanp (opb) (dp)))
                (not (qnanp (opc) (dp)))
                (not (and (infp (opbd) (dp)) (zerp (opcd) (dp))))
		(not (and (infp (opcd) (dp)) (zerp (opbd) (dp))))
		(or (infp (opb) (dp)) (infp (opc) (dp)) (= (p) 0)))
           (or (equal (opd) (ash (iencode (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp))) (dp)) 53))
	       (equal (opd) (ash (zencode (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp))) (dp)) 53))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable comp-2 sign FMUL64-FUSED-SPEC-SPECIAL-VAL fmul64-fused-spec fmul64-fused-special
                                     zerp-opbd zerp-opcd piz-rewrite opb-opbd opc-opcd specialp INF-TIMES-ZERO
				     snanp-nanp fmul64-fused-special-p fmul64-fused-comp p)
                  :use (fzerp-b-0 fzerp-c-0 fmul64-result))))

(local-defthm final-16
  (implies (or (equal (opd) (ash (iencode (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp))) (dp)) 53))
	       (equal (opd) (ash (zencode (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp))) (dp)) 53)))
           (equal (signb)
	          (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signb dp iencode zencode sgnf)
                  :use ((:instance bitn-0-1 (x (opb)) (n 63))
		        (:instance bitn-0-1 (x (opc)) (n 63))))))

(local-defthmd final-17
  (implies (and (specialp)
                (not (snanp (opb) (dp)))
                (not (snanp (opc) (dp)))
                (not (qnanp (opb) (dp)))
                (not (qnanp (opc) (dp)))
                (not (and (infp (opbd) (dp)) (zerp (opcd) (dp))))
		(not (and (infp (opcd) (dp)) (zerp (opbd) (dp))))
		(or (infp (opb) (dp)) (infp (opc) (dp)) (= (p) 0)))
           (equal (signb)
	          (logxor (sgnf (opb) (dp)) (sgnf (opc) (dp)))))
  :hints (("Goal" :use (final-15 final-16))))

(local-defthmd final-18
  (and (equal (sgnf (opad) (dp)) (sgnf (opa) (dp)))
       (equal (sgnf (opbd) (dp)) (sgnf (opb) (dp)))
       (equal (sgnf (opcd) (dp)) (sgnf (opc) (dp))))
  :hints (("Goal" :in-theory (enable sgnf dp zencode opad opbd opcd))))

(local-defthmd final-19
  (equal (signa) (sgnf (opad) (dp)))
  :hints (("Goal" :in-theory (enable bitn-bits zencode dp sgnf checkdenorm opax opaz opad signa sign))))

(local-defthmd final-20
  (equal (bitn x 63) (sgnf x (dp)))
  :hints (("Goal" :in-theory (enable sgnf dp))))

(local-defthmd d-rewrite
  (implies (specialp)
           (equal (d)
                  (if (snanp (opad) (dp))
	              (if1 (dnp) (defnan) (gag (opad)))
                    (if (snanp (opbd) (dp))
                        (if1 (dnp) (defnan) (gag (opbd)))
                      (if (snanp (opcd) (dp))
                          (if1 (dnp) (defnan) (gag (opcd)))
			(if (or (and (infp (opbd) (dp)) (zerp (opcd) (dp)))
	  	                (and (infp (opcd) (dp)) (zerp (opbd) (dp))))
			    (defnan)
                          (if (qnanp (opad) (dp))
                              (if1 (dnp) (defnan) (opad))
                            (if (qnanp (opbd) (dp))
                                (if1 (dnp) (defnan) (opbd))
                              (if (qnanp (opcd) (dp))
                                  (if1 (dnp) (defnan) (opcd))
                                (if (infp (opad) (dp))
                                    (if (and (or (infp (opbd) (dp)) (infp (opcd) (dp)))
				             (not (= (sgnf (opad) (dp)) (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp))))))
                                        (defnan)
                                      (opad))
                                  (if (or (infp (opbd) (dp)) (infp (opcd) (dp)))
		                      (bits (iencode (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp))) (dp)) 63 0)
                                    (if (and (= (a) 0) (= (p) 0) (= (sgnf (opad) (dp)) (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp)))))
                                        (zencode (sgnf (opad) (dp)) (dp))
                                      (if (= (+ (a) (p)) 0)
                                          (if (= (rmode) 2)
                                              (zencode 1 (dp))
		                            (zencode 0 (dp)))
			                0)))))))))))))
  :hints (("Goal" :in-theory (enable final-14 final-17 final-18 final-19 final-20 opa-opad opb-opbd opc-opcd))))

(local-defthmd final-21
  (implies (specialp)
           (equal (flags)
                  (if (snanp (opa) (dp))
                      (setbitn (flags-3) 8 0 1)
                    (if (or (and (infp (opb) (dp)) (zerp (opcd) (dp)))
	  	            (and (infp (opc) (dp)) (zerp (opbd) (dp))))
                        (flags-3)
                      (if (and (not (= (dnp) 1))
		               (or (snanp (opb) (dp)) (snanp (opc) (dp))))
                          (setbitn (flags-3) 8 0 1)
                        (if (or (qnanp (opa) (dp))
			        (qnanp (opb) (dp))
				(qnanp (opc) (dp))
				(snanp (opb) (dp))
				(snanp (opc) (dp)))
                            (flags-3)
			  (if (and (infp (opa) (dp))
			           (or (infp (opb) (dp)) (infp (opc) (dp)))
				   (not (= (signa) (signb))))
                              (setbitn (flags-3) 8 0 1)
                            (flags-3))))))))
  :hints (("Goal" :in-theory (enable checkspecial-lemma flags-4* flags isspecial-specialp opbsnan-nanp opasnan-nanp opbqnan-nanp opaqnan-nanp
                                     opa-opad opb-opbd opc-opcd opainf-infp opbinf-infp piz-1-rewrite bvecp-opa zencode gag snanp qnanp
				     zerp-opbd zerp-opcd fmul64-fused-special-p specialp opazero-zerop opbzero-zerop
				     bits-opaz-opad p bits-logior)
		  :use (bvecp-opa bvecp-opb bvecp-opc signa-0-1 signb-0-1 sum-0))))

(local-defthmd final-22
  (implies (specialp)
           (equal (flags)
                  (if (snanp (opad) (dp))
                      (setbitn (flags-3) 8 0 1)
                    (if (or (and (infp (opbd) (dp)) (zerp (opcd) (dp)))
	  	            (and (infp (opcd) (dp)) (zerp (opbd) (dp))))
                        (flags-3)
                      (if (and (not (= (dnp) 1))
		               (or (snanp (opbd) (dp)) (snanp (opcd) (dp))))
                          (setbitn (flags-3) 8 0 1)
                        (if (or (qnanp (opad) (dp))
			        (qnanp (opbd) (dp))
				(qnanp (opcd) (dp))
				(snanp (opbd) (dp))
				(snanp (opcd) (dp)))
                            (flags-3)
			  (if (and (infp (opad) (dp))
			           (or (infp (opbd) (dp)) (infp (opcd) (dp)))
				   (not (= (sgnf (opad) (dp))
			                   (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp))))))
                              (setbitn (flags-3) 8 0 1)
                            (flags-3))))))))
  :hints (("Goal" :in-theory (enable final-21 final-17 final-18 final-19 opa-opad opb-opbd opc-opcd))))

(local-defthmd bvecp-flags-3
  (bvecp (flags-3) 8)
  :hints (("Goal" :in-theory (enable flags-3 flags-2 flags-1 checkdenorm))))

(local-defthmd final-23
  (implies (and (specialp) (natp k) (not (member k '(0 7))))
           (equal (bitn (flags) k) 0))
  :hints (("Goal" :use ((:instance bvecp-member (x k) (n 3))) :in-theory (enable bitn-bits bvecp final-21 flags-3-rewrite))))

(local-defthmd final-24
  (implies (specialp)
           (equal (bitn (flags) 7)
	          (if (or (fzerp (opa) (fzp))
		          (fzerp (opb) (fzp))
		          (fzerp (opc) (fzp)))
		      1 0)))
  :hints (("Goal" :in-theory (enable bitn-bits fzerp final-21 flags-3-rewrite))))

(local-defthmd final-25
  (implies (specialp)
           (equal (bitn (flags) 0)
	          (if (or (snanp (opad) (dp))
		          (snanp (opbd) (dp))
		          (snanp (opcd) (dp))
		          (and (infp (opbd) (dp)) (zerp (opcd) (dp)))
	  	          (and (infp (opcd) (dp)) (zerp (opbd) (dp)))
			  (and (infp (opad) (dp))
			       (not (nanp (opbd) (dp)))
			       (not (nanp (opcd) (dp)))
			       (or (infp (opbd) (dp)) (infp (opcd) (dp)))
			       (not (= (sgnf (opad) (dp))
			               (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp)))))))
		      1 0)))
  :hints (("Goal" :in-theory (enable zerp-opbd zerp-opcd inf-times-zero snanp-nanp final-22 opa-opad opb-opbd opc-opcd flags-3-rewrite))))

(local-defthmd final-26
  (implies (snanp x (dp))
           (equal (process-nan x r (dp))
	          (if1 (bitn r 25) (defnan) (gag x))))
  :hints (("Goal" :in-theory (enable snanp nanp encodingp defnan indef dp qnanize gag bits-logior))))

(local-defthmd final-27
  (implies (qnanp x (dp))
           (equal (process-nan x r (dp))
	          (if1 (bitn r 25) (defnan) x)))
  :hints (("Goal" :in-theory (enable qnanp nanp encodingp defnan indef dp qnanize gag bits-logior)
                  :use ((:instance logior-2**n (n 51))))))

(local-in-theory (disable process-nan (process-nan)))

(local-in-theory (disable flags (flags)))

(local-defthmd final-28
  (implies (specialp)
           (equal (bitn (logior (flags) (rin)) 7)
	          (bitn (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp)) 7)))
  :hints (("Goal" :in-theory (enable rz fzerp fzp final-24 arm-fma-pre-comp-excp fma-undefined-p bitn-logior)
                  :use (bvecp-rin bvecp-flags))))

(local-defthmd final-29
  (implies (specialp)
           (equal (bitn (logior (flags) (rin)) 0)
	          (bitn (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp)) 0)))
  :hints (("Goal" :in-theory (enable snanp-nanp opa-opad opb-opbd opc-opcd rz fzp final-23 final-24 final-25 arm-fma-pre-comp-excp fma-undefined-p bitn-logior)
                  :use (bvecp-rin bvecp-flags))))

(local-defthmd final-30
  (implies (and (specialp) (natp k) (not (member k '(0 7))))
           (equal (bitn (logior (flags) (rin)) k)
	          (bitn (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp)) k)))
  :hints (("Goal" :in-theory (enable rz final-23 arm-fma-pre-comp-excp bitn-logior)
                  :use (bvecp-rin bvecp-flags))))

(local-defthmd final-31
  (implies (and (specialp) (natp k))
           (equal (bitn (logior (flags) (rin)) k)
	          (bitn (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp)) k)))
  :hints (("Goal" :use (final-28 final-29 final-30))))

(local-defthmd specialp-rewrite
  (equal (specialp)
         (or (nanp (opad) (dp))
             (infp (opad) (dp))
             (nanp (opbd) (dp))
             (infp (opbd) (dp))
             (nanp (opcd) (dp))
             (infp (opcd) (dp))
             (= (+ (a) (p)) 0)))
  :hints (("Goal" :in-theory (enable specialp snanp-nanp opa-opad opb-opbd opc-opcd))))

(local-defthm gag-qnan
  (implies (qnanp x (dp))
           (equal (gag x) x))
  :hints (("Goal" :in-theory (enable dp gag prec qnanp nanp encodingp)
                  :use ((:instance logior-2**n (n 51))))))

(local-defthmd final-32
  (implies (or (nanp (opad) (dp))
               (nanp (opbd) (dp))
               (nanp (opcd) (dp))
               (fma-undefined-p (opbd) (opcd) (opad) (dp)))
	   (equal (d)
	          (arm-fma-pre-comp-val (opad) (opbd) (opcd) (rz) (dp))))
  :hints (("Goal" :in-theory (enable final-26 final-27 specialp-rewrite d-rewrite fma-undefined-p arm-fma-pre-comp-val
                                     opa-opad opb-opbd opc-opcd snanp-nanp dnp))))

(local-defthmd final-33
  (implies (or (nanp (opad) (dp))
               (nanp (opbd) (dp))
               (nanp (opcd) (dp))
               (fma-undefined-p (opbd) (opcd) (opad) (dp)))
	   (equal (d)
	          (mv-nth 0 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))))
  :hints (("Goal" :in-theory (enable snanp-nanp final-32 arm-fma-spec-rewrite))))

(local-defthmd final-34
  (implies (or (nanp (opad) (dp))
               (nanp (opbd) (dp))
               (nanp (opcd) (dp))
               (fma-undefined-p (opbd) (opcd) (opad) (dp)))
	   (arm-fma-pre-comp-val (opad) (opbd) (opcd) (rz) (dp)))
  :hints (("Goal" :in-theory (enable final-26 final-27 specialp-rewrite d-rewrite fma-undefined-p arm-fma-pre-comp-val
                                     opa-opad opb-opbd opc-opcd snanp-nanp dnp)
		  :use (bvecp-opb bvecp-opc))))

(local-defthmd final-35
  (implies (or (nanp (opad) (dp))
               (nanp (opbd) (dp))
               (nanp (opcd) (dp))
               (fma-undefined-p (opbd) (opcd) (opad) (dp)))
	   (equal (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp))
	          (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))))
  :hints
; Matt K. mod: Formerly both arm-fma-spec-rewrite and final-34 were enabled
; below, with no :use hint.  But the change in storing rewrite rules after
; v8-0, to keep LET (LAMBDA) expressions on the right-hand side, caused this to
; fail, apparently without an easier solution than the one used below.
  (("Goal" :use final-34 :in-theory (enable arm-fma-spec-rewrite))))

(local-defthm final-36
  (implies (arm-fma-pre-comp-val (opad) (opbd) (opcd) (rz) (dp))
           (or (nanp (opad) (dp))
               (nanp (opbd) (dp))
               (nanp (opcd) (dp))
               (fma-undefined-p (opbd) (opcd) (opad) (dp))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable final-26 final-27 specialp-rewrite d-rewrite fma-undefined-p arm-fma-pre-comp-val
                                     opa-opad opb-opbd opc-opcd snanp-nanp dnp))))

(local-defthm final-37
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp)))))
	   (or (infp (opad) (dp))
	       (infp (opbd) (dp))
	       (infp (opcd) (dp))
	       (= (+ (a) (p)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable specialp-rewrite fma-undefined-p))))

(local-defthm bvecp-iencode
  (bvecp (iencode x (dp)) 64)
  :hints (("Goal" :in-theory (enable iencode dp))))

(local-defthmd final-38
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp)))))
	   (equal (d)
	          (if (infp (opad) (dp))
		      (opad)
		    (if (or (infp (opbd) (dp)) (infp (opcd) (dp)))
		        (iencode (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp))) (dp))
	              (if (and (= (a) 0) (= (p) 0) (= (sgnf (opad) (dp)) (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp)))))
		          (zencode (sgnf (opad) (dp)) (dp))
			(if (= (rmode) 2)
                            (zencode 1 (dp))
                          (zencode 0 (dp))))))))
  :hints (("Goal" :use (final-37)
                  :in-theory (enable d-rewrite fma-undefined-p opa-opad opb-opbd opc-opcd snanp-nanp dnp))))

(local-defthmd final-4-a
  (and (equal (decode (opad) (dp)) (a))
       (equal (decode (opbd) (dp)) (b))
       (equal (decode (opcd) (dp)) (c)))
  :hints (("Goal" :in-theory (enable expw sigw encodingp sigf sgnf denormp decode ddecode expf a b c opad opbd opcd
                                     specialp bvecp-opa bvecp-opb bvecp-opc zencode bitn-bits dp prec bias))))

(local-defthmd final-39
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp)))))
	   (equal (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))
	          (arm-fma-pre-comp-excp (opad) (opbd) (opcd) (rz) (dp))))
  :hints (("Goal" :use (final-36 final-37)
                  :in-theory (enable p final-4-a arm-fma-comp arm-fma-spec-rewrite))))

(local-defthm final-40
  (iff (EQUAL (FPSCR-RC (RZ)) 'RDN)
       (EQUAL (RMODE) 2))
  :hints (("Goal" :in-theory (enable rmode fpscr-rc rz))))

(local-defthmd final-41
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp)))))
	   (equal (mv-nth 0 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))
	          (if (or (infp (opbd) (dp)) (infp (opcd) (dp)))
                      (iencode (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp))) (dp))
                    (if (infp (opad) (dp))
                        (opad)
                      (zencode (if (= (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp)))
		                      (sgnf (opad) (dp)))
                                   (sgnf (opad) (dp))
                                 (if (eql (rmode) 2) 1 0))
			       (dp))))))
  :hints (("Goal" :use (final-36 final-37)
                  :in-theory (enable p final-4-a arm-fma-comp arm-fma-spec-rewrite))))

(local-defthmd final-42
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp))))
		(infp (opad) (dp))
		(or (infp (opbd) (dp)) (infp (opcd) (dp))))
	   (equal (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp)))
		  (sgnf (opad) (dp))))
  :hints (("Goal" :in-theory (enable fma-undefined-p))))

(local-defthmd final-43
  (implies (not (= (a) 0))
           (equal (sgnf (opa) (dp))
	          (if (> (a) 0) 0 1)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode a sigw expw dp fraca frac
                              bitn-bits sigf manf sgnf checkdenorm expnt expf expa a fzp sign))))

(local-defthmd final-44
  (implies (not (= (b) 0))
           (equal (sgnf (opb) (dp))
	          (if (> (b) 0) 0 1)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode b sigw expw dp
                              bitn-bits sigf manf sgnf checkdenorm expnt expf expb b fzp sign))))

(local-defthmd final-45
  (implies (not (= (c) 0))
           (equal (sgnf (opc) (dp))
	          (if (> (c) 0) 0 1)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode c sigw expw dp
                              bitn-bits sigf manf sgnf checkdenorm expnt expf c fzp sign))))

(local-defthmd final-46
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp))
	    	         (infp (opad) (dp))
		         (infp (opbd) (dp))
			 (infp (opcd) (dp))))
		(= (logxor (sgnf (opbd) (dp)) (sgnf (opcd) (dp)))
		   (sgnf (opad) (dp))))
           (and (equal (a) 0)
	        (equal (p) 0)))
  :hints (("Goal" :use (final-37 final-43 final-44 final-45) :in-theory (enable final-18 p))))

(local-defthm final-47
  (implies (infp x (dp))
           (equal (iencode (sgnf x (dp)) (dp))
	          x))
  :hints (("Goal" :in-theory (enable iencode dp sgnf infp cat encodingp expf manf unsupp)
                  :use ((:instance bitn-0-1 (n 63))
		        (:instance bitn-plus-bits (n 63) (m 0))
		        (:instance bits-plus-bits (n 62) (p 52) (m 0))))))

(local-defthmd final-48
  (implies (and (specialp)
                (not (or (nanp (opad) (dp))
                         (nanp (opbd) (dp))
                         (nanp (opcd) (dp))
                         (fma-undefined-p (opbd) (opcd) (opad) (dp)))))
	   (equal (mv-nth 0 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))
	          (d)))
  :hints (("Goal" :use (final-42 final-46)
                  :in-theory (enable final-41 final-38))))

(local-defthmd final-49
  (implies (specialp)
	   (equal (mv-nth 0 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))
	          (d)))
  :hints (("Goal" :use (final-48 final-33))))

(local-defthmd final-50
  (implies (and (specialp) (natp k))
           (equal (bitn (logior (flags) (rin)) k)
	          (bitn (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))) k)))
  :hints (("Goal" :use (final-31 final-39 final-35))))

(local-defthmd final-51
  (integerp (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))))
  :hints (("Goal" :in-theory (enable arm-post-comp arm-fma-spec) :use (bvecp-rin))))

(local-defthmd final-52
  (implies (specialp)
           (equal (logior (flags) (rin))
	          (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))))
  :hints (("Goal" :use (final-51 bvecp-flags bvecp-rin
                        (:instance final-50 (k (bit-diff (logior (flags) (rin)) (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp))))))
			(:instance bit-diff-diff (x (logior (flags) (rin))) (y (mv-nth 1 (arm-fma-spec (opa) (opb) (opc) (rin) (dp)))))))))

(local-defthm special-case
  (implies (specialp)
           (mv-let (d-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :rule-classes ()
  :hints (("Goal" :use (final-52 final-49))))


;;*******************************************************************************
;; Final Result
;;*******************************************************************************

(local-defthm fma-main
  (mv-let (d-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
    (and (equal (d) d-spec)
         (equal (logior (rin) (flags)) r-spec)))
  :rule-classes ()
  :hints (("Goal" :use (comp-case special-case))))

(local-defthm lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25)) (fzp (bitn (rin) 24)) (rmode (bits (rin) 23 22)))
    (mv-let (opd mulexcps piz inz expovfl) (fmul64 (opb) (opc) (scale) fzp dnp rmode 1 0)
	 (mv-let (d flags) (fadd64 (opa) opd fzp dnp rmode 1 inz piz expovfl mulexcps)
	   (mv-let (d-spec r-spec) (arm-fma-spec (opa) (opb) (opc) (rin) (dp))
          (and (equal d d-spec)
               (equal (logior (rin) flags) r-spec))))))
  :rule-classes ()
  :hints (("Goal" :use (fma-main)
                  :in-theory (e/d (fzp dnp rmode opd inz piz expovfl mulexcps equivalence-lemma) (arm-fma-spec)))))

(local (defmacro ic ()
  '(fma-constraints opa opb opc scale rin fma fscale)))

(local-defthm fadd64-fma-1
  (implies (fma-constraints opa opb opc scale rin fma fscale)
           (let ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22)))
             (mv-let (opd mulexcps piz inz expovfl) (fmul64 opb opc scale fz dn rmode 1 0)
	       (mv-let (d flags) (fadd64 opa opd fz dn rmode 1 inz piz expovfl mulexcps)
	         (mv-let (d-spec r-spec) (arm-fma-spec opa opb opc rin (dp))
                   (and (equal d d-spec)
                        (equal (logior rin flags) r-spec)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (opb (lambda () (if (ic) opb (opb))))
                         (opc (lambda () (if (ic) opc (opc))))
                         (scale (lambda () (if (ic) scale (scale))))
                         (rin (lambda () (if (ic) rin (rin))))
                         (fscale (lambda () (if (ic) fscale (fscale))))
                         (fma (lambda () (if (ic) fma (fma)))))))
           ("Subgoal 1" :use (fma-constraints-lemma))))

(defthm fadd64-fma
  (implies (and (bvecp opa 64)
                (bvecp opb 64)
                (bvecp opc 64)
                (bvecp scale 64)
                (bvecp rin 32)
                (equal (bits rin 12 8) 0)
                (equal (bitn rin 15) 0))
           (let ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22)))
             (mv-let (opd mulexcps piz inz expovfl) (fmul64 opb opc scale fz dn rmode 1 0)
	       (mv-let (d flags) (fadd64 opa opd fz dn rmode 1 inz piz expovfl mulexcps)
	         (mv-let (d-spec r-spec) (arm-fma-spec opa opb opc rin (dp))
                   (and (equal d d-spec)
                        (equal (logior rin flags) r-spec)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fadd64-fma-1 (fma 1) (fscale 0))) :in-theory (enable fma-constraints))))
