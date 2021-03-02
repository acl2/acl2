(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

(include-book "../fmul/fmul64")

(encapsulate ()
  
(local (include-book "../fmul/summary"))

;; We impose the following constraints on the arguments of fmul64:

(defund input-constraints (opa opb rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (bvecp rin 32)
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


;; Note that in the case of a subnormal product, the specification does not compute 
;; a specific value, but rather constrains it:

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

;; The main theorem:

(defthm fmul64-fused-correct
  (implies (input-constraints opa opb rin)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb fzp dnp rmode 1)
               (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
  :rule-classes ())

)

(include-book "fadd64")

(defund absval (e s)
  (if (> e 0)
      (* (expt 2 (- (- e (1- (expt 2 10))) 106)) s)
    (* (expt 2 (- (- 1 (1- (expt 2 10))) 106)) s)))

(defund val (b e s)
  (if (= b 0)
      (absval e s)
    (- (absval e s))))

;; The following constraints on the inputs of fadd64 represent the computational case:

(defund comp-constraints (opa opb rin fma inz piz expovfl mulexcps b)
  (let* ((mulovfl (if (and (= fma 1) (= inz 0)) expovfl 0))
         (mulstk (if (= fma 1) (bitn mulexcps 4) 0))
         (fz (bitn rin (fz)))
         (expa (expf opa (dp)))
         (a (if (and (= fz 1) (= expa 0)) 0 (decode opa (dp))))
         (signb (bitn opb 116))
         (expb (bits opb 115 105))
         (fracb (if (and (= fma 0) (= fz 1) (= expb 0)) 0 (bits opb 104 0)))
         (sigb (if (= expb 0) (* 2 fracb) (+ (expt 2 106) (* 2 fracb)))))
    (and (bvecp opa 64)
         (bvecp opb 117)
         (bvecp rin 32)
         (bvecp fma 1)
         (bvecp inz 1)
         (bvecp piz 1)
         (bvecp expovfl 1)
         (bvecp mulexcps 8)
         (rationalp b)
         (= (bits rin 12 10) 0)
         (< expa (1- (expt 2 11)))
	 (implies (= fma 0) (and (< expb (1- (expt 2 11))) (= (bits opb 52 0) 0)))
         (not (= (+ a b) 0))
         (implies (= fma 1) (and (= piz 0) (= (bitn mulexcps 3) 0) (= (bitn mulexcps 2) 0)))
         (implies (= fma 1) (= inz (if (= b 0) 1 0)))
         (implies (not (= b 0)) (= signb (if (< b 0) 1 0)))
         (cond ((= mulovfl 1)
	        (and (>= (abs b) (expt 2 (1+ (expt 2 10))))
	             (= mulstk 0)))
               ((> expb 0)
                (and (= mulstk 0)
                     (= b (val signb expb sigb))))
               (t
                (and (<= (absval expb (chop sigb -53)) (abs b))
                     (< (abs b) (absval expb (+ (chop sigb -53) (expt 2 53))))
                     (iff (= (absval expb (chop sigb -53)) (abs b))
                          (and (= (bits sigb 52 0) 0)
                               (= mulstk 0)))))))))          

;; We shall prove the following:

;; (defthm fadd64-comp
;;   (implies (comp-constraints opa opb rin fma inz piz expovfl mulexcps b)
;;            (let* ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22))
;;                   (a (if (and (= fz 1) (= (expf opa (dp)) 0)) 0 (decode opa (dp)))))
;;              (mv-let (d flags) (fadd64 opa opb fz dn rmode fma inz piz expovfl mulexcps)
;;                (mv-let (d-spec r-spec) (arm-post-comp (+ a b) rin (dp))
;;                  (and (equal d d-spec)
;;                       (equal (logior (bitn flags (ixc)) (bitn rin (ixc))) (bitn r-spec (ixc)))
;;                       (equal (logior (bitn flags (ufc)) (bitn rin (ufc))) (bitn r-spec (ufc)))
;;                       (equal (logior (bitn flags (ofc)) (bitn rin (ofc))) (bitn r-spec (ofc)))))))))

;; In order to address the lack of modularity of the ACL2 function fadd64, we
;; take the following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate (((opa) => *) ((opb) => *) ((rin) => *) ((fma) => *)
              ((inz) => *) ((piz) => *) ((expovfl) => *) ((mulexcps) => *)
              ((b) => *))
  (local (defun opa () 1))
  (local (defun opb () 0))
  (local (defun rin () 0))
  (local (defun fma () 1))
  (local (defun inz () 1))
  (local (defun piz () 0))
  (local (defun expovfl () 0))
  (local (defun mulexcps () 0))
  (local (defun b () 0))
  (defthm comp-constraints-lemma
    (comp-constraints (opa) (opb) (rin) (fma) (inz) (piz) (expovfl) (mulexcps) (b))
    :rule-classes ()))

;; In terms of these constants, we shall define constants corresponding to the local 
;; variables of fadd64, culminating in the constants (d) and (flags), corresponding to
;; the outputs.

;; The constant definitions will be derived from that of fadd64 in such a way that 
;; the proof of the following will be trivial:

;; (defthm equivalence-lemma
;;   (mv-let (d flags)
;;           (fadd64 (opa) (opb) (bitn (rin) 24) (bitn (rin) 25) (bits (rin) 23 22)
;;                   (fma) (inz) (piz) (expovfl) (mulexcps))
;;     (and (equal (d) d)
;;          (equal (flags) flags))))

;; The real work will be the proof of the following theorem:

;; (defthm fadd64-main
;;   (let ((a (if (and (= (bitn (rin) 24) 1) (= (expf (opa) (dp)) 0))
;;                0
;;              (decode (opa) (dp)))))
;;     (mv-let (d-spec r-spec) (arm-post-comp (+ a (b)) (rin) (dp))
;;       (and (equal (d) d-spec)
;;            (equal (logior (bitn (flags) (ixc)) (bitn (rin) (ixc))) (bitn r-spec (ixc)))
;;            (equal (logior (bitn (flags) (ufc)) (bitn (rin) (ufc))) (bitn r-spec (ufc)))
;;            (equal (logior (bitn (flags) (ofc)) (bitn (rin) (ofc))) (bitn r-spec (ofc)))))))

;; The following is an immediate consequence of the two preceding results:

;; (defthmd lemma-to-be-functionally-instantiated
;;   (let* ((fz (bitn (rin) 24)) (dn (bitn (rin) 25)) (rmode (bits (rin) 23 22))
;;          (a (if (and (= fz 1) (= (expf (opa) (dp)) 0)) 0 (decode (opa) (dp)))))
;;     (mv-let (d flags) (fadd64 (opa) (opb) fz dn rmode (fma) (inz) (piz) (expovfl) (mulexcps))
;;       (mv-let (d-spec r-spec) (arm-post-comp (+ a (b)) (rin) (dp))
;;         (and (equal d d-spec)
;;              (equal (logior (bitn flags (ixc)) (bitn (rin) (ixc))) (bitn r-spec (ixc)))
;;              (equal (logior (bitn flags (ufc)) (bitn (rin) (ufc))) (bitn r-spec (ufc)))
;;              (equal (logior (bitn flags (ofc)) (bitn (rin) (ofc))) (bitn r-spec (ofc)))))))
 
;; The desired theorem can then be derived by functional instantiation.

;;*******************************************************************************
;; Formulation and proof of equivalence-lemma
;;*******************************************************************************

(defund fzp () (bitn (rin) 24))
(defund dnp () (bitn (rin) 25))
(defund rmode () (bits (rin) 23 22))

(defund opblong () (logand1 (fma) (lognot1 (inz))))

(defund mulovfl () (logand1 (opblong) (expovfl)))

(defund piz-1 () (logand1 (fma) (piz)))

(defund mulstk () (logand1 (bitn (mulexcps) (ixc)) (opblong)))

(defund flags-1 ()
  (if1 (fma)
       (let ((flags (mulexcps)))
         (setbitn flags 8 (ixc)
                  (logand1 (bitn flags (ixc))
                           (lognot1 (opblong)))))
     (bits 0 7 0)))

(defund opax () (setbits (bits 0 116 0) 117 116 53 (opa)))

(defund opaz ()
  (mv-let (opaz r) (checkdenorm (opax) (flags-1) (fzp))
    (declare (ignore r))
    opaz))

(defund flags-2 ()
  (mv-let (opaz r) (checkdenorm (opax) (flags-1) (fzp))
    (declare (ignore opaz))
    r))

(defund opbz ()
  (if1 (lognot1 (fma))
       (mv-let (opbz flags) (checkdenorm (opb) (flags-2) (fzp))
         (declare (ignore flags))
         opbz)
       (opb)))

(defund flags-3 ()
  (if1 (lognot1 (fma))
       (mv-let (opb flags) (checkdenorm (opb) (flags-2) (fzp))
         (declare (ignore opb))
         flags)
       (flags-2)))

(defund isspecial ()
  (mv-let (isspecial d flags) (checkspecial (opaz) (opbz) (fzp) (dnp) (rmode) (opblong) (mulovfl) (piz-1) (mulstk) (flags-3))
    (declare (ignore d flags))
    isspecial))

(defund d-1 ()
  (mv-let (isspecial d flags) (checkspecial (opaz) (opbz) (fzp) (dnp) (rmode) (opblong) (mulovfl) (piz-1) (mulstk) (flags-3))
    (declare (ignore isspecial flags))
    d))

(defund flags-4 ()
  (mv-let (isspecial d flags) (checkspecial (opaz) (opbz) (fzp) (dnp) (rmode) (opblong) (mulovfl) (piz-1) (mulstk) (flags-3))
    (declare (ignore isspecial d))
    flags))

(defund usa () (log<> (sign (opaz)) (sign (opbz))))

(defund far () (isfar (expnt (opaz)) (expnt (opbz)) (usa)))

(defund sum ()
  (mv-let (sum stk signl) (add (opaz) (opbz) (far) (usa) (mulstk))
    (declare (ignore stk signl))
    sum))

(defund stk ()
  (mv-let (sum stk signl) (add (opaz) (opbz) (far) (usa) (mulstk))
    (declare (ignore sum signl))
    stk))

(defund signl ()
  (mv-let (sum stk signl) (add (opaz) (opbz) (far) (usa) (mulstk))
    (declare (ignore sum stk))
     signl))

(defund lshift ()
  (mv-let (lshift expshft) (computelshift (opaz) (opbz) (far) (usa))
    (declare (ignore expshft))
    lshift))

(defund expshft ()
  (mv-let (lshift expshft) (computelshift (opaz) (opbz) (far) (usa))
    (declare (ignore lshift))
    expshft))

(defund sumshft () (bits (ash (sum) (lshift)) 107 0))

(defund signout () (if1 (mulovfl) (sign (opb)) (signl)))

(defund rnddir () (computernddir (rmode) (signout)))

(defund incovfl ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incnorm inxovfl inxnorm))
    incovfl))

(defund incnorm ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incovfl inxovfl inxnorm))
    incnorm))

(defund inxovfl ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incovfl incnorm inxnorm))
    inxovfl))

(defund inxnorm ()
  (mv-let (incovfl incnorm inxovfl inxnorm) (rndinfo (sum) (stk) (lshift) (rnddir))
    (declare (ignore incovfl incnorm inxovfl))
    inxnorm))

(defund sumunrnd () (bits (sumshft) 107 54))

(defund sumnorm () (bits (+ (sumunrnd) (incnorm)) 53 0))

(defund sumovfl () (bits (+ (bits (sumunrnd) 53 1) (incovfl)) 53 0))

(defund tiny () (logand1 (lognot1 (bitn (sumunrnd) 53)) (lognot1 (bitn (sumunrnd) 52))))

(defund ovfl2 () (logand1 (log= (bits (sumunrnd) 53 1) (- (ash 1 53) 1)) (incovfl)))

(defund ovfl () (bitn (sumnorm) 53))

(defund informax ()
  (logior1 (logior1 (logior1 (logand1 (log= (expshft) 2046)
                                      (logior1 (ovfl) (ovfl2)))
                             (logand1 (log= (expshft) 2045) (ovfl2)))
                    (logand1 (log= (expshft) 2047) (opblong)))
           (mulovfl)))

(defund expout ()
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

(defund fracout ()
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

(defund flags-5 ()
  (if1 (informax)
       (setbitn (setbitn (flags-4) 8 (ofc) 1) 8 (ixc) 1)
       (if1 (tiny)
            (if1 (fzp)
                 (setbitn (flags-4) 8 (ufc) 1)
                 (if1 (bitn (sumnorm) 52)
                      (setbitn (setbitn (flags-4) 8 (ufc) 1) 8 (ixc) 1)
                      (if1 (inxnorm)
                           (setbitn (setbitn (flags-4) 8 (ufc) 1) 8 (ixc) 1)
                           (flags-4))))
            (if1 (ovfl2)
                 (setbitn (flags-4) 8 (ixc) (logior1 (bitn (flags-4) (ixc)) (inxovfl)))
                 (if1 (ovfl)
                      (setbitn (flags-4) 8 (ixc) (logior1 (bitn (flags-4) (ixc)) (inxovfl)))
                      (setbitn (flags-4) 8 (ixc) (logior1 (bitn (flags-4) (ixc)) (inxnorm))))))))

(defund d ()
  (if1 (isspecial)
       (d-1)
       (setbits (setbits (setbitn (d-1) 64 63 (signout)) 64 62 52 (expout)) 64 51 0
                (fracout))))

(defun flags ()
  (if1 (isspecial)
       (flags-4)
       (flags-5)))

(defthmd equivalence-lemma
  (mv-let (d flags)
          (fadd64 (opa) (opb) (bitn (rin) 24) (bitn (rin) 25) (bits (rin) 23 22)
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

(in-theory (disable (comp-constraints) (opblong) (mulovfl) (piz-1) (fzp) (dnp) (rmode)
                    (mulstk) (flags-1) (opax) (opaz) (flags-2) (opbz) (flags-3) (isspecial) (d-1) (flags-4) (usa) 
                    (far) (sum) (stk) (signl) (signout) (lshift) (expshft) (sumshft) (rnddir) (incovfl) (incnorm)
                    (inxovfl) (inxnorm) (sumunrnd) (sumnorm) (sumovfl) (tiny) (ovfl2) (ovfl)
                    (informax) (expout) (fracout) (flags-5) (d) (flags)))

;; let's also disable all the functions defined by the model and enable them only as needed:

(in-theory (disable (computernddir) (gag) (sign) (expnt) (frac) (checkdenorm) (checkspecial)
                    (isfar) (add) (clz128) (lza128) (computelza) (computelshift) (rndinfo) (fadd64)
                    computernddir gag sign expnt frac checkdenorm checkspecial isfar
                    add clz128 lza128 computelza computelshift rndinfo fadd64))

;;*******************************************************************************
;; Operand components
;;*******************************************************************************

;; The following constants are shared by the auxiliary functions:

(defund signa () (sign (opaz)))

(defund signb () (sign (opbz)))

(defund expa () (expnt (opaz)))

(defund expb () (expnt (opbz)))

(defund fraca () (frac (opaz)))

(defund fracb () (frac (opbz)))

(defund siga () (setbits (setbitn (bits 0 107 0) 108 106 (log<> (expa) 0)) 108 105 1 (fraca)))

(defund sigb () (setbits (setbitn (bits 0 107 0) 108 106 (log<> (expb) 0)) 108 105 1 (fracb)))

(in-theory (disable (signa) (signb) (expa) (expb) (fraca) (fracb) (siga) (sigb)))

(defthm signa-0-1
  (member (signa) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signa))))

(defthmd bvecp-expa
  (bvecp (expa) 11)
  :hints (("Goal" :in-theory (enable cat-0 expa expnt))))

(defthm natp-expa
  (natp (expa))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-expa)))

(defthmd bvecp-fraca
  (bvecp (fraca) 105)
  :hints (("Goal" :in-theory (enable fraca frac opax opaz checkdenorm))))

(defthm natp-fraca
  (natp (fraca))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-fraca)))

(defthmd fraca-low
  (equal (bits (fraca) 52 0) 0)
  :hints (("Goal" :in-theory (enable fraca frac opax opaz checkdenorm))))

(defthm signb-0-1
  (member (signb) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signb))))

(defthmd bvecp-expb
  (bvecp (expb) 11)
  :hints (("Goal" :in-theory (enable expb expnt))))

(defthm natp-expb
  (natp (expb))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-expb)))

(defthmd bvecp-fracb
  (bvecp (fracb) 105)
  :hints (("Goal" :in-theory (enable fracb frac opbz checkdenorm))))

(defthm natp-fracb
  (natp (fracb))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-fracb)))

(defthmd bvecp-siga
  (bvecp (siga) 107)
  :hints (("Goal" :in-theory (enable bvecp cat siga)
                  :use (bvecp-fraca))))

(defthmd bvecp-siga-0
  (iff (= (expa) 0)
       (bvecp (siga) 106))
  :hints (("Goal" :in-theory (enable bvecp cat siga)
                  :use (bvecp-fraca))))

(defthm natp-siga
  (natp (siga))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-siga)))

(defthmd bvecp-sigb
  (bvecp (sigb) 107)
  :hints (("Goal" :in-theory (enable bvecp cat sigb)
                  :use (bvecp-fracb))))

(defthmd bvecp-sigb-0
  (iff (= (expb) 0)
       (bvecp (sigb) 106))
  :hints (("Goal" :in-theory (enable bvecp cat sigb)
                  :use (bvecp-fracb))))

(defthm natp-sigb
  (natp (sigb))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use bvecp-sigb)))

;;*******************************************************************************
;; checkSpecial
;;*******************************************************************************

(defund opazero () (logand1 (log= (expa) 0) (log= (fraca) 0)))

(defund opainf () (logand1 (log= (expa) 2047) (log= (fraca) 0)))

(defund opanan () (logand1 (log= (expa) 2047) (log<> (fraca) 0)))

(defund opaqnan () (logand1 (opanan) (bitn (fraca) 104)))
  
(defund opasnan () (logand1 (opanan) (lognot1 (bitn (fraca) 104))))
    
(defund opbzero () (logand1 (logand1 (logand1 (log= (expb) 0) (log= (fracb) 0)) (lognot1 (mulovfl))) (lognot1 (mulstk))))
   
(defund opbinf () (logand1 (logand1 (log= (expb) 2047) (log= (fracb) 0)) (lognot1 (opblong))))

(defund opbnan () (logand1 (logand1 (log= (expb) 2047) (log<> (fracb) 0)) (lognot1 (opblong))))

(defund opbqnan () (logand1 (opbnan) (bitn (fracb) 104)))

(defund opbsnan () (logand1 (opbnan) (lognot1 (bitn (fracb) 104))))

(defund isspecial* ()
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

(defund flags-4* ()
  (if1 (opasnan)
       (setbitn (flags-3) 8 (ioc) 1)
       (if1 (piz-1)
            (flags-3)
            (if1 (opbsnan)
                 (setbitn (flags-3) 8 (ioc) 1)
                 (if1 (opaqnan)
                      (flags-3)
                      (if1 (opbqnan)
                           (flags-3)
                           (if1 (opainf)
                                (if1 (logand1 (opbinf) (log<> (signa) (signb)))
                                     (setbitn (flags-3) 8 (ioc) 1)
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

(in-theory (disable (opazero) (opainf) (opanan) (opasnan) (opaqnan) (opbzero) (opbinf) (opbnan)
                    (opbsnan) (opbqnan) (isspecial*) (flags-4*)))

(defthmd checkspecial-lemma
  (and (equal (isspecial) (isspecial*))
       (equal (flags-4) (flags-4*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(opazero opainf opanan opasnan opaqnan opbzero opbinf opbnan
                        opbsnan opbqnan isspecial* flags-4* isspecial flags-4 checkspecial expa expb
                        fraca fracb signa signb))))

;;*******************************************************************************
;; isFar
;;*******************************************************************************

(defund expap1 () (bits (+ (expa) 1) 11 0))

(defund expbp1 () (bits (+ (expb) 1) 11 0))

(defund isnear ()
  (logand1 (usa)
           (logior1 (logior1 (log= (expa) (expb))
                             (log= (expa) (expbp1)))
                    (log= (expb) (expap1)))))

(in-theory (disable (expap1) (expbp1) (isnear)))

(defthmd isfar-lemma
  (equal (far) (lognot1 (isnear)))
  :hints (("Goal" :in-theory '(isnear isfar expap1 expbp1 expa expb far))))

;;*******************************************************************************
;; add
;;*******************************************************************************

(defund opbgeopa ()
  (logior1 (log> (expb) (expa))
           (logand1 (log= (expb) (expa))
                    (log>= (fracb) (fraca)))))

(defund sigaprime ()
  (if1 (logand1 (far) (usa))
       (bits (ash (siga) 1) 107 0)
       (siga)))

(defund sigbprime ()
  (if1 (logand1 (far) (usa))
       (bits (ash (sigb) 1) 107 0)
       (sigb)))

(defund signl* ()
  (if1 (opbgeopa)
       (signb)
       (signa)))

(defund sigl ()
  (if1 (opbgeopa)
       (sigbprime)
       (sigaprime)))

(defund sigs ()
  (if1 (opbgeopa)
       (sigaprime)
       (sigbprime)))

(defund expdiff ()
  (if1 (opbgeopa)
       (if1 (logand1 (log= (expa) 0) (log<> (expb) 0))
            (bits (- (- (expb) (expa)) 1) 11 0)
            (bits (- (expb) (expa)) 11 0))
       (if1 (logand1 (log= (expb) 0) (log<> (expa) 0))
            (bits (- (- (expa) (expb)) 1) 11 0)
            (bits (- (expa) (expb)) 11 0))))

(defund rshift ()
  (if1 (log<> (bits (expdiff) 11 7) 0)
       (bits (logior (bits (expdiff) 6 0) 112) 6 0)
       (bits (expdiff) 6 0)))

(defund sigshft () (bits (ash (sigs) (- (rshift))) 107 0))

(defund shiftout () (log<> (ash (sigshft) (rshift)) (sigs)))

(defund sum* ()
  (bits (+ (+ (sigl) (bits (if1 (usa) (lognot (sigshft)) (sigshft)) 107 0))
           (logand1 (usa)
                    (lognot1 (logior1 (logand1 (mulstk) (lognot1 (opbgeopa)))
                                      (logand1 (far) (shiftout))))))
        107 0))

(defund stk* () (logior1 (mulstk) (logand1 (far) (shiftout))))

(in-theory (disable  (opbgeopa) (sigaprime) (sigbprime) (signl*) (sigl) (sigs)
                     (expdiff) (rshift) (sigshft) (shiftout) (sum*) (stk*)))

(defthmd add-lemma
  (and (equal (sum) (sum*))
       (equal (stk) (stk*))
       (equal (signl) (signl*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(signa signb expa expb fraca fracb opbgeopa siga sigb sigaprime
                        sigbprime signl* sigl sigs expdiff rshift sigshft shiftout sum* 
                        stk* signl sum stk add))))

;;*******************************************************************************
;; computeLshift
;;*******************************************************************************

(defund expl () (bits (if1 (log>= (expa) (expb)) (expa) (expb)) 11 0))

(defund lza () (computelza (opaz) (opbz)))

(defund lshift* ()
  (if1 (far)
       (bits 0 6 0)
       (if1 (log< (lza) (expl))
            (lza)
	    (bits (if1 (log= (expl) 0) 0 (- (expl) 1)) 6 0))))

(defund expshft* ()
  (if1 (far)
       (bits (if1 (usa) (- (expl) 1) (expl)) 11 0)
       (if1 (log< (lza) (expl))
            (bits (- (expl) (lza)) 11 0)
            (bits 0 11 0))))

(in-theory (disable (expl) (lza) (lshift*) (expshft*)))
	    
(defthmd computelshift-lemma
  (and (equal (lshift) (lshift*))
       (equal (expshft) (expshft*)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(computelshift lshift lshift* expshft expshft* expl lza expb expa))))

;;*******************************************************************************
;; computeLZA
;;*******************************************************************************

(defund fracl () (if1 (opbgeopa) (fracb) (fraca))) 

(defund fracs () (if1 (opbgeopa) (fraca) (fracb))) 

(defund in1lza ()
  (setbits (setbitn (bits 0 127 0) 128 127 1) 128 126 22 (fracl)))

(defund in2lza ()
  (if1 (log= (bitn (expb) 0) (bitn (expa) 0))
       (setbits (bits (- (ash 1 22) 1) 127 0) 128 126 22 (lognot (fracs)))
       (setbitn (setbits (bits (- (ash 1 21) 1) 127 0) 128 125 21 (lognot (fracs)))
                128 127 1)))

(defund lza* () (lza128 (in1lza) (in2lza)))

(in-theory (disable (fracl) (fracs) (in1lza) (in2lza) (lza*)))

(defthmd computelza-lemma
  (equal (lza) (lza*))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(computelza expa expb opbgeopa lza lza* fracl fracs fraca
                                   fracb in1lza in2lza))))

           
;;*******************************************************************************
;; LZA128
;;*******************************************************************************

(defund p1 () (logxor (in1lza) (in2lza)))

(defund k1 ()
  (logand (bits (lognot (in1lza)) 127 0)
          (bits (lognot (in2lza)) 127 0)))

(defund w3 () (bits (lognot (logxor (p1) (ash (k1) 1))) 127 0))

(defthmd lza128-lemma
  (equal (lza*) (clz128 (bits (ash (w3) (- 1)) 127 0)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(lza128 lza* p1 k1 w3))))

(in-theory (disable (p1) (k1) (w3)))


;;*******************************************************************************
;; rndInfo
;;*******************************************************************************

(defund lovflmask () (bits (ash 36028797018963968 (- (lshift))) 55 0))

(defund govflmask () (bits (ash (lovflmask) (- 1)) 54 0))

(defund sovflmask () (bits (ash 18014398509481983 (- (lshift))) 53 0))

(defund lnormmask () (bits (ash (lovflmask) (- 1)) 54 0))

(defund gnormmask () (bits (ash (lovflmask) (- 2)) 53 0))

(defund snormmask () (bits (ash (sovflmask) (- 1)) 52 0))

(defund lovfl () (log<> (logand (sum) (lovflmask)) 0))

(defund govfl () (log<> (logand (sum) (govflmask)) 0))

(defund sovfl () (logior1 (log<> (logand (sum) (sovflmask)) 0) (stk)))

(defund lnorm () (log<> (logand (sum) (lnormmask)) 0))

(defund gnorm () (log<> (logand (sum) (gnormmask)) 0))

(defund snorm () (logior1 (log<> (logand (sum) (snormmask)) 0) (stk)))

(defund incovfl* ()
  (logior1 (logand1 (logand1 (log= (rnddir) 0) (govfl))
                    (logior1 (lovfl) (sovfl)))
           (logand1 (log= (rnddir) 2)
                    (logior1 (govfl) (sovfl)))))

(defund incnorm* ()
  (logior1 (logand1 (logand1 (log= (rnddir) 0) (gnorm))
                    (logior1 (lnorm) (snorm)))
           (logand1 (log= (rnddir) 2)
                    (logior1 (gnorm) (snorm)))))

(defund inxovfl* () (logior1 (govfl) (sovfl)))
       
(defund inxnorm* () (logior1 (gnorm) (snorm)))

(in-theory (disable (lovflmask) (govflmask) (sovflmask) (lnormmask) (gnormmask) (snormmask)
                    (lovfl) (govfl) (sovfl) (lnorm) (gnorm) (snorm) (incovfl*) (incnorm*)
                    (inxovfl*) (inxnorm*)))

(defthmd rndinfo-lemma
  (and (equal (incovfl) (incovfl*))
       (equal (inxovfl) (inxovfl*))
       (equal (incnorm) (incnorm*))
       (equal (inxnorm) (inxnorm*)))
  :hints (("goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(lovflmask govflmask sovflmask lnormmask gnormmask snormmask
                        lovfl govfl sovfl lnorm gnorm snorm incovfl* incnorm*
                        inxovfl* inxnorm* incovfl incnorm inxovfl inxnorm rndinfo))))

;;*******************************************************************************
;; Reformulation of input constraints
;;*******************************************************************************

(defthmd usa-rewrite
  (equal (usa) (if (= (signa) (signb)) 0 1))
  :hints (("Goal" :in-theory (enable usa sign signa signb opaz opax opbz))))

(defthm bvecp-opa
  (bvecp (opa) 64)
  :hints (("Goal" :use (comp-constraints-lemma) :in-theory (enable comp-constraints)))
  :rule-classes ())

(defthm integerp-opa
  (integerp (opa))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (bvecp-opa))))

(defthmd signa-rewrite
  (equal (signa) (bitn (opa) 63))
  :hints (("Goal" :in-theory (enable bitn-bits signa sign opaz opax checkdenorm))))

(defthmd expa-rewrite
  (equal (expa) (bits (opa) 62 52))
  :hints (("Goal" :in-theory (enable cat-0 bitn-bits expa expnt opaz opax
                                     checkdenorm))))

(defthm natp-rin
  (natp (rin))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (comp-constraints-lemma)
                  :in-theory (enable comp-constraints))))

(defthmd bvecp-rin
  (bvecp (rin) 32)
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (comp-constraints-lemma)
                  :in-theory (enable comp-constraints))))

(defthmd fzp-0-1
  (member (fzp) '(0 1))
  :hints (("Goal" :in-theory (enable fzp))))

(defthmd dnp-0-1
  (member (dnp) '(0 1))
  :hints (("Goal" :in-theory (enable dnp))))

(defthmd rmode-vales
  (member (rmode) '(0 1 2 3))
  :hints (("Goal" :in-theory (enable rmode)
                  :use ((:instance bvecp-member (x (rmode)) (n 2))))))

(defthmd fraca-rewrite
  (equal (fraca)
         (if (and (= (fzp) 1) (denormp (opa) (dp)))
             0
           (cat (bits (opa) 51 0) 52 0 53)))
  :hints (("Goal" :use (bvecp-opa fzp-0-1
                        (:instance bits-shift-up-2 (x (opa)) (k 53) (i 51))
                        (:instance bits-shift-up-1 (x (opa)) (k 53) (i 115) (j 105))
                        (:instance bits-shift-up-1 (x (bits (* 9007199254740992 (opa)) 116 105)) (k 105) (i 104) (j 0)))
                  :in-theory (enable bvecp opax cat fraca frac denormp dp opaz encodingp expnt expf sigf checkdenorm))))

(defthm bvecp-opb
  (bvecp (opb) 117)
  :hints (("Goal" :use (comp-constraints-lemma) :in-theory (enable comp-constraints)))
  :rule-classes ())

(defthm integerp-opb
  (integerp (opb))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (bvecp-opb))))

(defthmd signb-rewrite
  (equal (signb) (bitn (opb) 116))
  :hints (("Goal" :in-theory (enable bitn-bits signb sign opbz checkdenorm))))

(defthmd expb-rewrite
  (equal (expb) (bits (opb) 115 105))
  :hints (("Goal" :in-theory (enable cat-0 bitn-bits expb expnt opbz checkdenorm))))

(defthmd fracb-fma-rewrite
  (implies (= (fma) 1)
           (equal (fracb) (bits (opb) 104 0)))
  :hints (("Goal" :in-theory (enable cat-0 frac opbz bitn-bits fracb))))

(local-defthmd expb-pos-b-1
  (implies (and (equal (fma) 1) (equal (mulovfl) 0) (> (expb) 0))
           (equal (b) (val (signb) (expb) (sigb))))
  :hints (("Goal" :in-theory (enable bvecp frac cat opblong fracb opbz sign expnt signb sigb mulovfl expb comp-constraints)
                  :use (comp-constraints-lemma (:instance bits-bounds (x (opb)) (i 104) (j 0))))))

(local-defthm expb-pos-opbz
  (implies (> (expb) 0)
           (equal (opbz) (opb)))
  :hints (("Goal" :in-theory (enable opbz checkdenorm expnt expb))))

(local-defthmd expb-pos-b-0
  (implies (and (equal (fma) 0) (equal (mulovfl) 0) (> (expb) 0))
           (equal (b) (val (signb) (expb) (sigb))))
  :hints (("Goal" :in-theory (enable bvecp frac cat opblong fracb sign expnt signb sigb mulovfl expf dp expb-rewrite comp-constraints)
                  :use (comp-constraints-lemma (:instance bits-bounds (x (opb)) (i 104) (j 0))))))

(defthmd expb-pos-b
  (implies (and (equal (mulovfl) 0) (> (expb) 0))
           (equal (b) (val (signb) (expb) (sigb))))
  :hints (("Goal" :in-theory (enable comp-constraints)
                  :use (expb-pos-b-0 expb-pos-b-1 comp-constraints-lemma))))

(defthmd b-0
  (implies (= (fma) 1)
           (iff (equal (b) 0)
                (and (= (expb) 0)
                     (= (fracb) 0)
	             (= (mulstk) 0)
	             (= (mulovfl) 0))))
  :hints (("Goal" :use (comp-constraints-lemma
                        (:instance bits-plus-bits (x (opb)) (n 104) (p 52) (m 0))
                        (:instance bits-shift-up-2 (x (opb)) (k 1) (i 51)))
		  :expand ((BITS (OPB) 104 52))
                  :in-theory (enable comp-constraints bits-mod expb opbz chop expnt mulstk mulovfl opblong fracb frac val absval))))

(local-defthmd expb-0-b-1
  (implies (and (equal (fma) 1) (equal (mulovfl) 0) (= (expb) 0))
           (and (iff (= (absval (expb) (chop (sigb) -53)) (abs (b)))
	             (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
		(implies (not (= (b) 0)) (iff (= (signb) 0) (>= (b) 0)))
		(<= (absval (expb) (chop (sigb) -53)) (abs (b)))
                (< (abs (b)) (absval (expb) (+ (chop (sigb) -53) (expt 2 53))))))
  :hints (("Goal" :in-theory (enable opblong mulstk bvecp frac cat fracb opbz sign expnt signb sigb mulovfl expb comp-constraints)
                  :use (comp-constraints-lemma b-0 (:instance bits-bounds (x (opb)) (i 104) (j 0))))))

(local-defthm expb-0-opbz
  (implies (not (= (bitn (rin) 24) 1))
           (equal (opbz) (opb)))
  :hints (("Goal" :in-theory (enable fzp opbz checkdenorm expnt expb))))

(local-defthm expb-0-opbz-fma
  (implies (= (fma) 1)
           (equal (opbz) (opb)))
  :hints (("Goal" :in-theory (enable fzp opbz checkdenorm expnt expb))))

(local-defthm expb-0-opbz-2
  (implies (and (= (expb) 0) (= (fma) 0) (= (bitn (rin) 24) 1))
           (equal (bits (opbz) 104 0) 0))
  :hints (("Goal" :in-theory (enable frac expb-rewrite fzp opbz checkdenorm expnt expb))))

(local-defthmd expb-0-b-0
  (implies (and (equal (fma) 0) (equal (mulovfl) 0) (= (expb) 0))
           (and (iff (= (absval (expb) (chop (sigb) -53)) (abs (b)))
	             (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
		(implies (not (= (b) 0)) (iff (= (signb) 0) (>= (b) 0)))
		(<= (absval (expb) (chop (sigb) -53)) (abs (b)))
                (< (abs (b)) (absval (expb) (+ (chop (sigb) -53) (expt 2 53))))))
  :hints (("Goal" :in-theory (enable bvecp frac cat mulstk opblong fracb sign expnt signb-rewrite sigb mulovfl expf dp
                                     expb-rewrite comp-constraints)
                  :use (comp-constraints-lemma (:instance bits-bounds (x (opb)) (i 104) (j 0))))))

(defthmd expb-0-b
  (implies (and (equal (mulovfl) 0) (= (expb) 0))
           (and (iff (= (absval (expb) (chop (sigb) -53)) (abs (b)))
	             (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0)))
		(implies (not (= (b) 0)) (iff (= (signb) 0) (>= (b) 0)))
		(<= (absval (expb) (chop (sigb) -53)) (abs (b)))
                (< (abs (b)) (absval (expb) (+ (chop (sigb) -53) (expt 2 53))))))
  :hints (("Goal" :in-theory (enable comp-constraints)
                  :use (expb-0-b-0 expb-0-b-1 comp-constraints-lemma))))

(defund a () (val (signa) (expa) (siga)))

(in-theory (disable (a)))

(local-defthmd a-rewrite-1
  (implies (and (= (fzp) 1) (= (expa) 0))
           (equal (a) 0))
  :hints (("Goal" :in-theory (enable bvecp a expnt ndecode ddecode decode expa cat signa siga expf fraca-rewrite
                              opax checkdenorm opaz encodingp denormp fzp sigf sgnf dp val absval sign comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-shift-up-1 (x (opa)) (k 53) (i 115) (j 105))))))

(local-defthmd a-rewrite-2
  (implies (not (and (= (fzp) 1) (= (expa) 0)))
           (equal (a) (decode (opa) (dp))))
  :hints (("Goal" :in-theory (enable bvecp a expnt ndecode ddecode decode expa cat signa siga expf fraca-rewrite
                              manf opax checkdenorm opaz encodingp denormp fzp sigf sgnf dp val absval sign comp-constraints)
                  :use (comp-constraints-lemma
		        (:instance bits-bounds (x (opa)) (i 51) (j 0))
		        (:instance bits-shift-up-1 (x (opa)) (k 53) (i 115) (j 105))
			(:instance bitn-shift-up (x (opa)) (k 53) (n 63))
			(:instance bits-shift-up-2 (x (bits (opa) 51 0)) (k 53) (i 51))
			(:instance bits-shift-up-1 (x (BITS (* 9007199254740992 (OPA)) 116 105)) (k 105) (i 115) (j 105))))))

(defthmd a-rewrite
  (equal (a)
         (if (and (= (fzp) 1) (= (expa) 0)) 0 (decode (opa) (dp))))
  :hints (("Goal" :use (a-rewrite-1 a-rewrite-2))))

(defthmd a+b<>0
  (not (equal (+ (a) (b)) 0))
  :hints (("Goal" :in-theory (enable expnt opaz opax checkdenorm expf dp expa fzp a-rewrite comp-constraints)
                  :use (comp-constraints-lemma))))
  
(defthm rat-b
  (rationalp (b))
  :hints (("Goal" :in-theory (enable comp-constraints) :use (comp-constraints-lemma))))

(defthmd opblong-rewrite
  (implies (= (mulovfl) 0)
           (equal (opblong)
                  (if (or (= (fma) 0)
	                  (and (= (expb) 0)
	                       (= (fracb) 0)
	                       (= (bitn (mulexcps) 4) 0)))
	              0 1)))
  :hints (("Goal" :in-theory (enable mulovfl fracb frac expb-rewrite opblong comp-constraints)
                  :use (b-0 comp-constraints-lemma))))

(defthm expb-pos-mulstk
  (implies (and (= (mulovfl) 0) (> (expb) 0))
           (equal (mulstk) 0))
  :hints (("Goal" :in-theory (enable mulovfl opblong-rewrite mulstk expb-rewrite comp-constraints)
                  :use (comp-constraints-lemma))))
