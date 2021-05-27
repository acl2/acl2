(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "fadd64")
(include-book "../fmul/fmul64")

(local (include-book "round"))
(local (include-book "comp"))
(local (include-book "fadd"))
(local (include-book "fma"))

;;*******************************************************************************
;; Overview
;;*******************************************************************************

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
;;                       (equal (bitn (logior rin flags) (ixc)) (bitn r-spec (ixc)))
;;                       (equal (bitn (logior rin flags) (ufc)) (bitn r-spec (ufc)))
;;                       (equal (bitn (logior rin flags) (ofc)) (bitn r-spec (ofc)))))))))

;; The final theorems for FADD and FMUL will be derived from fadd64-comp.

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

;; We define a constant function corresponding to every variable bindong in the
;; definition of execute.  The definitions are ugly because their bodies are
;; lifted from that of the automatically generated definition.  This means that
;; nothing is required for the proof of the equivalence lemma other than
;; expanding the definitions, so that the rewriter can be turned off, which
;; allows the proof to go through quickly.

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

;;*******************************************************************************
;; Local Variables of Auxiliary Functions
;;*******************************************************************************

;; For each auxiliary function called by execute, we follow the same procedure,
;; defining constants corresponding to their local variables and proving an
;; equivalence lemma that allows us to use them in the proof in the same way
;; that we use the locals of execute.  Here we include only the definitions
;; of those constants that are mentioned in this summary of the proof.

;; The following constants are shared by the auxiliary functions:

(defund signa () (sign (opaz)))

(defund signb () (sign (opbz)))

(defund expa () (expnt (opaz)))

(defund expb () (expnt (opbz)))

(defund fraca () (frac (opaz)))

(defund fracb () (frac (opbz)))

(defund siga () (setbits (setbitn (bits 0 107 0) 108 106 (log<> (expa) 0)) 108 105 1 (fraca)))

(defund sigb () (setbits (setbitn (bits 0 107 0) 108 106 (log<> (expb) 0)) 108 105 1 (fracb)))

(defund a () (val (signa) (expa) (siga)))

;; Variables of add:

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


;; Variables of computelshift:

(defund expl () (bits (if1 (log>= (expa) (expb)) (expa) (expb)) 11 0))

(defund lza () (computelza (opaz) (opbz)))

;; Variables of computelza:

(defund fracl () (if1 (opbgeopa) (fracb) (fraca))) 

(defund fracs () (if1 (opbgeopa) (fraca) (fracb))) 

(defund in1lza ()
  (setbits (setbitn (bits 0 127 0) 128 127 1) 128 126 22 (fracl)))

(defund in2lza ()
  (if1 (log= (bitn (expb) 0) (bitn (expa) 0))
       (setbits (bits (- (ash 1 22) 1) 127 0) 128 126 22 (lognot (fracs)))
       (setbitn (setbits (bits (- (ash 1 21) 1) 127 0) 128 125 21 (lognot (fracs)))
                128 127 1)))

;; Variables of rndinfo:

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


;;*******************************************************************************
;; Alignment
;;*******************************************************************************

;; Under the condition that expovfl = 0, the far path is taken just in the case
;; of unlike signs and an exponent difference of 0 or 1 (Lemma 3.1):

(defthmd far-rewrite
  (implies (equal (mulovfl) 0)
           (equal (far)
                  (if (and (= (usa) 1)
                           (or (= (expa) (expb))
                               (= (expa) (1+ (expb)))
                               (= (1+ (expa)) (expb))))
                      0
                    1))))

;; It must be proved that the variable opbgeopa correctly identifies the larger
;; operand (Lemma 3.2):

(defthmd opbgeopa-b>=a
  (implies (equal (mulovfl) 0)
           (equal (opbgeopa)
                  (if (>= (abs (b)) (abs (a))) 1 0))))

;; Exponent of the larger operand:

(defund exps ()
  (if (>= (expa) (expb)) (expb) (expa)))

;; The exponent is decremented in the case far = usa = 1:

(defund explp ()
  (if1 (logand1 (far) (usa)) (1- (expl)) (expl)))

;; Shifted and truncated significand of the larger operand (Lemma 3.4 (a)):

(defthmd sigshft-rewrite
  (implies (= (mulovfl) 0)
           (equal (sigshft) (fl (* (expt 2 (- (expdiff))) (sigs))))))

;; The boolean shiftout is an indication that the sigshft is
;; imprecise (Lemma 3.4 (b)):

(defthmd shiftout-rewrite
  (implies (= (mulovfl) 0)
           (equal (shiftout)
                  (if (= (sigshft) (* (expt 2 (- (expdiff))) (sigs))) 0 1))))

;; This can happen only in the far case (Lemma 3.5):

(defthm near-shiftout-0
  (implies (and (= (mulovfl) 0) (= (far) 0))
           (equal (shiftout) 0))
  :rule-classes ())

;; Bounds on the shifted significand (Lemma 3.6):

(defthmd shiftout-1-bounds
  (implies (and (= (mulovfl) 0) (= (shiftout) 1))
           (and (<= (+ (sigshft) (expt 2 (- 1 (expdiff))))
                    (* (expt 2 (- (expdiff))) (sigs)))
                (<= (* (expt 2 (- (expdiff))) (sigs))
                    (- (1+ (sigshft)) (expt 2 (- 1 (expdiff))))))))


;;*******************************************************************************
;; Addition
;;*******************************************************************************

;; The case of a precise product (Lemma 4.1):

(defthm sum-bounds-0
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (explp) (sum)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (explp) (1+ (sum))))
		(iff (= (absval (explp) (sum)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ())

;; The case of an imprecisely approximated product (Lemma 4.2):

(defthm sum-bounds-1
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (< (absval (explp) (chop (sum) -53))
	           (abs (+ (a) (b))))
	        (< (abs (+ (a) (b)))
		   (absval (explp) (+ (chop (sum) -53) (expt 2 53))))
		(or (= (stk) 1)
	            (not (equal (bits (sum) 52 0) 0)))))
  :rule-classes ())


;;*******************************************************************************
;; Leading Zero Anticipation
;;*******************************************************************************

;; Counting leading zeroes (Lemma 5.1):

(defthmd clz128-expo
  (implies (bvecp x 128)
           (equal (clz128 x) (- 127 (expo x)))))

;; The inputs to lza128:

(defthmd in1lza-rewrite
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0) (= (expa) (expb)))
           (equal (in2lza) (- (expt 2 128) (1+ (* (expt 2 21) (sigs)))))))

(defthmd in2lza-rewrite
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (in2lza)
	          (- (expt 2 128) (1+ (* (expt 2 (- 21 (expdiff))) (sigs)))))))

;; The sum of the inputs (mod 2^(128) is 1 less than the shifted sum:

(defthmd sum-lza
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (+ (in1lza) (in2lza)) (+ (expt 2 128) (1- (* (expt 2 21) (sum)))))))

;; Therefore, for the purpose of the proof, we increment one of the inputs:

(defund in1lzap () (1+ (in1lza)))

;; the resulting value lza' returned by lza128 is shown to be the (approximate)
;; leading zero count of the sum (Lemma5.2):

(defund lzap () (lza128 (in1lzap) (in2lza)))

(defthm expo-sum-lzap
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (or (= (expo (sum)) (- 106 (lzap)))
               (= (expo (sum)) (- 107 (lzap)))))
  :rule-classes ())

;; We need to know that the count is always positive (Lemma 5.3):

(defthm lzap-pos
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (not (zp (lzap))))
  :rule-classes ())

;; in1lza and inlza' agree at every index except 0.  Consequently, the adjustment,
;; does not affect the count (Lemmas 5.4 and 5.5):

(defthm bitn-in1lza-in1lzap
  (implies (not (zp k))
           (equal (bitn (in1lzap) k)
	          (bitn (in1lza) k))))

(defthmd lza=lzap
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (lza) (lzap))))

(defthm expo-sum-lza
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (or (= (expo (sum)) (- 106 (lza)))
               (= (expo (sum)) (- 107 (lza)))))
  :rule-classes ())


;;*******************************************************************************
;; Normalization
;;*******************************************************************************

;; The shifted sum and bounds on the adjusted exponent (Lemma 6.1):

(defthmd sumshft-rewrite
  (implies (= (mulovfl) 0)
           (equal (sumshft) (* (expt 2 (lshift)) (sum)))))

(defthmd expshft>0-sumshft
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (>= (expo (sumshft)) 106)))

(defthmd expshft=0-sumshft
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (<= (expo (sumshft)) 106)))

;; Accuracy of the sum (Lemma 6.2):

(defthm expshft-sumshft-0
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (sumshft)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (1+ (sumshft))))
		(iff (= (absval (expshft) (sumshft)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ())

(defthm expshft-sumshft
  (implies (= (mulovfl) 0)
           (and (<=  (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (+ (chop (sumshft) -53) (expt 2 53))))
		(iff (= (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
                     (and (= (bits (sumshft) 52 0) 0)
		          (= (stk) 0)))))
  :rule-classes ())


;;*******************************************************************************
;; Rounding
;;*******************************************************************************

;; Rounding control bits for the overflow and normal cases (Lemma 7.1):

(defthmd lovfl-rewrite
  (implies (= (mulovfl) 0)
           (equal (lovfl) (bitn (sumshft) 55))))

(defthmd govfl-rewrite
  (implies (= (mulovfl) 0)
           (equal (govfl) (bitn (sumshft) 54))))

(defthmd lnorm-rewrite
  (implies (= (mulovfl) 0)
           (equal (lnorm) (bitn (sumshft) 54))))

(defthmd gnorm-rewrite
  (implies (= (mulovfl) 0)
           (equal (gnorm) (bitn (sumshft) 53))))

(defthmd sovfl-lemma
  (implies (= (mulovfl) 0)
           (iff (equal (sovfl) 0)
	        (and (equal (bits (sumshft) 53 0) 0)
                     (equal (stk) 0)))))

(defthmd sovfl-rewrite
  (implies (= (mulovfl) 0)
           (equal (sovfl)
	          (if (and (equal (bits (sumshft) 53 0) 0)
                           (equal (stk) 0))
		      0 1))))

(defthmd snorm-rewrite
  (implies (= (mulovfl) 0)
           (equal (snorm)
	          (if (and (equal (bits (sumshft) 52 0) 0)
                           (equal (stk) 0))
		      0 1))))


;; The rounding mode:

(defund mode () (fpscr-rc (rin)))

;; The rounding mode applied to the absolute value of the sum:

(defund modep () (if1 (signout) (flip-mode (mode)) (mode)))

;; Justification of the definition (Lemma 7.2):

(defthmd rnd-modep-rmode
  (implies (= (mulovfl) 0)
           (equal (rnd (+ (a) (b)) (mode) 53)
                  (if (= (signl) 0)
	              (rnd (abs (+ (a) (b))) (modep) 53)
    	            (- (rnd (abs (+ (a) (b))) (modep) 53))))))

(defthmd drnd-modep-rmode
  (implies (= (mulovfl) 0)
           (equal (drnd (+ (a) (b)) (mode) (dp))
                  (if (= (signl) 0)
	              (drnd (abs (+ (a) (b))) (modep) (dp))
	            (- (drnd (abs (+ (a) (b))) (modep) (dp)))))))

;; The case expshft > 0 (Lemma 7.3):

(defthmd rnd-expshft-pos-107
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (and (>= (abs (+ (a) (b))) (spn (dp)))
	        (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 51)))
		          (sumovfl)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (govfl) 0)
		          (= (sovfl) 0))))))

(defthmd rnd-expshft-pos-106
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (and (>= (abs (+ (a) (b))) (spn (dp)))
	        (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 52)))
		          (sumnorm)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0))))))

;; The case expshft = 0 (Lemma 7.4):

(defthmd rnd-expshft-0-norm
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (and (>= (abs (+ (a) (b))) (spn (dp)))
	        (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0))))))

(defthmd rnd-expshft-0-denorm
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106))
           (and (< (abs (+ (a) (b))) (spn (dp)))
	        (equal (drnd (abs (+ (a) (b))) (modep) (dp))
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (equal (drnd (abs (+ (a) (b))) (modep) (dp))
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0))))))

;; The overflow bits in the case expo(sumshft) = 107 (Lemma 7.5):

(defthm ovfl-107
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 107))
           (and (implies (= (ovfl2) 0)
	                 (equal (expo (sumovfl)) 52))
                (implies (= (ovfl2) 1)
                         (equal (sumovfl) (expt 2 53)))
                (or (= (ovfl2) 1) (= (ovfl) 1))))
  :rule-classes ())

;; The overflow bits in the case expo(sumshft) = 106 (Lemma 7.6):

(defthm ovfl-106
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106))
           (and (= (ovfl2) 0)
                (implies (= (ovfl) 0)
                         (equal (expo (sumnorm)) 52))
	        (implies (= (ovfl) 1)
                         (and (equal (sumnorm) (expt 2 53))
			      (equal (sumovfl) (expt 2 52))
			      (equal (govfl) 1)
			      (or (= (gnorm) 1) (= (snorm) 1))))))
  :rule-classes ())

;; The overflow bits in the case expo(sumshft) < 107 (Lemma 7.7):

(defthmd ovfl-denorm
  (implies (and (= (mulovfl) 0) (< (expo (sumshft)) 106))
           (and (= (ovfl2) 0)
	        (= (ovfl) 0)
		(<= (sumnorm) (expt 2 52)))))


;;*******************************************************************************
;; Main Theorems
;;*******************************************************************************

;; The main theorem for the computational case, derived as explained under "Proof Strategy":

(defthm fadd64-comp
  (implies (comp-constraints opa opb rin fma inz piz expovfl mulexcps b)
           (let* ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22))
                  (a (if (and (= fz 1) (= (expf opa (dp)) 0)) 0 (decode opa (dp)))))
             (mv-let (d flags) (fadd64 opa opb fz dn rmode fma inz piz expovfl mulexcps)
               (mv-let (d-spec r-spec) (arm-post-comp (+ a b) rin (dp))
                 (and (equal d d-spec)
                      (equal (bitn (logior rin flags) (ixc)) (bitn r-spec (ixc)))
                      (equal (bitn (logior rin flags) (ufc)) (bitn r-spec (ufc)))
                      (equal (bitn (logior rin flags) (ofc)) (bitn r-spec (ofc))))))))
  :rule-classes ())

;; The final theorem for FADD:

(defthm fadd64-correct
  (implies (and (bvecp opa 64)
                (bvecp opb 117)
                (bvecp rin 32)
                (equal fma 0)
                (bvecp mulexcps 8)
                (bitp inz)
                (bitp piz)
                (bitp expovfl)
                (equal (bits opb 52 0) 0)
                (equal (bits rin 12 8) 0)
                (equal (bitn rin 15) 0))
          (let ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22)) (opbhi (bits opb 116 53)))
             (mv-let (d flags) (fadd64 opa opb fz dn rmode fma inz piz expovfl mulexcps)
               (mv-let (d-spec r-spec) (arm-binary-spec 'add opa opbhi rin (dp))
                 (and (equal d d-spec)
                      (equal (logior rin flags) r-spec))))))
  :rule-classes ())

;; The final theorem for FMA:

(defthm fadd64-fma
  (implies (and (bvecp opa 64)
                (bvecp opb 64)
                (bvecp opc 64)
                (bvecp rin 32)
                (equal fma 1)
                (equal (bits rin 12 8) 0)
                (equal (bitn rin 15) 0))
           (let ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22)))
             (mv-let (opd mulexcps piz inz expovfl) (fmul64 opb opc fz dn rmode fma)
	       (mv-let (d flags) (fadd64 opa opd fz dn rmode fma inz piz expovfl mulexcps)
	         (mv-let (d-spec r-spec) (arm-fma-spec opa opb opc rin (dp))
                   (and (equal d d-spec)
                        (equal (logior rin flags) r-spec)))))))
  :rule-classes ())
