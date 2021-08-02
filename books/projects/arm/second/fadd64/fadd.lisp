(in-package "RTL")

(include-book "comp")

(local (include-book "arithmetic-5/top" :dir :system))

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

(local-defund fadd-constraints (opa opb rin fma inz piz expovfl mulexcps)
  (and (bvecp opa 64)
       (bvecp opb 117)
       (bvecp rin 32)
       (equal fma 0)
       (bvecp mulexcps 8)
       (bitp inz)
       (bitp piz)
       (bitp expovfl)
       (equal (bits opb 52 0) 0)
       (equal (bits rin 12 8) 0)
       (equal (bitn rin 15) 0)))

(local (encapsulate (((opa) => *) ((opb) => *) ((rin) => *) ((fma) => *) ((inz) => *) ((piz) => *) ((expovfl) => *) ((mulexcps) => *))
  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun rin () 0))
  (local (defun fma () 0))
  (local (defun inz () 0))
  (local (defun piz () 0))
  (local (defun expovfl () 0))
  (local (defun mulexcps () 0))
  (defthmd fadd-constraints-lemma (fadd-constraints (opa) (opb) (rin) (fma) (inz) (piz) (expovfl) (mulexcps)))))

(local-defthmd bvecp-opa (bvecp (opa) 64) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd bvecp-opb (bvecp (opb) 117) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd bvecp-rin (bvecp (rin) 32) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthm fma-0 (equal (fma) 0) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd bvecp-mulexcps (bvecp (mulexcps) 8) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd bitp-inz  (bitp (inz)) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd bitp-piz (bitp (piz)) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd bitp-expovfl (bitp (expovfl)) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthmd opb-low (equal (bits (opb) 52 0) 0) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthm bitn-rin-15 (equal (bitn (rin) 15) 0) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthm bits-rin-12-8 (equal (bits (rin) 12 8) 0) :hints (("Goal" :in-theory (enable fadd-constraints) :use (fadd-constraints-lemma))))
(local-defthm bitn-rin-12 (equal (bitn (rin) 12) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 4))))))
(local-defthm bitn-rin-11 (equal (bitn (rin) 11) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 3))))))
(local-defthm bitn-rin-10 (equal (bitn (rin) 10) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 2))))))
(local-defthm bitn-rin-9 (equal (bitn (rin) 9) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 1))))))
(local-defthm bitn-rin-8 (equal (bitn (rin) 8) 0) :hints (("Goal" :use ((:instance bitn-bits (x (rin)) (i 12) (j 8) (k 0))))))

(local-defund a () (if (and (= (bitn (rin) 24) 1) (= (expf (opa) (dp)) 0)) 0 (decode (opa) (dp))))
(local-defund opbhi () (bits (opb) 116 53))
(local-defund b () (if (and (= (bitn (rin) 24) 1) (= (expf (opbhi) (dp)) 0)) 0 (decode (opbhi) (dp))))
(local-in-theory (disable (a) (opbhi) (b)))

;;*******************************************************************************
;; Formulation and proof of equivalence-lemma
;;*******************************************************************************

(local-defund fzp () (bitn (rin) 24))
(local-defund dnp () (bitn (rin) 25))
(local-defund rmode () (bits (rin) 23 22))

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
       (mv-let (opbz flags) (checkdenorm (opb) (flags-2) (fzp))
         (declare (ignore flags))
         opbz)
       (opb)))

(local-defund flags-3 ()
  (if1 (lognot1 (fma))
       (mv-let (opb flags) (checkdenorm (opb) (flags-2) (fzp))
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

(local-defund signout () (if1 (mulovfl) (sign (opb)) (signl)))

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

(local-defund specialp ()
  (or (nanp (opa) (dp))
      (infp (opa) (dp))
      (nanp (opbhi) (dp))
      (infp (opbhi) (dp))
      (= (+ (a) (b)) 0)))

(local-in-theory (disable (specialp)))

(local-defthm rin-12-10
  (equal (bits (rin) 12 10) 0)
  :hints (("Goal" :use ((:instance bits-bits (x (rin)) (i 12) (j 8) (k 4) (l 2)))
                  :in-theory (disable bits-bits))))

(local-defthmd expa-bound
  (implies (not (specialp))
           (< (expf (opa) (dp)) 2047))
  :hints (("Goal" :in-theory (enable specialp nanp infp expf expw manf dp encodingp unsupp bvecp-opa)
                  :use ((:instance bits-bounds (x (opa)) (i 62) (j 52))))))

(local-defthmd expb-bound
  (implies (not (specialp))
           (< (bits (opb) 115 105) 2047))
  :hints (("Goal" :in-theory (enable specialp nanp infp expf expw manf dp encodingp unsupp bvecp-opb opbhi)
                  :use ((:instance bits-bounds (x (opb)) (i 115) (j 105))))))

(local-defthmd a+b<>0
  (implies (not (specialp))
           (not (= (+ (a) (b)) 0)))
  :hints (("Goal" :in-theory (enable specialp))))

(local-defthmd b-signb
  (implies (and (not (specialp))
                (not (= (b) 0)))
           (equal (bitn (opb) 116)
	          (if (< (b) 0) 1 0)))
  :hints (("Goal" :in-theory (enable b opbhi decode ddecode ndecode dp bias prec sgnf bitn-bits bits-bits))))

(local-defthmd b-val-pos
  (implies (and (not (specialp))
                (> (bits (opb) 115 105) 0))
	   (equal (b)
	          (val (bitn (opb) 116) (bits (opb) 115 105) (+ (expt 2 106) (* 2 (bits (opb) 104 0))))))
  :hints (("Goal" :in-theory (enable sgnf manf expf dp val absval b opbhi bitn-bits bits-bits opb-low decode ndecode)
                  :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd b-val-zero
  (implies (and (not (specialp))
                (= (bits (opb) 115 105) 0))
	   (equal (abs (b))
	          (absval (bits (opb) 115 105)
		          (chop (if (= (bitn (rin) 24) 1) 0 (* 2 (bits (opb) 104 0))) -53))))
  :hints (("Goal" :in-theory (enable sgnf sigf manf expf dp val absval b opbhi bitn-bits bits-bits opb-low decode ddecode chop)
                  :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd b-val-zero-<
  (implies (and (not (specialp))
                (= (bits (opb) 115 105) 0))
	   (< (abs (b))
	      (absval (bits (opb) 115 105)
		      (+ (chop (if (= (bitn (rin) 24) 1) 0 (* 2 (bits (opb) 104 0))) -53) (expt 2 53)))))
  :hints (("Goal" :in-theory (enable sgnf sigf manf expf dp val absval b opbhi bitn-bits bits-bits opb-low decode ddecode chop)
                  :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd opb-low-2
  (equal (BITS (* 2 (BITS (OPB) 104 0)) 52 0)
         0)
  :hints (("Goal" :in-theory (enable opb-low)
                  :use ((:instance bits-shift-up-2 (x (BITS (OPB) 104 0)) (k 1) (i 51))
		        (:instance bits-bits (x (opb)) (i 52) (j 0) (k 51) (l 0))))))

(local-defund rz ()
  (if (and (= (bitn (rin) (fz)) 1)
           (or (denormp (opa) (dp)) (denormp (opbhi) (dp))))
      (set-flag 7 (rin))
    (rin)))

(local-in-theory (disable (rz)))

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

(local-defthmd fadd-comp-constraints
  (implies (not (specialp))
           (comp-constraints (opa) (opb) (rz) 0 (inz) (piz) (expovfl) (mulexcps) (b)))
  :hints (("Goal" :in-theory (enable comp-constraints bvecp-opa bvecp-opb bvecp-mulexcps 
                              prec dp sigw expw opb-low opb-low-2 b-signb expf a)
                  :use (b-val-zero-< b-val-pos bitp-inz bitp-piz bitp-expovfl expa-bound expb-bound a+b<>0 b-val-zero))))

(local-defthm fadd-comp
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rz) (dp))
             (and (equal (d) d-spec)
                  (equal (bitn (logior (rz) (flags)) 4) (bitn r-spec 4))
                  (equal (bitn (logior (rz) (flags)) 3) (bitn r-spec 3))
                  (equal (bitn (logior (rz) (flags)) 2) (bitn r-spec 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fadd64-comp (opa (opa)) (opb (opb)) (rin (rz)) (fma (fma)) (inz (inz))
                                               (piz (piz)) (expovfl (expovfl)) (mulexcps (mulexcps)) (b (b))))
		  :in-theory (enable a equivalence-lemma fadd-comp-constraints))))

(local-defthmd opbnan-nanp
  (equal (opbnan)
         (if (nanp (opbhi) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable nanp opbnan expf dp expb encodingp unsupp opbz expnt checkdenorm opblong fracb
                                     opb-low manf frac opbhi)
	          :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd opbsnan-nanp
  (equal (opbsnan)
         (if (snanp (opbhi) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable snanp opbsnan nanp opbnan expf dp expb encodingp unsupp opbz expnt checkdenorm 
                                     bitn-bits opblong fracb opb-low manf frac opbhi)
	          :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd opbqnan-nanp
  (equal (opbqnan)
         (if (qnanp (opbhi) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable qnanp opbqnan nanp opbnan expf dp expb encodingp unsupp opbz expnt checkdenorm 
                                     bitn-bits opblong fracb opb-low manf frac opbhi)
	          :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

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

(local-defthm int-opb
  (integerp (opb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (bvecp-opb))))

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

(local-defthmd opbinf-infp
  (equal (opbinf)
         (if (infp (opbhi) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable infp opbinf expf dp expb encodingp unsupp opbz expnt checkdenorm opblong fracb
                                     opb-low manf frac opbhi)
	          :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd opainf-infp
  (equal (opainf)
         (if (infp (opa) (dp))
	     1 0))
  :hints (("Goal" :in-theory (enable infp opainf expf dp expa encodingp unsupp opaz expnt checkdenorm fraca
                                     bvecp-opa cat opax manf frac))))

(local-defthm mulovfl-0
  (equal (mulovfl) 0)
  :hints (("Goal" :in-theory (enable opblong mulovfl))))

(local-defthm mulstk-0
  (equal (mulstk) 0)
  :hints (("Goal" :in-theory (enable opblong mulstk))))

(local-defthmd opbzero-zerop
  (equal (opbzero)
         (if (= (b) 0)
	     1 0))
  :hints (("Goal" :in-theory (enable zerop opbzero expf dp expb encodingp unsupp opbz expnt checkdenorm opblong fracb
                                     fzp sigf sgnf decode ndecode ddecode b opb-low manf frac opbhi)
	          :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd opazero-zerop
  (equal (opazero)
         (if (= (a) 0)
	     1 0))
  :hints (("Goal" :in-theory (enable zerop opazero expf dp expa encodingp unsupp opaz expnt checkdenorm fraca
                                     cat opax fzp sigf sgnf decode ndecode ddecode a manf frac))))

(local-defthm sum-0-1
  (implies (and (= (fzp) 1) (= (expa) 0))
           (and (equal (a) 0)
	        (equal (fraca) 0)))
  :hints (("Goal" :in-theory (enable opaz sigw expw dp fraca frac checkdenorm expnt expf opax expa a fzp))))

(local-defthm sum-0-2
  (implies (and (= (fzp) 1) (= (expb) 0))
           (and (equal (b) 0)
	        (equal (fracb) 0)))
  :hints (("Goal" :in-theory (enable opbhi opbz sigw expw dp fracb frac checkdenorm expnt expf expb b fzp))))

(local-defthm sum-0-3
  (implies (= (signa) (signb))
           (iff (= (+ (a) (b)) 0)
	        (and (= (a) 0) (= (b) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable decode ddecode ndecode opbhi a b opaz opax opbz sigw expw dp fraca fracb frac 
                              bitn-bits sigf manf sgnf checkdenorm expnt expf expb b fzp sign signa signb))))

(local-defthmd sum-0-4
  (implies (not (= (a) 0))
           (equal (signa)
	          (if (< (a) 0) 1 0)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode opbhi a b opaz opax opbz sigw expw dp fraca fracb frac 
                              bitn-bits sigf manf sgnf checkdenorm expnt expf expb b fzp sign signa signb))))

(local-defthmd sum-0-5
  (implies (not (= (b) 0))
           (equal (signb)
	          (if (< (b) 0) 1 0)))
  :hints (("Goal" :in-theory (enable decode ddecode ndecode opbhi a b opaz opax opbz sigw expw dp fraca fracb frac 
                              bitn-bits sigf manf sgnf checkdenorm expnt expf expb b fzp sign signa signb))))

(local-defthm sum-0-6
  (implies (not (and (= (fzp) 1) (= (expa) 0)))
           (iff (equal (a) 0)
	        (and (equal (expa) 0) (equal (fraca) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signa bitn-bits sigf manf sgnf sigw expw decode ddecode ndecode opaz sigw
                              cat expw dp fraca frac checkdenorm expnt expf opax expa a fzp))))

(local-defthm sum-0-7
  (implies (not (and (= (fzp) 1) (= (expb) 0)))
           (iff (equal (b) 0)
	        (and (equal (expb) 0) (equal (fracb) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sign signb bitn-bits sigf manf sgnf sigw expw decode ddecode ndecode opbz sigw
                              opb-low cat expw dp fracb frac checkdenorm expnt expf opbhi expb b fzp)
		  :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defund siga () 
  (if (= (expa) 0)
      (* 2 (fraca))
    (+ (expt 2 106) (* 2 (fraca)))))

(local-defund sigb () 
  (if (= (expb) 0)
      (* 2 (fracb))
    (+ (expt 2 106) (* 2 (fracb)))))

(local-in-theory (disable (siga) (sigb)))

(local-defthmd sum-0-8
  (implies (not (= (a) 0))
           (equal (abs (a))
	          (absval (expa) (siga))))
  :hints (("Goal" :in-theory (enable sign signa bitn-bits sigf manf sgnf sigw expw decode ddecode ndecode opaz sigw
                              siga absval cat expw dp fraca frac checkdenorm expnt expf opax expa a fzp))))

(local-defthmd sum-0-9
  (implies (not (= (b) 0))
           (equal (abs (b))
	          (absval (expb) (sigb))))
  :hints (("Goal" :in-theory (enable sign signb bitn-bits sigf manf sgnf sigw expw decode ddecode ndecode opbz sigw
                              sigb absval opb-low cat expw dp fracb frac checkdenorm expnt expf opbhi expb b fzp)
		  :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))))))

(local-defthmd bvecp-frac
  (and (bvecp (fraca) 105)
       (bvecp (fracb) 105))
  :hints (("Goal" :in-theory (enable frac fraca fracb))))

(local-defthmd sum-0-10
  (and (implies (not (= (expa) 0)) (> (* 2 (siga)) (sigb)))
       (implies (not (= (expb) 0)) (> (* 2 (sigb)) (siga))))
  :hints (("Goal" :in-theory (enable siga sigb) :use (bvecp-frac))))

(local-defthmd sum-0-11
  (and (implies (and (not (= (expa) 0)) (= (expb) 0)) (> (siga) (sigb)))
       (implies (and (not (= (expb) 0)) (= (expa) 0)) (> (sigb) (siga))))
  :hints (("Goal" :in-theory (enable siga sigb) :use (bvecp-frac))))

(local-defthmd hack-1
  (implies (not (zp n))
           (>= (expt 2 n) 2)))

(local-defthmd sum-0-12
  (implies (< (expa) (expb))
           (>= (expt 2 (- (expb) (expa))) 2))
  :hints (("Goal" :use ((:instance hack-1 (n (- (expb) (expa))))))))

(local-defthmd sum-0-13
  (implies (< (expa) (expb))
           (< (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-10 sum-0-11 sum-0-12) :in-theory (enable absval) :nonlinearp t)))

(local-defthmd hack-2
  (implies (not (zp n))
           (<= (expt 2 (- n)) 1/2)))

(local-defthmd sum-0-14
  (implies (> (expa) (expb))
           (<= (expt 2 (- (expb) (expa))) 1/2))
  :hints (("Goal" :use ((:instance hack-2 (n (- (expa) (expb))))))))

(local-defthmd sum-0-15
  (implies (and (> (expa) (expb)) (= (expb) 0))
           (> (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-10 sum-0-11 sum-0-14) :in-theory (enable absval) :nonlinearp t)))

(local-defthmd sum-0-16
  (implies (> (expa) (expb))
           (> (absval (expa) (siga)) (absval (expb) (sigb))))
  :hints (("Goal" :use (sum-0-10 sum-0-11 sum-0-14) :in-theory (enable absval) :nonlinearp t)))

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

(local-defthmd sum-0-17
  (implies (and (= (expa) (expb))
                (= (absval (expa) (siga)) (absval (expb) (sigb))))
           (equal (fraca) (fracb)))
  :hints (("Goal" :in-theory (enable absval siga sigb)
                  :use ((:instance hack-4 (x (fraca)) (y (fracb)) (z (expt 2 (+ -1128 (expa)))))))))

(local-defthmd sum-0-18
  (implies (and (not (= (a) 0))
                (not (= (b) 0))
		(= (abs (a)) (abs (b))))
           (and (equal (expa) (expb))
	        (equal (fraca) (fracb))))
  :hints (("Goal" :use (sum-0-17 sum-0-16 sum-0-13)
                  :in-theory (e/d (sum-0-8 sum-0-9) (abs)))))

(local-defthmd sum-0-19
  (implies (and (not (= (a) 0))
                (not (= (b) 0))
		(equal (expa) (expb))
	        (equal (fraca) (fracb)))
	   (equal (abs (a)) (abs (b))))
  :hints (("Goal" :in-theory (e/d (siga sigb sum-0-8 sum-0-9) (abs)))))

(local-defthm sum-0
  (iff (= (+ (a) (b)) 0)
       (if (= (signa) (signb))
           (and (= (a) 0) (= (b) 0))
         (and (= (expa) (expb))
              (= (fraca) (fracb)))))
  :rule-classes ()
  :hints (("Goal" :use (sum-0-3 sum-0-6 sum-0-7 sum-0-18 sum-0-19)
                  :in-theory (enable sum-0-4 sum-0-5))))

(local-defthmd isspecial-specialp
  (equal (isspecial)
         (if (specialp) 1 0))
  :hints (("Goal" :in-theory (enable checkspecial-lemma specialp isspecial* opaqnan-nanp opasnan-nanp opbqnan-nanp opbsnan-nanp
                                     piz-1 qnanp snanp opainf-infp opbinf-infp opazero-zerop opbzero-zerop)
		  :use (sum-0))))

(local-defthmd isspecial-0-flags
  (implies (= (isspecial) 0)
           (equal (flags-4) (flags-3)))
  :hints (("Goal" :in-theory (enable checkspecial-lemma specialp flags-4* isspecial* opaqnan-nanp opasnan-nanp opbqnan-nanp opbsnan-nanp
                                     piz-1 qnanp snanp opainf-infp opbinf-infp opazero-zerop opbzero-zerop))))

(local-defthmd flags-1-0
  (equal (flags-1) 0)
  :hints (("Goal" :in-theory (enable flags-1))))

(local-defthmd flags-3-rewrite
  (implies (natp k)
           (equal (bitn (flags-3) k)
	         (if (and (= k 7)
		          (= (fzp) 1)
			  (or (and (= (bits (opa) 62 52) 0)
			           (not (= (bits (opa) 51 0) 0)))
			      (and (= (bits (opbhi) 62 52) 0)
			           (not (= (bits (opbhi) 51 0) 0)))))			      
		     1
		   (bitn (flags-1) k))))
  :hints (("Goal" :in-theory (enable flags-2 flags-3 checkdenorm opaz opbz expnt expf expa expb opax fzp frac fraca fracb
                                     opb-low bvecp flags-1-0 bitn-bits cat opbhi)
		  :use ((:instance bits-plus-bits (x (opb)) (n 104) (p 53) (m 0))
		        (:instance bvecp-member (x k) (n 3))))))

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
  (if (and (= (bitn (rin) (fz)) 1) (denormp (opbhi) (dp)))
      (zencode (sgnf (opbhi) (dp)) (dp))
     (opbhi)))

(local-defund rz ()
  (if (and (= (bitn (rin) (fz)) 1)
           (or (denormp (opa) (dp)) (denormp (opbhi) (dp))))
      (set-flag 7 (rin))
    (rin)))

(local-in-theory (disable (opad) (opbd)))

(local-defthmd arm-binary-spec-rewrite
  (equal (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
         (let ((d (arm-binary-pre-comp-val 'add (opad) (opbd) (rz) (dp)))
               (r (arm-binary-pre-comp-excp 'add (opad) (opbd) (rz) (dp))))
	   (if d (mv d r)
	       (arm-binary-comp 'add (opad) (opbd) r (dp)))))
  :hints (("Goal" :in-theory (enable dp hp opad opbd rz))))

(local-in-theory (disable arm-binary-spec))

(local-defthmd nanp-infp-zencode
  (and (not (nanp (zencode (sgnf x (dp)) (dp)) (dp)))
       (not (infp (zencode (sgnf x (dp)) (dp)) (dp))))
  :hints (("Goal" :in-theory (enable encodingp unsupp expf manf sgnf manf cat dp expw sigw zencode infp nanp)
                  :use ((:instance bitn-0-1 (n 63))))))

(local-defthmd final-1
  (implies (not (specialp))
           (equal (arm-binary-pre-comp-val 'add (opad) (opbd) (rz) (dp))
                  ()))
  :hints (("Goal" :in-theory (enable opad opbd snanp qnanp specialp binary-undefined-p)
                  :use ((:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opbhi)))))))

(local-defthmd final-2
  (implies (not (specialp))
           (equal (arm-binary-pre-comp-excp 'add (opad) (opbd) (rz) (dp))
                  (rz)))
  :hints (("Goal" :in-theory (enable opad opbd specialp snanp qnanp binary-undefined-p)
                  :use ((:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opbhi)))))))

(local-defthmd final-3
  (implies (not (specialp))
           (equal (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
                  (arm-binary-comp 'add (opad) (opbd) (rz) (dp))))
  :hints (("Goal" :in-theory (enable arm-binary-spec-rewrite)
                  :use (final-1 final-2))))

(local-in-theory (disable arm-post-comp (arm-post-comp) arm-binary-spec (arm-binary-spec)))

(local-defthmd final-4
  (implies (not (specialp))
           (and (equal (decode (opad) (dp)) (a))
	        (equal (decode (opbd) (dp)) (b))))
  :hints (("Goal" :in-theory (enable expw sigw encodingp sigf sgnf denormp decode ddecode expf a b opad opbd specialp
                                     bvecp-opa zencode bitn-bits opbhi dp prec bias))))

(local-defthmd final-5
  (implies (not (specialp))
           (equal (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
                  (arm-post-comp (+ (a) (b)) (rz) (dp))))
  :hints (("Goal" :in-theory (enable opad opbd binary-eval specialp final-3)
                  :use (final-4
		        (:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opbhi)))))))

(local-defthm final-6
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (bitn (logior (rz) (flags)) 4) (bitn r-spec 4))
                  (equal (bitn (logior (rz) (flags)) 3) (bitn r-spec 3))
                  (equal (bitn (logior (rz) (flags)) 2) (bitn r-spec 2)))))
  :rule-classes ()
  :hints (("Goal" :use (fadd-comp)
                  :in-theory (enable final-5))))

(local-defthm final-7
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
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
			   (or (and (= (bits (opa) 62 52) 0)
			            (not (= (bits (opa) 51 0) 0)))
			       (and (= (bits (opbhi) 62 52) 0)
			            (not (= (bits (opbhi) 51 0) 0)))))			      
		      1
		    0)))
  :hints (("Goal" :in-theory (enable fzp isspecial-0-flags flags flags-3-rewrite flags-5-rewrite isspecial-specialp flags-1-0))))

(local-defthmd post-comp-bitn-other
  (implies (and (natp k) (not (member k '(2 3 4))))
           (equal (bitn (mv-nth 1 (arm-post-comp (+ (a) (b)) (rz) (dp))) k)
	          (bitn (rz) k)))
  :hints (("Goal" :in-theory (e/d (arm-post-comp) (bvecp-rz bvecp-set-flag))
                  :use (bvecp-rz))))

(local-defthmd r-spec-bitn-other
  (implies (and (not (specialp)) (natp k) (not (member k '(2 3 4))))
           (equal (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) k)
	          (bitn (rz) k)))
  :hints (("Goal" :in-theory (enable final-5)
                  :use (post-comp-bitn-other))))

(local-defthmd bitn-rz
  (implies (natp k)
           (equal (bitn (rz) k)
	          (if (and (= k 7)
		           (= (fzp) 1)
			   (or (and (= (bits (opa) 62 52) 0)
			            (not (= (bits (opa) 51 0) 0)))
			       (and (= (bits (opbhi) 62 52) 0)
			            (not (= (bits (opbhi) 51 0) 0)))))			      
		      1
		    (bitn (rin) k))))
  :hints (("Goal" :in-theory (enable bvecp-opa opbhi fzp denormp rz sigw expw encodingp prec dp explicitp sigf expf)
                  :use (bvecp-rin))))

(local-defthmd bvecp-flags
  (bvecp (flags) 8)
  :hints (("Goal" :in-theory (enable checkdenorm flags-5 flags-1 flags-2 flags-3 flags-4* checkspecial-lemma flags))))

(local-defthmd bvecp-logior-flags
  (bvecp (logior (rin) (flags)) 32)
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (bvecp-rin bvecp-flags (:instance logior-bvecp (n 32) (x (flags)) (y (rin)))))))

(local-defthmd bvecp-r-spec
  (bvecp (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 32)
  :hints (("Goal" :in-theory (enable arm-post-comp arm-binary-spec-rewrite))))

(local-defthmd final-8
  (implies (and (not (specialp)) (natp k) (< k 32) (not (member k '(2 3 4))))
           (equal (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) k)
	          (bitn (logior (rin) (flags)) k)))
  :hints (("Goal" :in-theory (e/d (bvecp bitn-logior r-spec-bitn-other bitn-rz flags-other) (flags))
                  :use (bvecp-flags final-7 bvecp-rin (:instance bvecp-member (x k) (n 5))))))

(local-defthmd final-9
  (implies (and (not (specialp)) (natp k))
           (equal (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) k)
	          (bitn (logior (rin) (flags)) k)))
  :hints (("Goal" :in-theory (enable bvecp) :use (final-8 final-7 bvecp-r-spec bvecp-logior-flags))))

(local-defthmd final-10
  (implies (not (specialp))
           (equal (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp)))
	          (logior (rin) (flags))))
  :hints (("Goal" :use (bvecp-r-spec bvecp-logior-flags
                        (:instance bit-diff-diff (x (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
                                                 (y (logior (rin) (flags))))
			(:instance final-9 (k (bit-diff (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp)))
			                                (logior (rin) (flags)))))))))

(local-defthm comp-case
  (implies (not (specialp))
           (mv-let (d-spec r-spec) (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :rule-classes ()
  :hints (("Goal" :use (final-7 final-10))))


;;*******************************************************************************
;; Special Case
;;*******************************************************************************

(local-defthmd final-12
  (implies (or (nanp (opa) (dp)) (infp (opa) (dp)))
           (equal (bits (opaz) 116 53)
	          (opa)))
  :hints (("Goal" :in-theory (enable opaz opax nanp checkdenorm expa expnt dp expw sigw manf expf sigf fzp encodingp frac fraca
                                     infp bvecp-opa unsupp))))

(local-defthmd final-13
  (implies (or (nanp (opbhi) (dp)) (infp (opbhi) (dp)))
           (equal (bits (opbz) 116 53)
	          (opbhi)))
  :hints (("Goal" :in-theory (enable opbz nanp checkdenorm expb expnt dp expw sigw manf expf sigf fzp encodingp frac fracb
                                     opbhi infp unsupp))))

(local-defthmd final-14
  (implies (specialp)
           (equal (d)
                  (if (snanp (opa) (dp))
	              (if1 (dnp) (defnan) (gag (opa)))
                    (if (snanp (opbhi) (dp))
                        (if1 (dnp) (defnan) (gag (opbhi)))
                      (if (qnanp (opa) (dp))
                          (if1 (dnp) (defnan) (opa))
                        (if (qnanp (opbhi) (dp))
                            (if1 (dnp) (defnan) (opbhi))
                          (if (infp (opa) (dp))
                              (if (and (infp (opbhi) (dp)) (not (= (signa) (signb))))
                                  (defnan)
                                (opa))
                            (if (infp (opbhi) (dp))
		                (opbhi)
                              (if (and (= (a) 0) (= (b) 0) (= (signa) (signb)))
                                  (zencode (signa) (dp))
                                (if (= (+ (a) (b)) 0)
                                    (if (= (rmode) 2)
                                        (zencode 1 (dp))
		                      (zencode 0 (dp)))
			          0))))))))))
  :hints (("Goal" :in-theory (enable checkspecial-lemma d-1* d isspecial-specialp opbsnan-nanp opasnan-nanp opbqnan-nanp opaqnan-nanp
                                     opainf-infp opbinf-infp opbhi snanp qnanp piz-1 final-12 final-13 dp bvecp-opa zencode gag
				     opazero-zerop opbzero-zerop bits-logior)
		  :use (signa-0-1 signb-0-1 sum-0))))

(local-defthmd final-14-a
  (implies (specialp)
           (equal (flags)
                  (if (snanp (opa) (dp))
	              (setbitn (flags-3) 8 0 1)
                    (if (snanp (opbhi) (dp))
                        (setbitn (flags-3) 8 0 1)
                      (if (qnanp (opa) (dp))
                          (flags-3)
                        (if (qnanp (opbhi) (dp))
                            (flags-3)
                          (if (and (infp (opa) (dp)) (infp (opbhi) (dp)) (not (= (signa) (signb))))
                              (setbitn (flags-3) 8 0 1)
		            (flags-3))))))))
  :hints (("Goal" :in-theory (enable checkspecial-lemma flags-4* d isspecial-specialp opbsnan-nanp opasnan-nanp opbqnan-nanp opaqnan-nanp
                                     opainf-infp opbinf-infp opbhi snanp qnanp piz-1 final-12 final-13 dp bvecp-opa zencode gag
				     opazero-zerop opbzero-zerop bits-logior)
		  :use (signa-0-1 signb-0-1 sum-0))))

(local-defthmd final-15
  (implies (snanp x (dp))
           (equal (process-nan x r '(nil 53 11))
	          (if1 (bitn r 25) (defnan) (gag x))))
  :hints (("Goal" :in-theory (enable snanp nanp encodingp defnan indef dp qnanize gag bits-logior))))

(local-defthmd final-16
  (implies (qnanp x (dp))
           (equal (process-nan x r '(nil 53 11))
	          (if1 (bitn r 25) (defnan) x)))
  :hints (("Goal" :in-theory (enable qnanp nanp encodingp defnan indef dp qnanize gag bits-logior)
                  :use ((:instance logior-2**n (n 51))))))

(local-defthm hack-5
  (implies (integerp x)
           (equal (bitn (+ 1 (* 2 x)) 0)
	          1))
  :hints (("Goal" :use ((:instance bitn-plus-mult (x 1) (m 1) (n 0) (k x))))))

(local-defthmd final-17
  (implies (and (specialp) (snanp (opa) (dp)))
           (and (equal (d)
	               (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
		(equal (bitn (logior (flags) (rin)) 0)
		       (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 0))))
  :hints (("Goal" :in-theory (e/d (arm-binary-spec arm-binary-pre-comp arm-binary-pre-comp-val arm-binary-comp
                                   nanp denormp sgnf zencode signa signb dp final-14 final-14-a bitn-logior final-15 final-16 snanp qnanp
				   unsupp fpscr-rc binary-zero-sgn binary-undefined-p cat binary-inf-sgn hp dnp)
				  (process-nan))
		  :use (bvecp-rin
		        (:instance bitn-0-1 (x (opa)) (n 63))
			(:instance bitn-0-1 (x (opbhi)) (n 63))))))

(local-defthmd final-18
  (implies (and (specialp) (not (snanp (opa) (dp))) (snanp (opbhi) (dp)))
           (and (equal (d)
	               (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
		(equal (bitn (logior (flags) (rin)) 0)
		       (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 0))))
  :hints (("Goal" :in-theory (e/d (arm-binary-spec arm-binary-pre-comp arm-binary-pre-comp-val arm-binary-comp
                                   nanp denormp sgnf zencode signa signb dp final-14 final-15 final-16 snanp qnanp
				   final-14-a bitn-logior unsupp fpscr-rc binary-zero-sgn binary-undefined-p cat binary-inf-sgn hp dnp)
				  (process-nan))
		  :use (bvecp-rin
		        (:instance bitn-0-1 (x (opa)) (n 63))
			(:instance bitn-0-1 (x (opbhi)) (n 63))))))

(local-defthm flags-3-rewrite-2
  (implies (and (natp k) (not (= k 7)))
           (equal (bitn (flags-3) k) 0))
  :hints (("Goal" :in-theory (enable flags-3-rewrite flags-1))))

(local-defthmd final-19
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(qnanp (opa) (dp)))
           (and (equal (d)
	               (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
		(equal (bitn (logior (flags) (rin)) 0)
		       (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 0))))
  :hints (("Goal" :in-theory (e/d (arm-binary-spec arm-binary-pre-comp arm-binary-pre-comp-val arm-binary-comp
                                   nanp denormp sgnf zencode signa signb dp final-14 final-15 final-16 snanp qnanp
				   final-14-a bitn-logior unsupp fpscr-rc binary-zero-sgn binary-undefined-p cat binary-inf-sgn hp dnp)
				  (process-nan))
		  :use (bvecp-rin
		        (:instance bitn-0-1 (x (opa)) (n 63))
			(:instance bitn-0-1 (x (opbhi)) (n 63))))))

(local-defthmd final-20
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(qnanp (opbhi) (dp)))
           (and (equal (d)
	               (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
		(equal (bitn (logior (flags) (rin)) 0)
		       (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 0))))
  :hints (("Goal" :in-theory (e/d (arm-binary-spec arm-binary-pre-comp arm-binary-pre-comp-val arm-binary-comp
                                   nanp denormp sgnf zencode signa signb dp final-14 final-15 final-16 snanp qnanp
				   final-14-a bitn-logior unsupp fpscr-rc binary-zero-sgn binary-undefined-p cat binary-inf-sgn hp dnp)
				  (process-nan))
		  :use (bvecp-rin
		        (:instance bitn-0-1 (x (opa)) (n 63))
			(:instance bitn-0-1 (x (opbhi)) (n 63))))))

(local-defthmd final-21
  (equal (signa) (sgnf (opa) (dp)))
  :hints (("Goal" :in-theory (enable prec dp sigw sgn signa opaz opax checkdenorm sign sgnf bitn-bits))))

(local-defthmd final-22
  (equal (signb) (sgnf (opbhi) (dp)))
  :hints (("Goal" :in-theory (enable prec dp sigw sgn signb opbz opbhi checkdenorm sign sgnf bitn-bits))))

(local-defthmd final-23
  (implies (infp x (dp))
           (equal (+ (* (expt 2 63) (bitn x 63))
	             (- (expt 2 63) (expt 2 52)))
		  x))
  :hints (("Goal" :in-theory (enable dp infp encodingp expf manf expw)
                  :use ((:instance bitn-plus-bits (n 63) (m 0))
			(:instance bits-plus-bits (n 62) (p 52) (m 0))))))

(local-defthm final-24
  (not (snanp (zencode x '(() 53 11)) '(() 53 11)))
  :hints (("Goal" :in-theory (enable zencode snanp nanp manf expf expw encodingp))))

(local-defthm final-25
  (not (qnanp (zencode x '(() 53 11)) '(() 53 11)))
  :hints (("Goal" :in-theory (enable zencode qnanp nanp manf expf expw encodingp))))

(local-defthm final-26
  (implies (infp x '(() 53 11))
           (not (denormp x '(() 53 11))))
  :hints (("Goal" :in-theory (enable denormp infp manf expf expw encodingp))))

(local-defthm final-27
  (not (infp (zencode x '(() 53 11)) '(() 53 11)))
  :hints (("Goal" :in-theory (enable zencode infp manf expf expw encodingp))))

(local-defthmd final-28
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(infp (opa) (dp)))
           (and (equal (d)
	               (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
		(equal (bitn (logior (flags) (rin)) 0)
		       (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 0))))
  :hints (("Goal" :in-theory (enable arm-binary-spec arm-binary-pre-comp arm-binary-pre-comp-val arm-binary-comp
                                     final-21 final-22 nanp sgnf dp final-14 final-15 final-16 fpscr-rc binary-undefined-p
				     final-14-a bitn-logior bvecp-opa cat binary-inf-sgn hp)
		  :use (bvecp-rin (:instance final-23 (x (opa)))))))

(local-defthmd final-29
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (infp (opa) (dp)))
		(infp (opbhi) (dp)))
           (and (equal (d)
	               (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))
		(equal (bitn (logior (flags) (rin)) 0)
		       (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) 0))))
  :hints (("Goal" :in-theory (enable arm-binary-spec arm-binary-pre-comp arm-binary-pre-comp-val arm-binary-comp
                                     final-21 final-22 nanp sgnf dp final-14 final-15 final-16 fpscr-rc binary-undefined-p
				     final-14-a bitn-logior bvecp-opa cat binary-inf-sgn hp)
		  :use (bvecp-rin (:instance final-23 (x (opbhi)))))))

(local-defthmd final-30
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (and (infp (opa) (dp))
		          (infp (opbhi) (dp))
			  (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp)))))))
           (equal (arm-binary-pre-comp-val 'add (opad) (opbd) (rz) (dp))
                  ()))
  :hints (("Goal" :in-theory (enable opad opbd snanp qnanp binary-undefined-p)
                  :use ((:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opbhi)))))))

(local-defthmd final-31
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (and (infp (opa) (dp))
		          (infp (opbhi) (dp))
			  (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp)))))))
           (equal (arm-binary-pre-comp-excp 'add (opad) (opbd) (rz) (dp))
                  (rz)))
  :hints (("Goal" :in-theory (enable opad opbd snanp qnanp binary-undefined-p)
                  :use ((:instance nanp-infp-zencode (x (opa)))
		        (:instance nanp-infp-zencode (x (opbhi)))))))

(local-defthmd final-32
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (and (infp (opa) (dp))
		          (infp (opbhi) (dp))
			  (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp)))))))
           (equal (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
                  (arm-binary-comp 'add (opad) (opbd) (rz) (dp))))
  :hints (("Goal" :in-theory (enable arm-binary-spec-rewrite)
                  :use (final-30 final-31))))

(local-defthmd final-33
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (and (infp (opa) (dp))
		          (infp (opbhi) (dp))
			  (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp)))))))
           (and (equal (decode (opad) (dp)) (a))
	        (equal (decode (opbd) (dp)) (b))))
  :hints (("Goal" :in-theory (enable expw sigw encodingp sigf sgnf denormp decode ddecode expf a b opad opbd specialp
                                     infp bvecp-opa zencode bitn-bits opbhi dp prec bias))))

(local-defthmd infp-opad
  (iff (infp (opad) (dp))
       (infp (opa) (dp)))
  :hints (("Goal" :in-theory (enable opad manf unsupp expf dp denormp infp) :use ((:instance nanp-infp-zencode (x (opa)))))))

(local-defthmd infp-opbd
  (iff (infp (opbd) (dp))
       (infp (opbhi) (dp)))
  :hints (("Goal" :in-theory (enable opbd manf unsupp expf dp denormp infp) :use ((:instance nanp-infp-zencode (x (opbhi)))))))

(local-defthmd sgnf-opad
  (equal (sgnf (opad) (dp))
         (sgnf (opa) (dp)))
  :hints (("Goal" :in-theory (enable opad sgnf dp zencode))))

(local-defthmd sgnf-opbd
  (equal (sgnf (opbd) (dp))
         (sgnf (opbhi) (dp)))
  :hints (("Goal" :in-theory (enable opbd sgnf dp zencode))))

(local-defthmd final-34
  (implies (not (= (a) 0))
           (equal (sgnf (opa) (dp))
	          (if (< (a) 0) 1 0)))
  :hints (("Goal" :use (sum-0-4 final-21))))

(local-defthmd final-35
  (implies (not (= (b) 0))
           (equal (sgnf (opbhi) (dp))
	          (if (< (b) 0) 1 0)))
  :hints (("Goal" :use (sum-0-5 final-22))))

(local-defthmd final-36
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (infp (opa) (dp)))
		(not (infp (opbhi) (dp)))
		(= (+ (a) (b)) 0))
           (equal (d)
	          (mv-nth 0 (arm-binary-comp 'add (opad) (opbd) (rz) (dp)))))
  :hints (("Goal" :in-theory (enable rmode fpscr-rc binary-zero-sgn binary-eval final-21 final-22 final-14 final-33
                                     arm-binary-comp)
                  :use (final-34 final-35 sgnf-opad sgnf-opbd infp-opad infp-opbd))))

(local-defthmd final-36-a
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (and (infp (opa) (dp))
		          (infp (opbhi) (dp))
			  (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp))))))
		(or (infp (opa) (dp))
		    (infp (opbhi) (dp))
	    	    (= (+ (a) (b)) 0)))
          (equal (bitn (logior (flags) (rin)) 0)
	         (bitn (mv-nth 1 (arm-binary-comp 'add (opad) (opbd) (rin) (dp))) 0)))
  :hints (("Goal" :in-theory (enable rmode fpscr-rc binary-zero-sgn binary-eval final-21 final-22 final-14-a final-33
                                     final-24 bitn-logior arm-binary-comp)
                  :use (bvecp-rin final-34 final-35 sgnf-opad sgnf-opbd infp-opad infp-opbd))))

(local-defthmd denormp-lemma
  (implies (bvecp x 64)
           (iff (denormp x (dp))
	        (and (= (bits x 62 52) 0)
		     (not (= (bits x 51 0) 0)))))
  :hints (("Goal" :in-theory (enable dp denormp expf manf expw sigf encodingp))))

(local-defthmd bvecp-flags-3
  (bvecp (flags-3) 8)
  :hints (("Goal" :in-theory (enable flags-3 flags-2 flags-1 checkdenorm))))

(local-defthmd final-36-b
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (and (infp (opa) (dp))
		          (infp (opbhi) (dp))
			  (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp))))))
		(or (infp (opa) (dp))
		    (infp (opbhi) (dp))
	    	    (= (+ (a) (b)) 0))
		(natp k))
          (equal (bitn (logior (flags) (rin)) k)
	         (bitn (mv-nth 1 (arm-binary-comp 'add (opad) (opbd) (rz) (dp))) k)))
  :hints (("Goal" :in-theory (enable rmode fpscr-rc binary-zero-sgn binary-eval final-21 final-22 final-14-a final-33
                                     bvecp-opa opbhi denormp-lemma fzp rz flags-1 flags-3-rewrite final-24 bitn-logior arm-binary-comp)
                  :use (bvecp-flags-3 bvecp-rin final-34 final-35 sgnf-opad sgnf-opbd infp-opad infp-opbd))))

(local-defthm snanp-expf
  (implies (snanp x (dp))
           (equal (bits x 62 52) 2047))
  :hints (("Goal" :in-theory (enable dp snanp nanp expf expw manf))))

(local-defthm qnanp-expf
  (implies (qnanp x (dp))
           (equal (bits x 62 52) 2047))
  :hints (("Goal" :in-theory (enable dp qnanp nanp expf expw manf))))

(local-defthm infp-expf
  (implies (infp x (dp))
           (equal (bits x 62 52) 2047))
  :hints (("Goal" :in-theory (enable dp infp expf expw manf))))

(local-defthmd final-36-c
  (implies (and (specialp)
                (or (snanp (opa) (dp))
                    (snanp (opbhi) (dp))
		    (qnanp (opa) (dp))
                    (qnanp (opbhi) (dp))
		    (and (infp (opa) (dp))
		         (infp (opbhi) (dp))
			 (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp))))))
		(not (zp k))(not (= (hp) (dp)))(bvecp (opbhi) 64))
          (equal (bitn (logior (flags) (rin)) k)
	         (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) k)))
  :hints (("Goal" :in-theory (enable rmode fpscr-rc binary-zero-sgn binary-eval final-21 final-22 final-14-a final-33
                                     bvecp-opa denormp-lemma fzp rz flags-1 flags-3-rewrite final-24 bitn-logior
				     qnanp snanp binary-undefined-p bitn-bits bitn-cat arm-binary-spec)
                  :use (bvecp-flags-3 bvecp-rin final-34 final-35 sgnf-opad sgnf-opbd infp-opad infp-opbd))))

(local-defthmd final-36-d
  (implies (and (specialp)
                (or (snanp (opa) (dp))
                    (snanp (opbhi) (dp))
		    (qnanp (opa) (dp))
                    (qnanp (opbhi) (dp))
		    (and (infp (opa) (dp))
		         (infp (opbhi) (dp))
			 (not (= (sgnf (opa) (dp)) (sgnf (opbhi) (dp))))))
		(not (zp k)))
          (equal (bitn (logior (flags) (rin)) k)
	         (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) k)))
  :hints (("Goal" :in-theory (enable dp hp opbhi)
                  :use (final-36-c))))

(local-defthmd final-37
  (implies (and (specialp)
		(natp k))
          (equal (bitn (logior (flags) (rin)) k)
	         (bitn (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))) k)))
  :hints (("Goal" :use (final-17 final-18 final-19 final-20 final-28 final-29 final-32 final-36-b final-36-d)
                  :in-theory (e/d (qnanp snanp specialp) (arm-binary-spec arm-binary-comp)))))

(local-defthmd final-37-a
  (implies (specialp)
          (equal (logior (flags) (rin))
	         (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp)))))
  :hints (("Goal" :use (bvecp-r-spec bvecp-flags bvecp-rin
                        (:instance final-37 (k (bit-diff (logior (flags) (rin))
			                                 (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))))))
                        (:instance bit-diff-diff (x (logior (flags) (rin)))
                                                 (y (mv-nth 1 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp)))))))))

(local-defthmd final-38
  (implies (and (specialp)
                (not (snanp (opa) (dp)))
		(not (snanp (opbhi) (dp)))
		(not (qnanp (opa) (dp)))
		(not (qnanp (opbhi) (dp)))
		(not (infp (opa) (dp)))
		(not (infp (opbhi) (dp)))
		(= (+ (a) (b)) 0))
           (equal (d)
	          (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp)))))
  :hints (("Goal" :use (final-36 final-32))))


(local-defthmd final-39
  (implies (specialp)
           (equal (d)
	          (mv-nth 0 (arm-binary-spec 'add (opa) (opbhi) (rin) (dp)))))
  :hints (("Goal" :use (final-17 final-18 final-19 final-20 final-28 final-29 final-38)
                  :in-theory (enable snanp qnanp specialp))))

(local-defthm special-case
  (implies (specialp)
           (mv-let (d-spec r-spec) (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
             (and (equal (d) d-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :rule-classes ()
  :hints (("Goal" :use (final-39 final-37-a))))


;;*******************************************************************************
;; Final Result
;;*******************************************************************************

(local-defthm fadd-main
  (mv-let (d-spec r-spec) (arm-binary-spec 'add (opa) (opbhi) (rin) (dp))
    (and (equal (d) d-spec)
         (equal (logior (rin) (flags)) r-spec)))
  :rule-classes ()
  :hints (("Goal" :use (comp-case special-case))))

(local-defthm lemma-to-be-functionally-instantiated
  (mv-let (d flags) (fadd64 (opa) (opb) (bitn (rin) 24) (bitn (rin) 25) (bits (rin) 23 22)
                            (fma) (inz) (piz) (expovfl) (mulexcps))
    (mv-let (d-spec r-spec) (arm-binary-spec 'add (opa) (bits (opb) 116 53) (rin) (dp))
      (and (equal d d-spec)
           (equal (logior (rin) flags) r-spec))))
  :rule-classes ()
  :hints (("Goal" :use (fadd-main)
                  :in-theory (e/d (equivalence-lemma opbhi) (arm-binary-spec)))))

(local (defmacro ic ()
  '(fadd-constraints opa opb rin fma inz piz expovfl mulexcps)))

(local-defthm fadd64-fadd
  (implies (fadd-constraints opa opb rin fma inz piz expovfl mulexcps)
           (let ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22)) (opbhi (bits opb 116 53)))
             (mv-let (d flags) (fadd64 opa opb fz dn rmode fma inz piz expovfl mulexcps)
               (mv-let (d-spec r-spec) (arm-binary-spec 'add opa opbhi rin (dp))
                 (and (equal d d-spec)
                      (equal (logior rin flags) r-spec))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (opb (lambda () (if (ic) opb (opb))))
                         (rin (lambda () (if (ic) rin (rin))))
                         (fma (lambda () (if (ic) fma (fma))))
                         (inz (lambda () (if (ic) inz (inz))))
                         (piz (lambda () (if (ic) piz (piz))))
                         (expovfl (lambda () (if (ic) expovfl (expovfl))))
                         (mulexcps (lambda () (if (ic) mulexcps (mulexcps)))))))
           ("Subgoal 1" :use (fadd-constraints-lemma))))

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
  :rule-classes ()
  :hints (("Goal" :use (fadd64-fadd) :in-theory (enable fadd-constraints))))

