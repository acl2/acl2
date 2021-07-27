(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)

(include-book "idiv8")

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

;; In terms of these constants, we shall define constants corresponding to the local 
;; variables of idiv8, culminating in the constant (data), corresponding to
;; the output.

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

;; In this book, we'll define the constants and prove the above idiv8-lemma.

;;*******************************************************************************
;; idiv8
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

;; It's usually a good idea to disable the executable counterpart of any function that depends
;; on a constrained function:

(in-theory (disable (input-constraints) (mska) (mskb) (sgna) (sgnb) (sgnq) (nega) (negb) (absa) (absb) (bgta) (clza) (clzb)
                    (del) (bitsmod6) (c) (only1iter) (skipiter) (k) (div) (div2) (div3) (cmpconst) (rp-1) (rn-1) (rs10-0)
		    (rs10-1) (gep2) (q-1) (quot-1) (quotm-1) (rpf) (rnf) (quotf) (quotmf) (quotpf) (islost) (quot0) (quotm0)
		    (quotp0) (rdiff) (data)))

;; Let's also disable all the functions defined by the model and enable them only as needed:

(in-theory (disable clz64-loop-0 clz64-loop-1 clz64-loop-2 clz64 ispow2-loop-0 ispow2-loop-1 ispow2-loop-2 ispow2 divpow2
                    compareops computecmpconst nextdigit nextrem nextquot incquot computers11 computers10 idiv8-loop-0
		    idiv8-loop-1 idiv8 (clz64-loop-0) (clz64-loop-1) (clz64-loop-2) (clz64) (ispow2-loop-0) (ispow2-loop-1)
		    (ispow2-loop-2) (ispow2) (divpow2) (compareops) (computecmpconst) (nextdigit) (nextrem) (nextquot) (incquot)
		    (computers11) (computers10) (idiv8-loop-0) (idiv8-loop-1) (IDIV8)))
