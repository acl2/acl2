;; Cuong Chau <cuong.chau@arm.com>

;; June 2021

(in-package "RTL")

(include-book "fdiv2")
(include-book "projects/arm/utils/rtl-utils" :dir :system)
(include-book "projects/rac/lisp/internal-fns-gen" :dir :system)

;; ======================================================================

;; We impose the following constraints on the inputs of fdivlane:

(defund input-constraints (opa opb fnum vec rin)
  (and (bvecp opa 64)
       (bvecp opb 64)
       (member fnum '(1 2 3))
       (bitp vec)
       (natp rin)))

;; Our ultimate objective is the following theorem:

;; (defthm fdivlane-correct
;;   (implies (input-constraints opa opb fnum vec rin)
;;            (let* ((f (case fnum (1 (hp)) (2 (sp)) (3 (dp))))
;;                   (fmtw (+ 1 (expw f) (sigw f)))
;;                   (fzp (bitn rin 24))
;;                   (dnp (bitn rin 25))
;;                   (rmode (bits rin 23 22)))
;;              (mv-let (data flags) (fdivlane opa opb fnum vec fzp dnp rmode)
;;                (mv-let
;;                  (data-spec r-spec)
;;                  (arm-binary-spec 'div
;;                                   (bits opa (1- fmtw) 0)
;;                                   (bits opb (1- fmtw) 0)
;;                                   rin
;;                                   f)
;;                  (and (equal data data-spec)
;;                       (equal (logior rin flags) r-spec)))))))

;; In order to address the lack of modularity of the ACL2 code, we take the
;; following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate
  (((opa) => *)
   ((opb) => *)
   ((fnum) => *)
   ((vec) => *)
   ((rin) => *))

  (local (defun opa () 0))
  (local (defun opb () 0))
  (local (defun fnum () 1))
  (local (defun vec () 0))
  (local (defun rin () 0))

  (defthm input-constraints-lemma
    (input-constraints (opa) (opb) (fnum) (vec) (rin))))

(local (in-theory (disable input-constraints-lemma)))

(bvecthm bvecp64-opa
  (bvecp (opa) 64)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(bvecthm bvecp64-opb
  (bvecp (opb) 64)
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(defthm fnum-vals
  (and (posp (fnum))
       (<= (fnum) 3))
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints)))
  :rule-classes ((:type-prescription :corollary (natp (fnum)))
                 (:linear :corollary (and (<= 1 (fnum))
                                          (<= (fnum) 3)))))

(bitthm bitp-vec
  (bitp (vec))
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints))))

(defthm natp-rin
  (natp (rin))
  :hints (("Goal"
           :use input-constraints-lemma
           :in-theory (enable input-constraints)))
  :rule-classes :type-prescription)

(defundd f ()
  (case (fnum)
    (1 (hp))
    (2 (sp))
    (3 (dp))))

(defthm formatp-f
  (formatp (f))
  :hints (("Goal" :in-theory (enable f))))

(defthm expw-f-domain
  (and (natp (expw (f)))
       (<= 5 (expw (f)))
       (<= (expw (f)) 11))
  :hints (("Goal" :in-theory (enable f)))
  :rule-classes ((:type-prescription :corollary (natp (expw (f))))
                 (:linear :corollary (and (<= 5 (expw (f)))
                                          (<= (expw (f)) 11)))))

(defthm sigw-f-domain
  (and (natp (sigw (f)))
       (<= 10 (sigw (f)))
       (<= (sigw (f)) 52))
  :hints (("Goal" :in-theory (enable f)))
  :rule-classes ((:type-prescription :corollary (natp (sigw (f))))
                 (:linear :corollary (and (<= 10 (sigw (f)))
                                          (<= (sigw (f)) 52)))))

(defthm prec-f-domain
  (and (natp (prec (f)))
       (<= 11 (prec (f)))
       (<= (prec (f)) 53))
  :hints (("Goal" :in-theory (enable f)))
  :rule-classes ((:type-prescription :corollary (natp (prec (f))))
                 (:linear :corollary (and (<= 11 (prec (f)))
                                          (<= (prec (f)) 53)))))

(defundd fzp () (bitn (rin) 24))

(bitthm bitp-fzp
  (bitp (fzp))
  :hints (("Goal" :in-theory (enable fzp))))

(defundd dnp () (bitn (rin) 25))

(bitthm bitp-dnp
  (bitp (dnp))
  :hints (("Goal" :in-theory (enable dnp))))

(defundd rmode () (bits (rin) 23 22))

(bvecthm bvecp2-rmode
  (bvecp (rmode) 2)
  :hints (("Goal" :in-theory (enable rmode))))

;; In terms of these constants, we shall define constants corresponding to the
;; local variables of fdivlane, culminating in the constant (result)
;; corresponding to the outputs.

;; The constant definitions will be derived from that of fdivlane in such a way
;; that the proof of the following will be trivial:

;; (defthm fdivlane-lemma
;;   (equal (result)
;;          (fdivlane (opa) (opb) (fnum) (vec) (fzp) (dnp) (rmode))))

;; (defundd data ()
;;   (mv-nth 0 (mv-list 2 (result))))

;; (defundd flags ()
;;   (mv-nth 1 (mv-list 2 (result))))

;; The real work will be the proof of the following theorem:

;; (defthm fdivlane-main
;;   (let ((fmtw (+ 1 (expw (f)) (sigw (f)))))
;;     (mv-let
;;       (data-spec r-spec)
;;       (arm-binary-spec 'div
;;                        (bits (opa) (1- fmtw) 0)
;;                        (bits (opb) (1- fmtw) 0)
;;                        (rin)
;;                        (f))
;;       (and (equal (data) data-spec)
;;            (equal (logior (rin) (flags)) r-spec)))))

;; The following is an immediate consequence of the four preceding events:

;; (defthm fdivlane-main-inst
;;   (let* ((f (case fnum (1 (hp)) (2 (sp)) (3 (dp))))
;;          (fmtw (+ 1 (expw f) (sigw f)))
;;          (fzp (bitn (rin) 24))
;;          (dnp (bitn (rin) 25))
;;          (rmode (bits (rin) 23 22)))
;;     (mv-let (data flags) (fdivlane (opa) (opb) (fnum) (vec) fzp dnp rmode)
;;       (mv-let
;;         (data-spec r-spec)
;;         (arm-binary-spec 'div
;;                          (bits (opa) (1- fmtw) 0)
;;                          (bits (opb) (1- fmtw) 0)
;;                          (rin)
;;                          f)
;;         (and (equal data data-spec)
;;              (equal (logior (rin) flags) r-spec))))))

;; The desired theorem can then be derived by functional instantiation.

;; ======================================================================

;; In this book, we'll define the constants and prove the above fdivlane-lemma
;; using the CONST-FNS-GEN utility.

;; For some reason, it takes a lot of time to prove fdivlane-lemma when
;; applying CONST-FNS-GEN to function fdivlane. To overcome this, we split the
;; definition of fdivlane into two functions and apply CONST-FNS-GEN to each of
;; them.

(encapsulate
  ()

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (defund fdivlane-segment (opa opb fmt vec fz)
    (let ((signa 0)
          (signb 0)
          (expa 0)
          (expb 0)
          (mana 0)
          (manb 0)
          (classa 0)
          (classb 0)
          (flags (bits 0 7 0)))
      (mv-let
        (signa expa mana classa flags)
        (analyze opa fmt fz flags)
        (mv-let
          (signb expb manb classb flags)
          (analyze opb fmt fz flags)
          (let ((sign (logxor signa signb)))
            (let ((x 0) (d 0) (expq 0))
              (mv-let
                (x d expq)
                (normalize expa expb mana manb fmt)
                (let* ((x57 (bits 0 56 0))
                       (d57 (bits 0 56 0))
                       (x57 (setbits x57 57 55 3 x))
                       (d57 (setbits d57 57 55 3 d))
                       (qtrunc 0)
                       (stk 0))
                  (mv-let
                    (qtrunc stk)
                    (if1
                     (log= manb 0)
                     (mv (bits (ash x 2) 54 0) 0)
                     (let* ((rs (bits 0 56 0))
                            (rc (bits 0 56 0))
                            (fmtrem (bits (if1 vec fmt 3) 1 0))
                            (quot (bits 0 54 0))
                            (quotm1 (bits 0 54 0))
                            (q 0)
                            (c 0)
                            (c (case fmt (3 18) (2 9) (1 4) (t c)))
                            (n (+ (* 3 c) 1))
                            (rs x57)
                            (rc d57)
                            (rc (bits (lognot rc) 56 0)))
                       (mv-let
                         (rc rs)
                         (case fmtrem
                           (3 (mv (setbits rc 57 1 0 0)
                                  (setbitn rs 57 2 1)))
                           (2 (mv (setbits rc 57 30 0 0)
                                  (setbitn rs 57 31 1)))
                           (1 (mv (setbits rc 57 43 0 0)
                                  (setbitn rs 57 44 1)))
                           (t (mv rc rs)))
                         (let ((quot (setbitn quot 55 54 1)))
                           (mv-let
                             (q rs rc quot quotm1)
                             (fdivlane-loop-0
                              2 n d57 fmtrem q rs rc quot quotm1)
                             (let* ((rfinal (bits (+ rs rc) 56 0))
                                    (rsign (log< (si rfinal 57) 0))
                                    (rnonzero (log<> (si rfinal 57) 0))
                                    (qtrunc (bits (if1 rsign quotm1 quot) 54 0))
                                    (rplusds (logxor (logxor rs rc) d57))
                                    (rplusdc
                                     (bits
                                      (ash
                                       (logior
                                        (logior (logand rs rc) (logand rs d57))
                                        (logand rc d57))
                                       1)
                                      56 0))
                                    (rplusdxor (logxor rplusds rplusdc))
                                    (rplusdor
                                     (bits (ash (logior rplusds rplusdc) 1)
                                           56 0))
                                    (rplusdis0 (log= rplusdxor rplusdor))
                                    (assert
                                     (in-function
                                      fdivlane
                                      (log= rplusdis0
                                            (log= (+ (si rfinal 57) d57) 0)))))
                               (mv
                                qtrunc
                                (logand1 rnonzero (lognot1 rplusdis0)))))))))
                    (mv-let
                      (expq stk qtrunc)
                      (if1
                       (log<= (si expq 13) 0)
                       (let ((shft (bits (- 1 (si expq 13)) 12 0)))
                         (mv
                          expq
                          (logior
                           stk
                           (logior1
                            (log>= shft 55)
                            (log<> (logand qtrunc (- (ash 1 shft) 1))
                                   0)))
                          (bits (ash qtrunc (- shft)) 54 0)))
                       (mv-let
                         (expq qtrunc)
                         (if1 (lognot1 (bitn qtrunc 54))
                              (let ((expq1 (bits (- (si expq 13) 1) 12 0)))
                                (mv expq1
                                    (if1 (log> (si expq1 13) 0)
                                         (bits (ash qtrunc 1) 54 0)
                                         qtrunc)))
                              (mv expq qtrunc))
                         (mv expq stk qtrunc)))
                      (mv expq stk qtrunc flags)))))))))))

  (defund fdivlane-alt (opa opb fmt vec fz dn rmode)
    (let ((signa 0)
          (signb 0)
          (expa 0)
          (expb 0)
          (mana 0)
          (manb 0)
          (classa 0)
          (classb 0)
          (flags (bits 0 7 0)))
      (mv-let
        (signa expa mana classa flags)
        (analyze opa fmt fz flags)
        (mv-let
          (signb expb manb classb flags)
          (analyze opb fmt fz flags)
          (let ((sign (logxor signa signb)))
            (if1
             (logior1
              (logior1
               (logior1
                (logior1 (logior1 (logior1 (logior1 (log= classa 0)
                                                    (log= classa 1))
                                           (log= classa 2))
                                  (log= classa 3))
                         (log= classb 0))
                (log= classb 1))
               (log= classb 2))
              (log= classb 3))
             (specialcase sign opa opb classa classb fmt dn flags)
             (mv-let
               (expq stk qtrunc flags)
               (fdivlane-segment opa opb fmt vec fz)
               (mv-let
                 (stk qtrunc)
                 (case fmt
                   (2 (mv (logior stk (log<> (bits qtrunc 28 0) 0))
                          (bits (ash qtrunc (- 29)) 54 0)))
                   (1 (mv (logior stk (log<> (bits qtrunc 41 0) 0))
                          (bits (ash qtrunc (- 42)) 54 0)))
                   (t (mv stk qtrunc)))
                 (let* ((lsb (bitn qtrunc 2))
                        (grd (bitn qtrunc 1))
                        (stk (logior stk (bitn qtrunc 0)))
                        (inx (logior1 grd stk))
                        (qrnd 0)
                        (qrnd
                         (if1
                          (logior1
                           (logior1
                            (logand1 (logand1 (log= rmode 0) grd)
                                     (logior1 lsb stk))
                            (logand1
                             (logand1 (log= rmode 1) (lognot1 sign))
                             (logior1 grd stk)))
                           (logand1 (logand1 (log= rmode 2) sign)
                                    (logior1 grd stk)))
                          (bits (+ (bits qtrunc 54 2) 1) 52 0)
                          (bits qtrunc 54 2))))
                   (final qrnd inx sign
                          expq rmode fz fmt flags))))))))))

  (defthm fdivlane-alt-=-fdivlane
    (equal (fdivlane-alt opa opb fmt vec fz dn rmode)
           (fdivlane     opa opb fmt vec fz dn rmode))
    :hints (("Goal" :in-theory '(fdivlane-alt fdivlane fdivlane-segment))))
  )

(make-event
 `,(const-fns-gen 'fdivlane-segment 'fdivlane-segment-result state
                  :sub-pairs '((fmt fnum)
                               (fz fzp)
                               (flags-1 flags-a)
                               (flags flags-b-segment)
                               (x siga)
                               (d sigb)
                               (rs-2 rs-0)
                               (rc-3 rc-0)
                               (expq expq-segment)
                               (stk stk-segment)
                               (qtrunc qtrunc-segment)
                               (rs rsf)
                               (rc rcf)
                               (quot quotf)
                               (quotm1 quotm1f)
                               (shft--0 shft))
                  :excluded-vars '(expq1--0
                                   rc-2
                                   qtrunc-1
                                   stk-1
                                   expq++1
                                   qtrunc++1)))

(local
 (defthm fdivlane-alt-lemma-aux
   (equal (mv-nth 3 (fdivlane-segment (opa)
                                      (opb)
                                      (fnum)
                                      (vec)
                                      (fzp)))
          (mv-nth 4 (analyze (opb)
                             (fnum)
                             (fzp)
                             (mv-nth 4
                                     (analyze (opa)
                                              (fnum)
                                              (fzp)
                                              (bits 0 7 0))))))
   :hints (("Goal" :in-theory '(fdivlane-segment)))))

(make-event
 `,(const-fns-gen 'fdivlane-alt 'result state
                  :sub-pairs '((fmt fnum)
                               (fz fzp)
                               (dn dnp)
                               (flags flags-b))
                  :excluded-vars '(flags-1 stk-1)
                  :rules '(fdivlane-alt-lemma-aux)))

(defthmd fdivlane-lemma
  (equal (result)
         (fdivlane (opa) (opb) (fnum) (vec) (fzp) (dnp) (rmode)))
  :hints (("Goal" :in-theory (enable fdivlane-alt-lemma))))

(defthmd fdivlane-segment-result-expand
  (and (equal (expq) (expq-segment))
       (equal (stk-0) (stk-segment))
       (equal (qtrunc-0) (qtrunc-segment))
       (equal (flags-b) (flags-b-segment)))
  :hints (("Goal"
           :use fdivlane-segment-lemma
           :in-theory '(expq stk-0 qtrunc-0 flags-b
                             fdivlane-segment-result))))

(defundd data ()
  (mv-nth 0 (mv-list 2 (result))))

(defundd flags ()
  (mv-nth 1 (mv-list 2 (result))))

(make-event
 `,(const-fns-gen 'normalize 'normalize-result state
                  :sub-pairs '((fmt fnum)
                               (siga nsiga)
                               (sigb nsigb)
                               (bias bs))
                  :excluded-vars '(clz--0-0 clz--0)))

(defthm n-bounds
  (and (<= 13 (n))
       (<= (n) 55))
  :hints (("Goal" :in-theory (enable n c)))
  :rule-classes :linear)

;; We define the sequences of values (q j), (rs57 j), (rc57 j), (quot j), and
;; (quotm1 j) as a set of mutually recursive functions, as they are computed by
;; fdivlane-loop-1. These functions are mechanically generated by applying the
;; LOOP-FNS-GEN utility. We also prove that the constants (rsf), etc., are
;; related to these functions as follows:

;; (equal (rsf) (rs57 (n)))
;; (equal (rcf) (rc57 (n)))
;; (equal (quotf) (quot (n)))
;; (equal (quotm1f) (quotm1 (n)))

(make-event
 `(progn
    ,@(loop-fns-gen 'fdivlane-loop-0 state
                    :base-cond '(or (zp i) (= i 1))
                    :init-alist '((q 1)
                                  (rs57 (rs-0))
                                  (rc57 (rc-0))
                                  (quot *2^54*)
                                  (quotm1 0))
                    :sub-pairs '(((i) . i)
                                 (rs rs57)
                                 (rc rc57)))))

(local
 (defthmd fdivlane-loop-0-lemma-1
   (implies (and (natp i)
                 (<= 2 i)
                 (<= i (1+ (n))))
            (equal (fdivlane-loop-0 i (n)
                                    (d57)
                                    (fmtrem)
                                    (q (1- i))
                                    (rs57 (1- i))
                                    (rc57 (1- i))
                                    (quot (1- i))
                                    (quotm1 (1- i)))
                   (list (q (n))
                         (rs57 (n))
                         (rc57 (n))
                         (quot (n))
                         (quotm1 (n)))))
   :hints (("Goal" :in-theory (enable fdivlane-loop-0
                                      fdivlane-loop-0-all-fns)))))

(local
 (defthm fdivlane-loop-0-lemma-2
   (equal (fdivlane-loop-0 2 (n)
                           (d57)
                           (fmtrem)
                           0
                           (rs-0)
                           (rc-0)
                           *2^54*
                           0)
          (fdivlane-loop-0 2 (n)
                           (d57)
                           (fmtrem)
                           1
                           (rs-0)
                           (rc-0)
                           *2^54*
                           0))
   :hints (("Goal" :expand ((:free (n) (fdivlane-loop-0 2 n
                                                        (d57)
                                                        (fmtrem)
                                                        0
                                                        (rs-0)
                                                        (rc-0)
                                                        *2^54*
                                                        0))
                            (:free (n) (fdivlane-loop-0 2 n
                                                        (d57)
                                                        (fmtrem)
                                                        1
                                                        (rs-0)
                                                        (rc-0)
                                                        *2^54*
                                                        0)))))))

(local
 (defthm fdivlane-loop-0-lemma-3
   (equal (fdivlane-loop-0 2 (n)
                           (d57)
                           (fmtrem)
                           0
                           (rs-0)
                           (rc-0)
                           *2^54*
                           0)
          (list (q (n))
                (rs57 (n))
                (rc57 (n))
                (quot (n))
                (quotm1 (n))))
   :hints (("Goal"
            :in-theory (enable fdivlane-loop-0-all-fns)
            :use (:instance fdivlane-loop-0-lemma-1 (i 2))))))

(defthmd rsf-rewrite
  (equal (rsf) (rs57 (n)))
  :hints (("Goal" :in-theory (enable rsf))))

(defthmd rcf-rewrite
  (equal (rcf) (rc57 (n)))
  :hints (("Goal" :in-theory (enable rcf))))

(defthmd quotf-rewrite
  (equal (quotf) (quot (n)))
  :hints (("Goal" :in-theory (enable quotf))))

(defthmd quotm1f-rewrite
  (equal (quotm1f) (quotm1 (n)))
  :hints (("Goal" :in-theory (enable quotm1f))))
