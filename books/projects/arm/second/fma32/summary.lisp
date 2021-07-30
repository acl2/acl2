;; Cuong Chau <cuong.chau@arm.com>

;; July 2021

(in-package "RTL")

(include-book "final")

;; ======================================================================

;; We impose the following constraints on the inputs of fma32:

(defund input-constraints (a b c d rmode scaleop)
  (and (bvecp a 32)
       (bvecp b 32)
       (bvecp c 32)
       (bvecp d 32)
       (natp rmode)
       (<= rmode 5)
       (bitp scaleop)))

;; Our ultimate objective is the following theorem:

;; (defthm fma32-correct
;;   (implies (input-constraints a b c d rmode scaleop)
;;            (equal (fma32      a b c d rmode scaleop)
;;                   (fma32-spec a b c d rmode scaleop))))

;; In order to address the lack of modularity of the ACL2 code, we take the
;; following approach.

;; First, we introduce constrained constants representing the inputs:

(encapsulate
  (((a) => *)
   ((b) => *)
   ((c) => *)
   ((d) => *)
   ((rmode) => *)
   ((scaleop) => *))

  (local (defun a () 0))
  (local (defun b () 0))
  (local (defun c () 0))
  (local (defun d () 0))
  (local (defun rmode () 0))
  (local (defun scaleop () 0))

  (defthm input-constraints-lemma
    (input-constraints (a) (b) (c) (d) (rmode) (scaleop))))

;; In terms of these constants, we shall define constants corresponding to the
;; local variables of fma32, culminating in the constant (data) corresponding
;; to the output. This can be done mechanically by applying the CONST-FNS-GEN
;; utility. See prelim.lisp for the details.

;; The constant definitions will be derived from that of fma32 in such a way
;; that the proof of the following will be trivial:

(defthmd fma32-lemma
  (equal (data)
         (fma32 (a) (b) (c) (d) (rmode) (scaleop))))

;; The real work will be the proof of the following theorem:

;; (defthm fma32-main
;;   (equal (fma32      (a) (b) (c) (d) (rmode) (scaleop))
;;          (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))

;; The desired theorem can then be derived by functional instantiation.

;; ======================================================================

;; Prove correctness for special inputs

(defundd numeric-a-b-p ()
  (and (equal (anan) 0)
       (equal (ainf) 0)
       (equal (bnan) 0)
       (equal (binf) 0)))

(defundd numeric-c-p ()
  (and (equal (cnan) 0)
       (equal (cinf) 0)))

(defundd not-both-p&c-zeros-p ()
  (or (equal (pzero) 0)
      (equal (czero) 0)))

(defthmd fma32-main-special
  (implies (or (not (numeric-a-b-p))
               (not (numeric-c-p))
               (not (not-both-p&c-zeros-p)))
           (equal (data)
                  (fma32-spec (a) (b) (c) (d) (rmode) (scaleop)))))

;; ======================================================================

;; Analyze addends

(defundd p ()
  (* (decode (a) (sp))
     (decode (b) (sp))))

(defundd cval ()
  (decode (c) (sp)))

(defundd s ()
  (if (equal (scaleop) 0)
      (+ (p) (cval))
    (* (expt 2 (si (d) 32))
       (+ (p) (cval)))))

(defundd p-tilde ()
  (* (if (equal (psign) 0) 1 -1)
     (expt 2 (- (pexp) 302))
     (pmant)))

(defundd c-tilde ()
  (* (if (equal (csign) 0) 1 -1)
     (expt 2 (- (cexp) 302))
     (cmant)))

(defundd s-tilde ()
  (* (expt 2 (si (scale) 10))
     (+ (p-tilde) (c-tilde))))

(defundd adj-cond-p ()
  (and (equal (scaleop) 1)
       (<= 16 (si (d) 32))
       (not (equal (p) 0))
       (equal (cdenorm) 1)
       (<= 64 (abexp))
       (< (abexp) 256)))

(defthmd c-tilde-cval-rel-1
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (equal (c-tilde)
                  (* (expt 2 128) (cval)))))

(defthmd c-tilde-cval-rel-2
  (implies (not (adj-cond-p))
           (equal (c-tilde) (cval))))

(defthmd s-s-tilde-rel-1
  (implies (numeric-a-b-p)
           (equal (equal (s-tilde) 0)
                  (equal (s) 0))))

(defthmd s-s-tilde-rel-2
  (implies (numeric-a-b-p)
           (equal (< 0 (s-tilde))
                  (< 0 (s)))))

(defthm s-s-tilde-rel-3
  (implies (and (numeric-a-b-p)
                (equal (scaleop) 1)
                (< (si (d) 32) -512))
           (<= (abs (s))
               (abs (s-tilde))))
  :rule-classes :linear)

(defthmd s-tilde-=-s-1
  (implies (and (numeric-a-b-p)
                (or (equal (scaleop) 0)
                    (and (<= -512 (si (d) 32))
                         (<= (si (d) 32) 511))))
           (equal (s-tilde) (s))))

(defundd elarge ()
  (if (equal (clarger) 0)
      (pexp)
    (cexp)))

(defundd esmall ()
  (if (equal (clarger) 0)
      (cexp)
    (pexp)))

(defundd mlarge ()
  (if (equal (clarger) 0)
      (pmant)
    (cmant)))

(defundd msmall ()
  (if (equal (clarger) 0)
      (cmant)
    (pmant)))

(defundd ediff ()
  (- (elarge) (esmall)))

(defundd fi ()
  (if (equal (sub) 0)
      (* 4 (+ (mlarge)
              (* (msmall) (expt 2 (- (ediff))))))
    (abs (* 4 (- (mlarge)
                 (* (msmall) (expt 2 (- (ediff)))))))))

(defthmd add1-rewrite
  (implies (numeric-a-b-p)
           (equal (add1)
                  (+ (expt 2 51)
                     (fl (* (msmall)
                            (expt 2 (- 2 (ediff)))))))))

(defthmd inx-0
  (implies (numeric-a-b-p)
           (equal (equal (inx) 0)
                  (integerp (* (msmall)
                               (expt 2 (- 2 (ediff))))))))

(defthmd add2-rewrite
  (equal (add2)
         (if (equal (sub) 0)
             (+ (expt 2 51)
                (* 4 (mlarge)))
           (+ (expt 2 51)
              (- (* 4 (mlarge)))
              -1))))

(defthmd s-tilde-rewrite
  (implies (numeric-a-b-p)
           (equal (s-tilde)
                  (if (equal (sub) 0)
                      (* (if (equal (signlarger) 0) 1 -1)
                         (expt 2 (+ (si (scale) 10)
                                    (elarge)
                                    -302))
                         (+ (mlarge)
                            (* (msmall)
                               (expt 2 (- (ediff))))))
                    (* (if (equal (signlarger) 0) 1 -1)
                       (expt 2 (+ (si (scale) 10)
                                  (elarge)
                                  -302))
                       (- (mlarge)
                          (* (msmall)
                             (expt 2 (- (ediff))))))))))

(defthmd abs-s-tilde-rewrite-1
  (implies (numeric-a-b-p)
           (equal (abs (s-tilde))
                  (* (fi)
                     (expt 2 (+ (si (scale) 10) (elarge) -304))))))

;; ======================================================================

;; Analyze sum

(defthmd sum-fi-rel
  (implies (and (numeric-a-b-p)
                (equal (severe) 0))
           (equal (sum) (fl (fi)))))

(defthmd sumexp-rewrite
  (implies (numeric-a-b-p)
           (equal (sumexp)
                  (+ (si (scale) 10)
                     (elarge)
                     794))))

(defthmd abs-s-tilde-rewrite-2
  (implies (numeric-a-b-p)
           (equal (abs (s-tilde))
                  (* (fi)
                     (expt 2 (- (sumexp) 1098))))))

(defthm s-tilde-sum-rel
  (implies (and (numeric-a-b-p)
                (equal (severe) 0))
           (and (<= (* (sum)
                       (expt 2 (- (sumexp) 1098)))
                    (abs (s-tilde)))
                (< (abs (s-tilde))
                   (* (1+ (sum))
                      (expt 2 (- (sumexp) 1098))))))
  :rule-classes :linear)

(defthmd s-tilde-sum-inx-rel
  (implies (and (numeric-a-b-p)
                (equal (severe) 0))
           (equal (equal (inx) 0)
                  (equal (* (sum)
                            (expt 2 (- (sumexp) 1098)))
                         (abs (s-tilde))))))

;; ======================================================================

;; Analyze sumshft

(defundd sumshft-prime ()
  (* (sum) (expt 2 (clzprime))))

(defundd sig&grd ()
  (if (equal (overshft) 0)
      (bits (sumshft) 76 52)
    (bits (sumshft) 77 53)))

(defundd omega ()
  (+ (sumexp) (- (clzprime)) 1))

(defthmd grd-sumshft-prime-rel
  (equal (grd)
         (bitn (sumshft-prime) 52)))

(defthmd grd-sig&grd-rel
  (equal (grd)
         (bitn (sig&grd) 0)))

(defthmd stk-0
  (equal (equal (stk) 0)
         (and (equal (inx)
                     (bits (sumshft-prime) 51 0))
              (equal (inx) 0))))

(defthmd s-tilde-sig&grd-stk-rel
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (equal (stk) 0)
                  (equal (* (sig&grd) (expt 2 (- (omega) 1047)))
                         (abs (s-tilde))))))

(defthmd s-tilde-=-s-2
  (implies (and (<= 1 (sig&grd))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (s-tilde) (s))))

;; ======================================================================

;; Rounding

;; Normal rounding

(defthmd resrnd-rnd-ext-s-rel-2
  (implies (and (<= (abs (rnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  24))
                    (lpn (sp)))
                (<= (spn (sp)) (abs (s)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (nencode (rnd-ext (s)
                                    (decode-fma-rmode (rmode))
                                    24)
                           (sp)))))

(defthmd resrnd-rnd-ext-s-rel-3
  (implies (and (< (lpn (sp))
                   (abs (rnd-ext (s)
                                 (decode-fma-rmode (rmode))
                                 24)))
                (<= (spn (sp)) (abs (s)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (and (equal (resrnd)
                       (iencode (ressign) (sp)))
                (or (and (equal (rmode) 0)
                         (equal (ressign) 0))
                    (and (equal (rmode) 1)
                         (equal (ressign) 1))
                    (equal (rmode) 3)
                    (equal (rmode) 4)
                    (equal (rmode) 5)))))

;; Subnormal rounding

(defthmd resrnd-drnd-ext-s-rel-5
  (implies (and (equal (drnd-ext (s)
                                 (decode-fma-rmode (rmode))
                                 (sp))
                       0)
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (zencode (ressign) (sp)))))

(defthmd resrnd-drnd-ext-s-rel-6
  (implies (and (not (equal (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp))
                            0))
                (< (abs (drnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  (sp)))
                   (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (dencode (drnd-ext (s)
                                     (decode-fma-rmode (rmode))
                                     (sp))
                           (sp)))))

(defthmd resrnd-drnd-ext-s-rel-7
  (implies (and (equal (abs (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp)))
                       (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (nencode (drnd-ext (s)
                                     (decode-fma-rmode (rmode))
                                     (sp))
                           (sp)))))

;; ======================================================================

;; The main lemma

(defthmd fma32-main
  (equal (fma32      (a) (b) (c) (d) (rmode) (scaleop))
         (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))

;; The final theorem

(defthmd fma32-correct
  (implies (input-constraints a b c d rmode scaleop)
           (equal (fma32      a b c d rmode scaleop)
                  (fma32-spec a b c d rmode scaleop))))
