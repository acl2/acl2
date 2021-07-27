;; Cuong Chau <cuong.chau@arm.com>

;; May 2021

(in-package "RTL")

(include-book "final")

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

(defundd fzp () (bitn (rin) 24))

(defundd dnp () (bitn (rin) 25))

(defundd rmode () (bits (rin) 23 22))

(defundd f ()
  (case (fnum)
    (1 (hp))
    (2 (sp))
    (3 (dp))))

;; In terms of these constants, we shall define constants corresponding to the
;; local variables of fdivlane, culminating in the constant (result)
;; corresponding to the outputs. This can be done mechanically by applying the
;; CONST-FNS-GEN utility. See prelim.lisp for the details.

;; The constant definitions will be derived from that of fdivlane in such a way
;; that the proof of the following will be trivial:

(defthmd fdivlane-lemma
  (equal (result)
         (fdivlane (opa) (opb) (fnum) (vec) (fzp) (dnp) (rmode))))

(defundd data ()
  (mv-nth 0 (mv-list 2 (result))))

(defundd flags ()
  (mv-nth 1 (mv-list 2 (result))))

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

;; Prove correctness for special inputs

(defundd specialp ()
  (or (member (classa) '(0 1 2 3))
      (member (classb) '(0 1 2 3))))

(defundd fmtw () (+ 1 (expw (f)) (sigw (f))))

(defundd opaw () (bits (opa) (1- (fmtw)) 0))

(defundd opbw () (bits (opb) (1- (fmtw)) 0))

(defundd opaz ()
  (if (and (= (fzp) 1)
           (denormp (opaw) (f)))
      (zencode (sgnf (opaw) (f)) (f))
     (opaw)))

(defundd opbz ()
  (if (and (= (fzp) 1)
           (denormp (opbw) (f)))
      (zencode (sgnf (opbw) (f)) (f))
    (opbw)))

(defthmd fdivlane-special-correct
  (mv-let
    (data-spec r-spec)
    (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
    (implies (specialp)
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec)))))

;; ======================================================================

;; Analyze function NORMALIZE

(defundd a () (decode (opaw) (f)))

(defundd b () (decode (opbw) (f)))

(defthmd quotient-formula
  (implies (not (specialp))
           (equal (abs (/ (a) (b)))
	          (* (expt 2 (- (si (expq-1) 13) (bias (f))))
		     (/ (siga) (sigb))))))

;; Define the normalized dividend x and normalized divisor d satisfying
;; 1 <= x < 2 and 1 <= d < 2.

(defundd x () (sig (a)))

(defundd d () (sig (b)))

(defthmd x57-rewrite
  (implies (not (specialp))
           (equal (x57)
                  (* *2^55* (x)))))

(defthmd d57-rewrite
  (implies (not (specialp))
           (equal (d57) (* *2^55* (d)))))

;; Partial quotients

(defundd quotient (i)
  (if (zp i)
      0
    (+ (quotient (1- i))
       (* (expt 2 (- 1 i)) (q i)))))

;; Partial remainders

(defundd rmd (i)
  (* (expt 2 (1- i))
     (- (x) (* (d) (quotient i)))))

(defthmd rmd-recurrence
  (implies (posp j)
           (equal (rmd j)
                  (- (* 2 (rmd (1- j)))
                     (* (q j) (d))))))

;; ======================================================================

;; Establish the relationship between the partial remainder and
;; (rs57 + rc57). From this relationship, prove the remainder bound invariant.

;; rmd(j) = 2^-55 * (si(rs57(j), 57) + si(rc57(j), 57)),

;; -d <= rmd(j) < d,

;; where j >= 1.

;; Remainder approximation

(defundd approx (i)
  (+ (si (bits (rs57 i) 56 54) 3)
     (si (bits (rc57 i) 56 54) 3)))

;; The first SRT iteration

(defthmd rmd1-rewrite
  (implies (not (specialp))
           (equal (rmd 1)
	          (* (/ *2^55*)
                     (+ (si (rs57 1) 57)
                        (si (rc57 1) 57))))))

(defthm rmd1-bounds
  (implies (not (specialp))
           (and (< (- (d)) (rmd 1))
                (< (rmd 1) (d))))
  :rule-classes :linear)

(defthmd bits-rs-0-0
  (implies (equal n (case (fmtrem)
                      (3 1)
                      (2 30)
                      (1 43)))
           (equal (bits (rs-0) n 0)
                  0)))

(defthmd bits-rc-0-0
  (implies (equal n (case (fmtrem)
                      (3 1)
                      (2 30)
                      (1 43)))
           (equal (bits (rc-0) n 0)
                  0)))

;; The iterative phase

(defthmd bits-rs57&rc57-0
  (implies (and (equal n (- 53 (prec (f))))
                (not (equal (fmtrem) 3)))
           (and (equal (bits (rs57 j) n 0) 0)
                (equal (bits (rc57 j) n 0) 0))))

(defthmd rmd-rewrite
  (implies (and (not (specialp))
                (posp j))
           (equal (rmd j)
                  (* (/ *2^55*)
                     (+ (si (rs57 j) 57) (si (rc57 j) 57))))))

(defthm rmd-bounds
  (implies (and (not (specialp))
                (posp j))
           (and (<= (- (d)) (rmd j))
                (< (rmd j) (d))))
  :rule-classes :linear)

;; ======================================================================

;; Prove quot(j) = 2^54 * quotient(j),
;; and quotm1(j) = quot(j) - 2^(55 - j)

(defthmd quot&quotm1-rewrite
  (implies (and (posp j)
                (<= j (n)))
           (and (equal (quot j)
                       (* *2^54* (quotient j)))
                (equal (quotm1 j)
                       (- (quot j) (expt 2 (- 55 j)))))))

;; Connect qtrunc and stk with x/d and p

(defthmd quotf-to-x/d
  (implies (not (specialp))
           (equal (quotf)
                  (- (* *2^54*
                        (/ (x) (d)))
                     (* (expt 2 (- 55 (n)))
                        (/ (rmd (n)) (d)))))))

(defthmd quotm1f-to-x/d
  (implies (not (specialp))
           (equal (quotm1f)
                  (- (* *2^54*
                        (/ (x) (d)))
                     (* (expt 2 (- 55 (n)))
                        (1+ (/ (rmd (n)) (d))))))))

(defthmd qtrunc-rewrite-gen
  (implies (not (specialp))
           (equal (qtrunc)
                  (cond ((<= (si (expq-1) 13) 1)
                         (fl (* (expt 2 (+ (prec (f))
                                           (si (expq-1) 13)))
                                (/ (x) (d)))))
                        ((< (x) (d))
                         (if (equal (fnum) 2)
                             (fl (* (expt 2 (+ 2 (prec (f))))
                                    (/ (x) (d))))
                           (* 2 (fl (* (expt 2 (1+ (prec (f))))
                                       (/ (x) (d)))))))
                        (t (fl (* (expt 2 (1+ (prec (f))))
                                  (/ (x) (d)))))))))

(defthmd stk-rewrite-gen-1
  (implies (and (<= (si (expq-1) 13) 1)
                (not (specialp)))
	   (equal (stk)
	          (if (and (integerp (* (expt 2 (1- (n)))
                                        (/ (x) (d))))
                           (< -54 (si (expq-1) 13))
                           (equal (bits (* *2^54*
                                           (/ (x) (d)))
                                        (- (si (expq-1) 13))
                                        0)
                                  0)
                           (equal (bits (* (expt 2 (+ 53 (si (expq-1) 13)))
                                           (/ (x) (d)))
                                        (- 52 (prec (f)))
                                        0)
                                  0)
                           (equal (bitn (* (expt 2 (+ (prec (f))
                                                      (si (expq-1) 13)))
                                           (/ (x) (d)))
                                        0)
                                  0))
		      0 1))))

(defthmd stk-rewrite-gen-2
  (implies (and (< (x) (d))
                (> (si (expq-1) 13) 1)
                (not (specialp)))
	   (equal (stk)
                  (if (and (integerp (* (expt 2 (1- (n)))
                                        (/ (x) (d))))
                           (equal (bits (* *2^55*
                                           (/ (x) (d)))
                                        (- 52 (prec (f)))
                                        0)
                                  0)
                           (equal (bitn (* (expt 2 (+ 2 (prec (f))))
                                           (/ (x) (d)))
                                        0)
                                  0))
                      0 1))))

(defthmd stk-rewrite-gen-3
  (implies (and (<= (d) (x))
                (>= (si (expq-1) 13) 1)
                (not (specialp)))
	   (equal (stk)
                  (if (and (integerp (* (expt 2 (1- (n)))
                                        (/ (x) (d))))
                           (equal (bits (* *2^54*
                                           (/ (x) (d)))
                                        (- 52 (prec (f)))
                                        0)
                                  0)
                           (equal (bitn (* (expt 2 (1+ (prec (f))))
                                           (/ (x) (d)))
                                        0)
                                  0))
                      0 1))))

;; Rounding

(defund rmode-prime (mode sign)
  (declare (xargs :guard (and (symbolp mode)
                              (bitp sign))))
  (cond ((and (equal mode 'RUP)
              (equal sign 1))
         'RDN)
        ((and (equal mode 'RDN)
              (equal sign 1))
         'RUP)
        (t mode)))

(defund mode (rmode)
  (declare (xargs :guard (natp rmode)))
  (case rmode
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

;; Normal rounding

(defthmd rnd-abs-a/b-to-qrnd
  (implies (and (<= 1 (si (expq) 13))
                (not (specialp)))
           (equal (rnd (abs (/ (a) (b)))
                       (rmode-prime (mode (rmode)) (sign))
                       (prec (f)))
                  (* (expt 2 (+ 1
                                (si (expq) 13)
                                (- (bias (f)))
                                (- (prec (f)))))
                     (+ (expt 2 (1- (prec (f))))
                        (bits (qrnd) (- (prec (f)) 2) 0))))))

(defthmd inx-exact-a/b-rel
  (implies (and (<= 1 (si (expq) 13))
                (not (specialp)))
           (equal (inx)
                  (if (equal (rnd (abs (/ (a) (b)))
                                  (rmode-prime (mode (rmode)) (sign))
                                  (prec (f)))
                             (abs (/ (a) (b))))
                      0
                    1))))

;; Subnormal rounding

(defthmd drnd-abs-a/b-to-qrnd
  (implies (and (not (specialp))
                (< (abs (/ (a) (b)))
                   (spn (f))))
           (equal (drnd (abs (/ (a) (b)))
                        (rmode-prime (mode (rmode)) (sign))
                        (f))
                  (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                     (bits (qrnd) (1- (prec (f))) 0)))))

(defthmd inx-exact-a/b-denormal-rel
  (implies (and (not (specialp))
                (< (abs (/ (a) (b)))
                   (spn (f))))
           (equal (inx)
                  (if (equal (drnd (abs (/ (a) (b)))
                                   (rmode-prime (mode (rmode)) (sign))
                                   (f))
                             (abs (/ (a) (b))))
                      0
                    1))))

;; The main lemma

(defthmd fdivlane-main
  (mv-let
    (data-spec r-spec)
    (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
    (and (equal (data) data-spec)
         (equal (logior (rin) (flags)) r-spec))))

;; The final theorem

(defthmd fdivlane-correct
  (implies (input-constraints opa opb fnum vec rin)
           (let* ((f (case fnum (1 (hp)) (2 (sp)) (3 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (fzp (bitn rin 24))
                  (dnp (bitn rin 25))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fdivlane opa opb fnum vec fzp dnp rmode)
               (mv-let
                 (data-spec r-spec)
                 (arm-binary-spec 'div
                                  (bits opa (1- fmtw) 0)
                                  (bits opb (1- fmtw) 0)
                                  rin
                                  f)
                 (and (equal data data-spec)
                      (equal (logior rin flags) r-spec)))))))
