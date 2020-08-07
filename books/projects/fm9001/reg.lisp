;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; Definitions and proofs of n-bit scan registers.

(in-package "FM9001")

(include-book "primitives")
(include-book "unbound")

;; ======================================================================

;; REG* n

;; An n-bit scan register. Scans from low-order to high-order.  The high order
;; bit Q_(n-1) is the scan-out.

;; MODULE REG_n;
;; INPUTS CLK, TE, TI, D_0 ... D_(n-1);
;; OUTPUTS Q_0 ... Q_(n-1);

(defund reg-body (m n ti te)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'G m)                    ; Occurrence name - G_m
           (list (si 'Q m) (si 'QB m))  ; Outputs (Q_m, QB_m)
           'FD1S                        ; Type FD1S
           (list (si 'D m) 'CLK ti te)) ; Inputs
     (reg-body (1+ m) (1- n) (si 'Q m) te))))

(destructuring-lemma
 reg* (n)
 (declare (xargs :guard (natp n)))
 nil                                      ; Bindings
 (si 'REG n)                              ; Name
 (list* 'CLK 'TE 'TI (sis 'D 0 n))        ; Inputs
 (sis 'Q 0 n)                             ; Outputs
 (sis 'G 0 n)                             ; States
 (list*
  (list 'TE-BUFFER '(TE-BUF)              ; Body
        (if (< n 8) 'B-BUF 'B-BUF-PWR)
        '(TE))
  '(TI-DEL (TI-BUF) DEL4 (TI))
  (reg-body 0 n 'TI-BUF 'TE-BUF)))

(defund reg& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'REG n) netlist)
              (reg* n))
       (let ((netlist (delete-to-eq (si 'REG n) netlist)))
         (if (< n 8)
             t
           (b-buf-pwr& netlist)))))

(defun reg$netlist (n)
  (declare (xargs :guard (natp n)))
  (if (< n 8)
      (list (reg* n))
    (cons (reg* n) *b-buf-pwr*)))

;;  REG value

; Matt K. mod: ACL2(p) with waterfall parallelism hangs in SBCL, so we turn it
; off.
(set-waterfall-parallelism nil)

(defthm reg-body$unbound-in-body
  (and (unbound-in-body 'CLK (reg-body m n ti te))
       (unbound-in-body 'TI (reg-body m n ti te))
       (unbound-in-body 'TI-DEL (reg-body m n ti te))
       (unbound-in-body 'TE (reg-body m n ti te))
       (unbound-in-body 'TE-BUF (reg-body m n ti te))
       (unbound-in-body (si 'D l) (reg-body m n ti te))
       (implies (and (natp l)
                     (natp m)
                     (< l m))
        (unbound-in-body (si 'Q l) (reg-body m n ti te))))
  :hints (("Goal"
           :in-theory (enable reg-body occ-outs))))

(defthm reg-body$all-unbound-in-body
  (all-unbound-in-body (sis 'D x y) (reg-body m n ti te))
  :hints (("Goal" :in-theory (enable sis))))

(defun reg-body-induction (m n ti te bindings state-bindings netlist)
  (if (zp n)
      (list m ti te bindings state-bindings netlist)
    (reg-body-induction
     (1+ m)
     (1- n)
     (si 'Q m)
     te
     (se-occ-bindings 1 (reg-body m n ti te)
                      bindings state-bindings netlist)
     state-bindings
     netlist)))

(defthmd reg-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'Q m n)
                   (se-occ (reg-body m n ti te)
                           bindings state-bindings netlist))
                  (v-threefix (strip-cars
                               (assoc-eq-values (sis 'G m n)
                                                state-bindings)))))
  :hints (("Goal"
           :induct (reg-body-induction m n ti te bindings
                                       state-bindings netlist)
           :in-theory (enable se-rules 3vp f-gates reg-body sis))))

(in-theory (disable reg-body$unbound-in-body
                    reg-body$all-unbound-in-body))

(not-primp-lemma reg)

(defthmd reg$value
  (implies (and (reg& netlist n)
                (equal (len sts) n)
                (true-listp sts))
           (equal (se (si 'REG n) inputs sts netlist)
                  (v-threefix (strip-cars sts))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             reg&
                             reg*$destructure
                             not-primp-reg
                             reg-body$value
                             b-buf-pwr$value)
                            ()))))

;; REG state

(defun reg-body-state-induction (m n ti te bindings state-bindings netlist)
  (if (zp n)
      (list m ti te bindings state-bindings netlist)
    (reg-body-state-induction
     (1+ m)
     (1- n)
     (si 'Q m)
     te
     bindings
     (de-occ-bindings 1 (reg-body m n ti te)
                      bindings state-bindings netlist)
     netlist)))

(local
 (defthm reg-body$state-aux-1
   (implies (and (member x (strip-cars alist))
                 x)
            (consp (assoc x alist)))
   :rule-classes :type-prescription))

(local
 (defthm reg-body$state-aux-2
   (implies (and (natp l)
                 (natp m)
                 (< l m))
            (not (member (si 'g l)
                         (strip-cars (reg-body m n ti te)))))
   :hints (("Goal"
            :in-theory (enable reg-body)))))

(defthm reg-body$state
  (implies (and (natp m)
                (subsetp (sis 'G m n) (strip-cars state-bindings))
                (not (assoc-eq-value te bindings)))
           (equal (assoc-eq-values
                   (sis 'G m n)
                   (de-occ (reg-body m n ti te) bindings
                           state-bindings netlist))
                  (pairlis$
                   (v-threefix (assoc-eq-values (sis 'D m n) bindings))
                   nil)))
  :hints (("Goal"
           :induct (reg-body-state-induction m n ti te bindings
                                             state-bindings netlist)
           :in-theory (enable de-rules f-gates reg-body sis))
          ("Subgoal *1/2"
           :use (:instance si-of-diff-symbols-2
                           (s1 nil)
                           (s2 'g)
                           (n m)))))

(defthmd reg$state
  (implies (and (reg& netlist n)
                (equal (len d) n)
                (true-listp d)
                (equal te nil))
           (equal (de (si 'REG n)
                      (list* clk te ti d)
                      sts netlist)
                  (pairlis$ (v-threefix d)
                            nil)))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                             reg&
                             reg*$destructure
                             not-primp-reg
                             reg-body$unbound-in-body
                             reg-body$all-unbound-in-body
                             b-buf-pwr$value)
                            ()))))

;; ======================================================================

;; WE-REG* n

;; An n-bit write-enabled scan register.  Scans from low-order to high-order.
;; The high order bit Q_(n-1) is the scan-out.

;; MODULE WE-REG_n;
;; INPUTS CLK, WE, TE, TI, D_0 ... D_(n-1);
;; OUTPUTS Q_0 ... Q_(n-1);

;; The test input TI is buffered by a 4ns delay to avoid problems with clock
;; skew.

(defund we-reg-body (m n ti)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'G m)                                ; Occurrence name - G_m
           (list (si 'Q m) (si 'QB m))              ; Outputs (Q_m , QB_m)
           'FD1SLP                                  ; Type FD1SLP
           (list (si 'D m) 'CLK 'WE-BUF ti 'TE-BUF))      ; Inputs
     (we-reg-body (1+ m) (1- n) (si 'Q m)))))

(destructuring-lemma
 we-reg* (n)
 (declare (xargs :guard (natp n)))
 nil                                          ; Bindings
 (si 'WE-REG n)                               ; Name
 (list* 'CLK 'WE 'TE 'TI (sis 'D 0 n))        ; Inputs
 (sis 'Q 0 n)                                 ; Outputs
 (sis 'G 0 n)                                 ; Statelist
 (list*
  (list 'WE-BUFFER '(WE-BUF)                  ; Body
        (if (< n 8) 'B-BUF 'B-BUF-PWR)
        '(WE))
  (list 'TE-BUFFER '(TE-BUF)
        (if (< n 8) 'B-BUF 'B-BUF-PWR)
        '(TE))
  '(TI-DEL (TI-BUF) DEL4 (TI))
  (we-reg-body 0 n 'TI-BUF)))

(defund we-reg& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'WE-REG n) netlist)
              (we-reg* n))
       (let ((netlist (delete-to-eq (si 'WE-REG n) netlist)))
         (if (< n 8)
             t
           (b-buf-pwr& netlist)))))

(defun we-reg$netlist (n)
  (declare (xargs :guard (natp n)))
  (if (< n 8)
      (list (we-reg* n))
    (cons (we-reg* n) *b-buf-pwr*)))

;;  WE-REG value

(defthm we-reg-body$unbound-in-body
  (and (unbound-in-body 'CLK (we-reg-body m n ti))
       (unbound-in-body 'WE (we-reg-body m n ti))
       (unbound-in-body 'WE-BUF (we-reg-body m n ti))
       (unbound-in-body 'TI (we-reg-body m n ti))
       (unbound-in-body 'TI-BUF (we-reg-body m n ti))
       (unbound-in-body 'TE (we-reg-body m n ti))
       (unbound-in-body 'TE-BUF (we-reg-body m n ti))
       (unbound-in-body (si 'D l) (we-reg-body m n ti))
       (implies (and (natp l)
                     (natp m)
                     (< l m))
                (unbound-in-body (si 'Q l) (we-reg-body m n ti))))
  :hints (("Goal"
           :in-theory (enable we-reg-body occ-outs))))

(defthm we-reg-body$all-unbound-in-body
  (all-unbound-in-body (sis 'D x y) (we-reg-body m n ti))
  :hints (("Goal" :in-theory (enable sis))))

(defun we-reg-body-induction (m n ti bindings state-bindings netlist)
  (if (zp n)
      (list m ti bindings state-bindings netlist)
    (we-reg-body-induction
     (1+ m)
     (1- n)
     (si 'Q m)
     (se-occ-bindings 1 (we-reg-body m n ti)
                      bindings state-bindings netlist)
     state-bindings
     netlist)))

(defthmd we-reg-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'Q m n)
                   (se-occ (we-reg-body m n ti)
                           bindings state-bindings netlist))
                  (v-threefix (strip-cars
                               (assoc-eq-values (sis 'G m n)
                                                state-bindings)))))
  :hints (("Goal"
           :induct (we-reg-body-induction m n ti bindings
                                          state-bindings netlist)
           :in-theory (enable se-rules 3vp f-gates we-reg-body sis))))

(in-theory (disable we-reg-body$unbound-in-body
                    we-reg-body$all-unbound-in-body))

(not-primp-lemma we-reg)

(defthmd we-reg$value
  (implies (and (we-reg& netlist n)
                (equal (len sts) n)
                (true-listp sts))
           (equal (se (si 'WE-REG n) inputs sts netlist)
                  (v-threefix (strip-cars sts))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             we-reg&
                             we-reg*$destructure
                             not-primp-we-reg
                             we-reg-body$value
                             b-buf-pwr$value)
                            ()))))

;; WE-REG state

(defun we-reg-body-state-induction (m n ti bindings state-bindings netlist)
  (if (zp n)
      (list m ti bindings state-bindings netlist)
    (we-reg-body-state-induction
     (1+ m)
     (1- n)
     (si 'Q m)
     bindings
     (de-occ-bindings 1 (we-reg-body m n ti)
                      bindings state-bindings netlist)
     netlist)))

(local
 (defthm we-reg-body$state-aux
   (implies (and (natp l)
                 (natp m)
                 (< l m))
            (not (member (si 'g l)
                         (strip-cars (we-reg-body m n ti)))))
   :hints (("Goal"
            :in-theory (enable we-reg-body)))))

(defthmd we-reg-body$state
  (implies (and (natp m)
                (subsetp (sis 'G m n) (strip-cars state-bindings))
                (not (assoc-eq-value 'TE-BUF bindings)))
           (equal (assoc-eq-values
                   (sis 'G m n)
                   (de-occ (we-reg-body m n ti)
                           bindings state-bindings netlist))
                  (pairlis$
                   (fv-if (assoc-eq-value 'WE-BUF bindings)
                          (assoc-eq-values (sis 'D m n) bindings)
                          (strip-cars
                           (assoc-eq-values (sis 'G m n) state-bindings)))
                   nil)))
  :hints (("Goal"
           :induct (we-reg-body-state-induction m n ti bindings
                                                state-bindings netlist)
           :in-theory (enable de-rules
                               f-gates
                               fv-if-rewrite
                               we-reg-body
                               sis
                               repeat))
          ("Subgoal *1/2"
           :use (:instance si-of-diff-symbols-2
                           (s1 nil)
                           (s2 'g)
                           (n m)))))

(defthmd we-reg$state
  (implies (and (we-reg& netlist n)
                (equal (len d) n)
                (true-listp d)
                (equal (len sts) n)
                (true-listp sts)
                (equal te nil))
           (equal (de (si 'WE-REG n)
                      (list* clk we te ti d)
                      sts netlist)
                  (pairlis$
                   (fv-if we d (strip-cars sts))
                   nil)))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                             we-reg&
                             we-reg*$destructure
                             not-primp-we-reg
                             we-reg-body$state
                             we-reg-body$unbound-in-body
                             we-reg-body$all-unbound-in-body
                             fv-if-rewrite
                             b-buf-pwr$value)
                            (tv-disabled-rules)))))


