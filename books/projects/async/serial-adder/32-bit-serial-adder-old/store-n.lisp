;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2019

(in-package "ADE")

(include-book "macros")
(include-book "unbound")

;; ======================================================================

;; LATCH-N

(defun latch-n-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'G m)                   ; Occurrence name - G_m
           (list (si 'Q m) (si 'Q~ m)) ; Outputs (Q_m, Q~_m)
           'LATCH                      ; Type LATCH
           (list 'CLK (si 'D m)))      ; Inputs
     (latch-n-body (1+ m) (1- n)))))

(module-generator
 latch-n* (n)
 (si 'LATCH-N n)           ; Name
 (list* 'CLK (sis 'D 0 n)) ; Inputs
 (sis 'Q 0 n)              ; Outputs
 (sis 'G 0 n)              ; States
 (latch-n-body 0 n)        ; Body
 (declare (xargs :guard (natp n))))

(defund latch-n& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (equal (assoc (si 'LATCH-N n) netlist)
         (latch-n* n)))

(defund latch-n$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (latch-n* n)))

(local
 (defthmd check-latch-n$netlist-64
   (and (net-syntax-okp (latch-n$netlist 64))
        (net-arity-okp (latch-n$netlist 64))
        (latch-n& (latch-n$netlist 64) 64))))

;; LATCH-N value

(defun latch-n-body-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      wire-alist
    (latch-n-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 1 (latch-n-body m n)
                      wire-alist st-alist netlist)
     st-alist
     netlist)))

(local
 (defthm latch-n$unbound-in-body
   (and
    (unbound-in-body 'clk (latch-n-body m n))
    (implies (and (natp k)
                  (natp m)
                  (< k m))
             (unbound-in-body (si 'Q k)
                              (latch-n-body m n))))
   :hints (("Goal" :in-theory (enable latch-n-body occ-outs)))))

(local
 (defthm latch-n$all-unbound-in-body
   (all-unbound-in-body (sis 'D x y) (latch-n-body m n))
   :hints (("Goal" :in-theory (enable latch-n-body occ-outs)))))

(local
 (defthm latch-n-body$value
   (implies (natp m)
            (equal (assoc-eq-values
                    (sis 'Q m n)
                    (se-occ (latch-n-body m n) wire-alist st-alist netlist))
                   (fv-if (assoc-eq-value 'clk wire-alist)
                          (assoc-eq-values (sis 'D m n) wire-alist)
                          (strip-cars
                           (assoc-eq-values (sis 'G m n) st-alist)))))
   :hints (("Goal"
            :induct (latch-n-body-induct m n wire-alist st-alist netlist)
            :in-theory (enable de-rules
                               fv-if-rewrite
                               f-gates
                               repeat
                               3vp
                               sis)))))

(defthm latch-n$value
  (implies (and (latch-n& netlist n)
                (true-listp inputs)
                (equal (len inputs) (1+ n))
                (equal (len st) n)
                (true-listp st))
           (equal (se (si 'latch-n n) inputs st netlist)
                  (fv-if (car inputs) (cdr inputs) (strip-cars st))))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'latch-n n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             latch-n&
                             latch-n*$destructure)
                            (de-module-disabled-rules)))))

;; LATCH-N state

(defun latch-n-body-state-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      st-alist
    (latch-n-body-state-induct
     (1+ m)
     (1- n)
     wire-alist
     (de-occ-bindings 1 (latch-n-body m n)
                      wire-alist st-alist netlist)
     netlist)))

(local
 (defthm latch-n-body$state-aux-1
   (implies (and (member x (strip-cars alist))
                 x)
            (consp (assoc x alist)))
   :rule-classes :type-prescription))

(local
 (defthm latch-n-body$state-aux-2
   (implies (and (natp l)
                 (natp m)
                 (< l m))
            (not (member (si 'g l)
                         (strip-cars (latch-n-body m n)))))
   :hints (("Goal"
            :in-theory (enable latch-n-body)))))

(local
 (defthm latch-n-body$state
   (implies (and (natp m)
                 (subsetp (sis 'G m n) (strip-cars st-alist)))
            (equal (assoc-eq-values
                    (sis 'G m n)
                    (de-occ (latch-n-body m n) wire-alist st-alist netlist))
                   (pairlis$
                    (fv-if (assoc-eq-value 'clk wire-alist)
                           (assoc-eq-values (sis 'D m n) wire-alist)
                           (strip-cars
                            (assoc-eq-values (sis 'G m n) st-alist)))
                    nil)))
   :hints (("Goal"
            :induct (latch-n-body-state-induct
                     m n wire-alist st-alist netlist)
            :in-theory (enable de-rules
                               fv-if-rewrite
                               f-gates
                               repeat
                               sis))
           ("Subgoal *1/2"
            :use (:instance not-equal-with-si-of-diff-symbol
                            (s1 nil)
                            (s2 'g)
                            (n m))))))

(defthm latch-n$state
  (implies (and (latch-n& netlist n)
                (true-listp inputs)
                (equal (len inputs) (1+ n))
                (equal (len st) n)
                (true-listp st))
           (equal (de (si 'latch-n n) inputs st netlist)
                  (pairlis$ (fv-if (car inputs) (cdr inputs) (strip-cars st))
                            nil)))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (de (si 'latch-n n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             latch-n&
                             latch-n*$destructure)
                            (de-module-disabled-rules)))))

;; ======================================================================

;; FF-N

(defun ff-n-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'G m)                   ; Occurrence name - G_m
           (list (si 'Q m) (si 'Q~ m)) ; Outputs (Q_m, Q~_m)
           'FF                         ; Type FF
           (list 'CLK (si 'D m)))      ; Inputs
     (ff-n-body (1+ m) (1- n)))))

(module-generator
 ff-n* (n)
 (si 'FF-N n)              ; Name
 (list* 'CLK (sis 'D 0 n)) ; Inputs
 (sis 'Q 0 n)              ; Outputs
 (sis 'G 0 n)              ; States
 (ff-n-body 0 n)           ; Body
 (declare (xargs :guard (natp n))))

(defund ff-n& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (equal (assoc (si 'FF-N n) netlist)
         (ff-n* n)))

(defund ff-n$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (ff-n* n)))

(local
 (defthmd check-ff-n$netlist-64
   (and (net-syntax-okp (ff-n$netlist 64))
        (net-arity-okp (ff-n$netlist 64))
        (ff-n& (ff-n$netlist 64) 64))))

;; FF-N value

(defun ff-n-body-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      wire-alist
    (ff-n-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 1 (ff-n-body m n)
                      wire-alist st-alist netlist)
     st-alist
     netlist)))

(local
 (defthm ff-n$unbound-in-body
   (and
    (unbound-in-body 'clk (ff-n-body m n))
    (implies (and (natp k)
                  (natp m)
                  (< k m))
             (unbound-in-body (si 'Q k)
                              (ff-n-body m n))))
   :hints (("Goal" :in-theory (enable ff-n-body occ-outs)))))

(local
 (defthm ff-n$all-unbound-in-body
   (all-unbound-in-body (sis 'D x y) (ff-n-body m n))
   :hints (("Goal" :in-theory (enable ff-n-body occ-outs)))))

(local
 (defthm ff-n-body$value
   (implies (natp m)
            (equal (assoc-eq-values
                    (sis 'Q m n)
                    (se-occ (ff-n-body m n)
                            wire-alist st-alist netlist))
                   (v-threefix (strip-cars
                                (assoc-eq-values (sis 'G m n)
                                                 st-alist)))))
   :hints (("Goal"
            :induct (ff-n-body-induct m n wire-alist st-alist netlist)
            :in-theory (enable de-rules
                               sis)))))

(defthm ff-n$value
  (implies (and (ff-n& netlist n)
                (equal (len st) n)
                (true-listp st))
           (equal (se (si 'ff-n n) inputs st netlist)
                  (v-threefix (strip-cars st))))
  :hints (("Goal"
           :expand (:free (n)
                          (se (si 'ff-n n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             ff-n&
                             ff-n*$destructure)
                            (de-module-disabled-rules)))))

;; FF-N state

(defun ff-n-body-state-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      st-alist
    (ff-n-body-state-induct
     (1+ m)
     (1- n)
     wire-alist
     (de-occ-bindings 1 (ff-n-body m n)
                      wire-alist st-alist netlist)
     netlist)))

(local
 (defthm ff-n-body$state-aux-1
   (implies (and (member x (strip-cars alist))
                 x)
            (consp (assoc x alist)))
   :rule-classes :type-prescription))

(local
 (defthm ff-n-body$state-aux-2
   (implies (and (natp l)
                 (natp m)
                 (< l m))
            (not (member (si 'g l)
                         (strip-cars (ff-n-body m n)))))
   :hints (("Goal"
            :in-theory (enable ff-n-body)))))

(local
 (defthm ff-n-body$state
   (implies (and (natp m)
                 (subsetp (sis 'G m n) (strip-cars st-alist)))
            (equal (assoc-eq-values
                    (sis 'G m n)
                    (de-occ (ff-n-body m n) wire-alist st-alist netlist))
                   (pairlis$
                    (fv-if (assoc-eq-value 'clk wire-alist)
                           (assoc-eq-values (sis 'D m n) wire-alist)
                           (strip-cars
                            (assoc-eq-values (sis 'G m n) st-alist)))
                    nil)))
   :hints (("Goal"
            :induct (ff-n-body-state-induct
                     m n wire-alist st-alist netlist)
            :in-theory (enable de-rules
                               fv-if-rewrite
                               f-gates
                               repeat
                               sis))
           ("Subgoal *1/2"
            :use (:instance not-equal-with-si-of-diff-symbol
                            (s1 nil)
                            (s2 'g)
                            (n m))))))

(defthm ff-n$state
  (implies (and (ff-n& netlist n)
                (true-listp inputs)
                (equal (len inputs) (1+ n))
                (equal (len st) n)
                (true-listp st))
           (equal (de (si 'ff-n n) inputs st netlist)
                  (pairlis$ (fv-if (car inputs) (cdr inputs) (strip-cars st))
                            nil)))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (de (si 'ff-n n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             ff-n&
                             ff-n*$destructure)
                            (de-module-disabled-rules)))))
