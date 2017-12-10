;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2017

(in-package "ADE")

(include-book "macros")
(include-book "unbound")

;; ======================================================================

;; LATCH-N

(defund latch-n-body (m n)
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

(destructuring-lemma
 latch-n* (n)
 (declare (xargs :guard (natp n)))
 nil                       ; Bindings
 (si 'LATCH-N n)           ; Name
 (list* 'CLK (sis 'D 0 n)) ; Inputs
 (sis 'Q 0 n)              ; Outputs
 (sis 'G 0 n)              ; States
 (latch-n-body 0 n))       ; Body

(defund latch-n& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (equal (assoc (si 'LATCH-N n) netlist)
         (latch-n* n)))

(defun latch-n$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (latch-n* n)))

(defthmd latch-n$netlist-64-okp
  (and (net-syntax-okp (latch-n$netlist 64))
       (net-arity-okp (latch-n$netlist 64))))

;; LATCH-N value

(defun latch-n-body-induct (m n wire-alist sts-alist netlist)
  (if (zp n)
      wire-alist
    (latch-n-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 1 (latch-n-body m n)
                      wire-alist sts-alist netlist)
     sts-alist
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

(defthmd latch-n-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'Q m n)
                   (se-occ (latch-n-body m n)
                           wire-alist sts-alist netlist))
                  (fv-if (assoc-eq-value 'clk wire-alist)
                         (assoc-eq-values (sis 'D m n) wire-alist)
                         (strip-cars
                          (assoc-eq-values (sis 'G m n) sts-alist)))))
  :hints (("Goal"
           :induct (latch-n-body-induct m n wire-alist sts-alist netlist)
           :in-theory (enable se-rules
                               latch-n-body
                               fv-if-rewrite
                               f-gates
                               repeat
                               3vp
                               sis))))

(not-primp-lemma latch-n)

(defthmd latch-n$value
  (implies (and (latch-n& netlist n)
                (equal (len d) n)
                (true-listp d)
                (equal (len sts) n)
                (true-listp sts))
           (equal (se (si 'LATCH-N n) (list* clk d) sts netlist)
                  (fv-if clk d (strip-cars sts))))
  :hints (("Goal"
           :in-theory (e/d* (se-rules
                             latch-n&
                             latch-n*$destructure
                             not-primp-latch-n
                             latch-n-body$value)
                            ()))))

;; LATCH-N state

(defun latch-n-body-state-induct (m n wire-alist sts-alist netlist)
  (if (zp n)
      sts-alist
    (latch-n-body-state-induct
     (1+ m)
     (1- n)
     wire-alist
     (de-occ-bindings 1 (latch-n-body m n)
                      wire-alist sts-alist netlist)
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

(defthm latch-n-body$state
  (implies (and (natp m)
                (subsetp (sis 'G m n) (strip-cars sts-alist)))
           (equal (assoc-eq-values
                   (sis 'G m n)
                   (de-occ (latch-n-body m n) wire-alist sts-alist netlist))
                  (pairlis$
                   (fv-if (assoc-eq-value 'clk wire-alist)
                          (assoc-eq-values (sis 'D m n) wire-alist)
                          (strip-cars
                           (assoc-eq-values (sis 'G m n) sts-alist)))
                   nil)))
  :hints (("Goal"
           :induct (latch-n-body-state-induct m n wire-alist sts-alist netlist)
           :in-theory (enable de-rules
                               latch-n-body
                               fv-if-rewrite
                               f-gates
                               repeat
                               sis))
          ("Subgoal *1/2"
           :use (:instance si-of-diff-symbols-2
                           (s1 nil)
                           (s2 'g)
                           (n m)))))

(defthmd latch-n$state
  (implies (and (latch-n& netlist n)
                (equal (len d) n)
                (true-listp d)
                (equal (len sts) n)
                (true-listp sts))
           (equal (de (si 'LATCH-N n) (list* clk d) sts netlist)
                  (pairlis$ (fv-if clk d (strip-cars sts))
                            nil)))
  :hints (("Goal"
           :in-theory (e/d* (de-rules
                             latch-n&
                             latch-n*$destructure
                             not-primp-latch-n)
                            ()))))

;; ======================================================================

;; FF-N

(defund ff-n-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  (if (zp n)
      nil
    (cons
     (list (si 'G m)                   ; Occurrence name - G_m
           (list (si 'Q m) (si 'Q~ m)) ; Outputs (Q_m, Q~_m)
           'FD1                        ; Type FD1
           (list 'CLK (si 'D m)))      ; Inputs
     (ff-n-body (1+ m) (1- n)))))

(destructuring-lemma
 ff-n* (n)
 (declare (xargs :guard (natp n)))
 nil                       ; Bindings
 (si 'FF-N n)              ; Name
 (list* 'CLK (sis 'D 0 n)) ; Inputs
 (sis 'Q 0 n)              ; Outputs
 (sis 'G 0 n)              ; States
 (ff-n-body 0 n))          ; Body

(defund ff-n& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (equal (assoc (si 'FF-N n) netlist)
         (ff-n* n)))

(defun ff-n$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (ff-n* n)))

(defthmd ff-n$netlist-64-okp
  (and (net-syntax-okp (ff-n$netlist 64))
       (net-arity-okp (ff-n$netlist 64))))

;; FF-N value

(defun ff-n-body-induct (m n wire-alist sts-alist netlist)
  (if (zp n)
      wire-alist
    (ff-n-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 1 (ff-n-body m n)
                      wire-alist sts-alist netlist)
     sts-alist
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

(defthmd ff-n-body$value
  (implies (natp m)
           (equal (assoc-eq-values
                   (sis 'Q m n)
                   (se-occ (ff-n-body m n)
                           wire-alist sts-alist netlist))
                  (v-threefix (strip-cars
                               (assoc-eq-values (sis 'G m n)
                                                sts-alist)))))
  :hints (("Goal"
           :induct (ff-n-body-induct m n wire-alist sts-alist netlist)
           :in-theory (enable se-rules ff-n-body sis))))

(not-primp-lemma ff-n)

(defthmd ff-n$value
  (implies (and (ff-n& netlist n)
                (equal (len sts) n)
                (true-listp sts))
           (equal (se (si 'FF-N n) ins sts netlist)
                  (v-threefix (strip-cars sts))))
  :hints (("Goal"
           :in-theory (e/d* (se-rules
                             ff-n&
                             ff-n*$destructure
                             not-primp-ff-n
                             ff-n-body$value)
                            ()))))

;; FF-N state

(defun ff-n-body-state-induct (m n wire-alist sts-alist netlist)
  (if (zp n)
      sts-alist
    (ff-n-body-state-induct
     (1+ m)
     (1- n)
     wire-alist
     (de-occ-bindings 1 (ff-n-body m n)
                      wire-alist sts-alist netlist)
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

(defthm ff-n-body$state
  (implies (and (natp m)
                (subsetp (sis 'G m n) (strip-cars sts-alist)))
           (equal (assoc-eq-values
                   (sis 'G m n)
                   (de-occ (ff-n-body m n) wire-alist sts-alist netlist))
                  (pairlis$
                   (fv-if (assoc-eq-value 'clk wire-alist)
                          (assoc-eq-values (sis 'D m n) wire-alist)
                          (strip-cars
                           (assoc-eq-values (sis 'G m n) sts-alist)))
                   nil)))
  :hints (("Goal"
           :induct (ff-n-body-state-induct m n wire-alist sts-alist netlist)
           :in-theory (enable de-rules
                              ff-n-body
                              fv-if-rewrite
                              f-gates
                              repeat
                              sis))
          ("Subgoal *1/2"
           :use (:instance si-of-diff-symbols-2
                           (s1 nil)
                           (s2 'g)
                           (n m)))))

(defthmd ff-n$state
  (implies (and (ff-n& netlist n)
                (equal (len d) n)
                (true-listp d)
                (equal (len sts) n)
                (true-listp sts))
           (equal (de (si 'FF-N n) (list* clk d) sts netlist)
                  (pairlis$ (fv-if clk d (strip-cars sts))
                            nil)))
  :hints (("Goal"
           :in-theory (e/d* (de-rules
                             ff-n&
                             ff-n*$destructure
                             not-primp-ff-n)
                            ()))))
