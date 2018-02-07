;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "../unbound")

;; ======================================================================

;; HALF ADDER

(defconst *half-adder*
  '((half-adder
     (a b)
     (sum carry)
     ()
     ((g0 (sum)   b-xor (a b))
      (g1 (carry) b-and (a b))))))

(defthmd half-adder-okp
  (and (net-syntax-okp *half-adder*)
       (net-arity-okp *half-adder*)))

(defund half-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist half-adder))

(defthmd half-adder$value
  (implies (half-adder& netlist)
           (equal (se 'half-adder (list a b) sts netlist)
                  (list (f-xor a b)
                        (f-and a b))))
  :hints (("Goal"
           :expand (se 'half-adder (list a b) sts netlist)
           :in-theory (enable de-rules half-adder&))))

;; ======================================================================

;; FULL ADDER

(defconst *full-adder*
  (cons
   '(full-adder
     (c a b)
     (sum carry)
     ()
     ((t0 (sum1 carry1) half-adder (a b))
      (t1 (sum  carry2) half-adder (sum1 c))
      (t2 (carry)       b-or       (carry1 carry2))))

   *half-adder*))

(defthmd full-adder-okp
  (and (net-syntax-okp *full-adder*)
       (net-arity-okp *full-adder*)))

(defund full-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (netlist-hyps netlist full-adder)
       (half-adder& (delete-to-eq 'full-adder netlist))))

(defthmd full-adder$value
  (implies (full-adder& netlist)
           (equal (se 'full-adder (list c a b) sts netlist)
                  (list (f-xor3 c a b)
                        (f-or (f-and a b)
                              (f-and (f-xor a b) c)))))
  :hints (("Goal"
           :expand (se 'full-adder (list c a b) sts netlist)
           :in-theory (enable de-rules
                              full-adder&
                              half-adder$value
                              3vp
                              f-gates))))

;; ======================================================================

;; RIPPLE-CARRY ADDER

;; Ripple-carry adder body generator

(defun ripple-adder-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  ;; m is the current index and n is the number of occurrences.
  (if (zp n)
      nil
    (cons
     (list
      ;; occurrence name
      (si 'g m)
      ;; outputs
      (list (si 'sum m)
            (si 'carry (1+ m)))
      ;; inferior module reference
      'full-adder
      ;; inputs
      (list (si 'carry m)
            (si 'a m)
            (si 'b m)))

     (ripple-adder-body (1+ m) (1- n)))))

(defun ripple-adder* (n)
  (declare (xargs :guard (natp n)))
  ;; n-bit wide input vectors
  (list (si 'ripple-adder n)          ; (index ripple-adder n),
                                      ; intuitively ripple-adder_n
        (cons (si 'carry 0)           ; inputs are
              (append (sis 'a 0 n)    ; (carry_0 a_0 a_1 ... a_n-1
                      (sis 'b 0 n)))  ;          b_0 b_1 ... b_n-1)
        (append (sis 'sum 0 n)        ; outputs are
                (list (si 'carry n))) ; (sum_0 sum_1 ... sum_n-1 carry_n)
        nil                           ; no state
        (ripple-adder-body 0 n)))     ; occurrences

(defund ripple-adder& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'ripple-adder n) netlist)
              (ripple-adder* n))
       (full-adder& (delete-to-eq (si 'ripple-adder n)
                                         netlist))))

(defun ripple-adder$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (ripple-adder* n)
        *full-adder*))

(defthmd ripple-adder$netlist-64-okp
  (and (net-syntax-okp (ripple-adder$netlist 64))
       (net-arity-okp (ripple-adder$netlist 64))))

(local
 (defun ripple-adder-body-induct (m n wire-alist sts-alist netlist)
   (if (zp n)
       wire-alist
     (ripple-adder-body-induct
      (1+ m)
      (1- n)
      (se-occ-bindings 1
                       (ripple-adder-body m n)
                       wire-alist
                       sts-alist
                       netlist)
      sts-alist
      netlist))))

(local
 (defthm ripple-adder$unbound-in-body-sum
   (implies (and (natp k)
                 (natp m)
                 (< k m))
            (unbound-in-body (si 'sum k)
                             (ripple-adder-body m n)))
   :hints (("Goal" :in-theory (enable occ-outs)))))

(local
 (defthm ripple-adder-body$value
   (implies (and (full-adder& netlist)
                 (natp m)
                 (natp n)
                 ;; We need the following hypothesis for the case of (zp n)
                 (3vp (assoc-eq-value (si 'carry m) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum m n)
                                            (list (si 'carry (+ m n))))
                                    (se-occ (ripple-adder-body m n)
                                            wire-alist
                                            sts-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (assoc-eq-values (sis 'b m n) wire-alist))))
   :hints (("Goal"
            :in-theory (enable de-rules
                               full-adder$value
                               fv-adder
                               sis)
            :induct (ripple-adder-body-induct m n
                                              wire-alist
                                              sts-alist
                                              netlist)))))

(local
 (defthm ripple-adder-body$value-m=0
   (implies (and (full-adder& netlist)
                 (natp n)
                 (3vp (assoc-eq-value (si 'carry 0) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum 0 n)
                                            (list (si 'carry n)))
                                    (se-occ (ripple-adder-body 0 n)
                                            wire-alist
                                            sts-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (assoc-eq-values (sis 'b 0 n) wire-alist))))
   :hints (("Goal" :use (:instance ripple-adder-body$value
                                   (m 0))))))

(not-primp-lemma ripple-adder)

(defthm ripple-adder$value
  (implies (and (ripple-adder& netlist n)
                (natp n)
                (3vp c)
                (true-listp a)
                (true-listp b)
                (equal n (len a))
                (equal n (len b)))
           (equal (se (si 'ripple-adder n)
                      (cons c (append a b))
                      sts
                      netlist)
                  (fv-adder c a b)))
  :hints (("Goal"
           :do-not '(preprocess)
           :expand (se (si 'ripple-adder n)
                       (cons c (append a b))
                       sts
                       netlist)
           :in-theory (e/d* (de-rules
                             ripple-adder&
                             not-primp-ripple-adder)
                            (de-module-disabled-rules)))))

(defthm ripple-adder$value-correct
  (implies (and (ripple-adder& netlist n)
                (natp n)
                (equal n (len a))
                (booleanp c)
                (bv2p a b))
           (equal (v-to-nat
                   (se (si 'ripple-adder n)
                       (cons c (append a b))
                       sts
                       netlist))
                  (+ (bool->bit c)
                     (v-to-nat a)
                     (v-to-nat b))))
  :hints (("Goal" :in-theory (enable bool->bit))))

(in-theory (disable ripple-adder$value
                    ripple-adder$value-correct))
