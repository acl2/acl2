;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "unbound")

;; ======================================================================

;; HALF ADDER

(defconst *half-adder*
  '((half-adder
     (a b)
     (sum carry)
     ()
     ((g0 (sum)   b-xor (a b))
      (g1 (carry) b-and (a b))))))

(defund half-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc 'half-adder netlist)
         (car *half-adder*)))

(local
 (defthmd check-half-adder
   (and (net-syntax-okp *half-adder*)
        (net-arity-okp *half-adder*)
        (half-adder& *half-adder*))))

(defun half-adder$outputs (inputs st)
  (declare (ignorable st))
  (let ((a (car inputs))
        (b (cadr inputs)))
    (list (f-xor a b)
          (f-and a b))))

(defthm half-adder$value
  (implies (half-adder& netlist)
           (equal (se 'half-adder inputs st netlist)
                  (half-adder$outputs inputs st)))
  :hints (("Goal"
           :expand (se 'half-adder inputs st netlist)
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

(defund full-adder& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (equal (assoc 'full-adder netlist)
              (car *full-adder*))
       (half-adder& (delete-to-eq 'full-adder netlist))))

(local
 (defthmd check-full-adder
   (and (net-syntax-okp *full-adder*)
        (net-arity-okp *full-adder*)
        (full-adder& *full-adder*))))

(defun full-adder$outputs (inputs st)
  (declare (ignorable st))
  (let ((c (car inputs))
        (a (cadr inputs))
        (b (caddr inputs)))
    (list (f-xor3 c a b)
          (f-or (f-and a b)
                (f-and (f-xor a b) c)))))

(defthm full-adder$value
  (implies (full-adder& netlist)
           (equal (se 'full-adder inputs st netlist)
                  (full-adder$outputs inputs st)))
  :hints (("Goal"
           :expand (se 'full-adder inputs st netlist)
           :in-theory (enable de-rules
                              full-adder&
                              3vp
                              f-gates))))

;; ======================================================================

;; RIPPLE-CARRY ADDER

;; Ripple-carry adder body generator

(defun ripple-add-body (m n)
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

     (ripple-add-body (1+ m) (1- n)))))

(module-generator
 ripple-add* (n)
 (si 'ripple-add n)            ; Name
 (cons (si 'carry 0)           ; Inputs are
       (append (sis 'a 0 n)    ; (carry_0 a_0 a_1 ... a_n-1
               (sis 'b 0 n)))  ;          b_0 b_1 ... b_n-1)
 (append (sis 'sum 0 n)        ; Outputs are
         (list (si 'carry n))) ; (sum_0 sum_1 ... sum_n-1 carry_n)
 ()                            ; State
 (ripple-add-body 0 n)         ; Occurrences
 (declare (xargs :guard (natp n))))

(defund ripple-add$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (ripple-add* n)
        *full-adder*))

(defund ripple-add& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'ripple-add n) netlist)
              (ripple-add* n))
       (full-adder& (delete-to-eq (si 'ripple-add n)
                                  netlist))))

(local
 (defthmd check-ripple-add$netlist-64
   (and (net-syntax-okp (ripple-add$netlist 64))
        (net-arity-okp (ripple-add$netlist 64))
        (ripple-add& (ripple-add$netlist 64) 64))))

(defun ripple-add-body-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      wire-alist
    (ripple-add-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 1
                      (ripple-add-body m n)
                      wire-alist
                      st-alist
                      netlist)
     st-alist
     netlist)))

(local
 (defthm ripple-add$unbound-in-body-sum
   (implies (and (natp k)
                 (natp m)
                 (< k m))
            (unbound-in-body (si 'sum k)
                             (ripple-add-body m n)))
   :hints (("Goal" :in-theory (enable occ-outs)))))

(local
 (defthm ripple-add-body$value
   (implies (and (full-adder& netlist)
                 (natp m)
                 (natp n)
                 (equal m+n (+ m n))
                 ;; We need the following hypothesis for the case of (zp n)
                 (3vp (assoc-eq-value (si 'carry m) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum m n)
                                            (list (si 'carry m+n)))
                                    (se-occ (ripple-add-body m n)
                                            wire-alist
                                            st-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (assoc-eq-values (sis 'b m n) wire-alist))))
   :hints (("Goal"
           :induct (ripple-add-body-induct m n wire-alist st-alist netlist)
           :in-theory (enable de-rules
                              fv-adder
                              sis)))))

(local
 (defthm ripple-add-body$value-m=0
   (implies (and (full-adder& netlist)
                 (natp n)
                 (3vp (assoc-eq-value (si 'carry 0) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum 0 n)
                                            (list (si 'carry n)))
                                    (se-occ (ripple-add-body 0 n)
                                            wire-alist
                                            st-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (assoc-eq-values (sis 'b 0 n) wire-alist))))))

(defthm ripple-add$value
  (implies (and (ripple-add& netlist n)
                (natp n)
                (3vp c)
                (true-listp a)
                (true-listp b)
                (equal n (len a))
                (equal n (len b)))
           (equal (se (si 'ripple-add n)
                      (cons c (append a b))
                      st
                      netlist)
                  (fv-adder c a b)))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'ripple-add n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             ripple-add&
                             ripple-add*$destructure)
                            (de-module-disabled-rules)))))

(defthm ripple-add$value-correct
  (implies (and (ripple-add& netlist n)
                (natp n)
                (equal n (len a))
                (booleanp c)
                (bv2p a b))
           (equal (v-to-nat
                   (se (si 'ripple-add n)
                       (cons c (append a b))
                       st
                       netlist))
                  (+ (bool->bit c)
                     (v-to-nat a)
                     (v-to-nat b))))
  :hints (("Goal" :in-theory (enable bool->bit))))
