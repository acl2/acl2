;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "adder")

(include-book "ihs/basic-definitions" :dir :system)

;; ======================================================================

;; RIPPLE-ADD/SUB-BODY

(defun ripple-add/sub-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  ;; m is the current index and n is the number of recursive calls.
  (if (zp n)
      nil
    (list*
     (list
      ;; occurrence name
      (si 'neg m)
      ;; outputs
      (list (si 'b-in~ m))
      ;; primitive reference
      'b-not
      ;; inputs
      (list (si 'b-in m)))

     (list
      ;; occurrence name
      (si 'mux m)
      ;; outputs
      (list (si 'b m))
      ;; primitive reference
      'b-if
      ;; inputs
      (list (si 'carry 0)
            (si 'b-in~ m)
            (si 'b-in m)))

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

     (ripple-add/sub-body (1+ m) (1- n)))))

(defun ripple-add/sub* (n)
  (declare (xargs :guard (natp n)))
  (list (si 'ripple-add/sub n)          ; ripple-add/sub_n
        (cons (si 'carry 0)             ; inputs are
              (append (sis 'a 0 n)      ; (carry_0 a_0    a_1    ... a_n-1
                      (sis 'b-in 0 n))) ;          b-in_0 b-in_1 ... b-in_n-1)
        (append (sis 'sum 0 n)          ; outputs are
                (list (si 'carry n)))   ; (sum_0 sum_1 ... sum_n-1 carry_n)
        nil                             ; no state
        (ripple-add/sub-body 0 n)))     ; occurrences

(defund ripple-add/sub& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'ripple-add/sub n) netlist)
              (ripple-add/sub* n))
       (full-adder& (delete-to-eq (si 'ripple-add/sub n)
                                  netlist))))

(defun ripple-add/sub$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (ripple-add/sub* n)
        *full-adder*))

(local
 (defthmd check-ripple-add/sub$netlist-64
   (and (net-syntax-okp (ripple-add/sub$netlist 64))
        (net-arity-okp (ripple-add/sub$netlist 64))
        (ripple-add/sub& (ripple-add/sub$netlist 64) 64))))

(local
 (defun ripple-add/sub-body-induct (m n wire-alist sts-alist netlist)
   (if (zp n)
       wire-alist
     (ripple-add/sub-body-induct
      (1+ m)
      (1- n)
      (se-occ-bindings 3
                       (ripple-add/sub-body m n)
                       wire-alist
                       sts-alist
                       netlist)
      sts-alist
      netlist))))

(local
 (defthm ripple-add/sub$unbound-in-body-sum
   (implies (and (natp k)
                 (natp m)
                 (< k m))
            (unbound-in-body (si 'sum k)
                             (ripple-add/sub-body m n)))
   :hints (("Goal" :in-theory (enable occ-outs)))))

(local
 (defthm ripple-add/sub-body$value-1
   (implies (and (full-adder& netlist)
                 (natp m)
                 (natp n)
                 (equal (assoc-eq-value (si 'carry 0) wire-alist)
                        NIL) ;; Add
                 (3vp (assoc-eq-value (si 'carry m) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum m n)
                                            (list (si 'carry (+ m n))))
                                    (se-occ (ripple-add/sub-body m n)
                                            wire-alist
                                            sts-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (assoc-eq-values (sis 'b-in m n) wire-alist))))
   :hints (("Goal"
            :in-theory (e/d* (de-rules
                              full-adder$value
                              fv-adder
                              sis)
                             ((si)))
            :induct (ripple-add/sub-body-induct m n
                                                wire-alist sts-alist
                                                netlist)))))

(local
 (defthm ripple-add/sub-body$value-2
   (implies (and (full-adder& netlist)
                 (natp m)
                 (natp n)
                 (equal (assoc-eq-value (si 'carry 0) wire-alist)
                        T) ;; Sub
                 (3vp (assoc-eq-value (si 'carry m) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum m n)
                                            (list (si 'carry (+ m n))))
                                    (se-occ (ripple-add/sub-body m n)
                                            wire-alist
                                            sts-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (fv-not
                     (assoc-eq-values (sis 'b-in m n) wire-alist)))))
   :hints (("Goal"
            :in-theory (e/d* (de-rules
                              full-adder$value
                              fv-adder
                              fv-not
                              sis)
                             ((si)))
            :induct (ripple-add/sub-body-induct m n
                                                wire-alist sts-alist
                                                netlist)))))

(local
 (defthm ripple-add/sub-body$value-m=0-1
   (implies (and (full-adder& netlist)
                 (natp n)
                 (equal (assoc-eq-value (si 'carry 0) wire-alist)
                        NIL)) ;; Add
            (equal (assoc-eq-values (append (sis 'sum 0 n)
                                            (list (si 'carry n)))
                                    (se-occ (ripple-add/sub-body 0 n)
                                            wire-alist
                                            sts-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (assoc-eq-values (sis 'b-in 0 n) wire-alist))))
   :hints (("Goal" :use (:instance ripple-add/sub-body$value-1
                                   (m 0))))))

(local
 (defthm ripple-add/sub-body$value-m=0-2
   (implies (and (full-adder& netlist)
                 (natp n)
                 (equal (assoc-eq-value (si 'carry 0) wire-alist)
                        T)) ;; Sub
            (equal (assoc-eq-values (append (sis 'sum 0 n)
                                            (list (si 'carry n)))
                                    (se-occ (ripple-add/sub-body 0 n)
                                            wire-alist
                                            sts-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (fv-not
                     (assoc-eq-values (sis 'b-in 0 n) wire-alist)))))
   :hints (("Goal" :use (:instance ripple-add/sub-body$value-2
                                   (m 0))))))

(not-primp-lemma ripple-add/sub)

(defthm ripple-add/sub$value-1
  (implies (and (ripple-add/sub& netlist n)
                (natp n)
                (equal c NIL) ;; Add
                (true-listp a)
                (true-listp b)
                (equal n (len a))
                (equal n (len b)))
           (equal (se (si 'ripple-add/sub n)
                      (cons c (append a b))
                      sts
                      netlist)
                  (fv-adder nil a b)))
  :hints (("Goal"
           :do-not '(preprocess)
           :expand (se (si 'ripple-add/sub n)
                       (cons c (append a b))
                       sts
                       netlist)
           :in-theory (e/d* (de-rules
                             ripple-add/sub&
                             not-primp-ripple-add/sub)
                            (de-module-disabled-rules)))))

(defthm ripple-add/sub$value-2
  (implies (and (ripple-add/sub& netlist n)
                (natp n)
                (equal c T) ;; Sub
                (true-listp a)
                (true-listp b)
                (equal n (len a))
                (equal n (len b)))
           (equal (se (si 'ripple-add/sub n)
                      (cons c (append a b))
                      sts
                      netlist)
                  (fv-adder t a (fv-not b))))
  :hints (("Goal"
           :do-not '(preprocess)
           :expand (se (si 'ripple-add/sub n)
                       (cons c (append a b))
                       sts
                       netlist)
           :in-theory (e/d* (de-rules
                             ripple-add/sub&
                             not-primp-ripple-add/sub)
                            (de-module-disabled-rules)))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (local
   (defthm ripple-adder-2-comp-sub-aux-1
     (implies (and (posp n)
                   (rationalp a)
                   (rationalp b))
              (equal (logext n
                             (+ a (- (expt 2 n) b)))
                     (logext n
                             (- a b))))))

  (local
   (set-default-hints
    '((nonlinearp-default-hint stable-under-simplificationp
                               hist pspv))))

  (local
   (defthm ripple-adder-2-comp-sub-aux-2
     (implies (bvp x)
              (equal (v-to-nat (v-not x))
                     (- (1- (expt 2 (len x)))
                        (v-to-nat x))))
     :hints (("Goal" :in-theory (enable bvp v-to-nat v-not)))))

  (defthm v-adder-sub-works
    (implies (bv2p a b)
             (equal (v-to-nat (v-adder c a (v-not b)))
                    (+ (if c 0 -1)
                       (expt 2 (len a))
                       (- (v-to-nat a)
                          (v-to-nat b))))))

  (defthm ripple-adder-2-comp-sub
    (implies (and (posp n)
                  (equal n (len a))
                  (bv2p a b))
             (equal (logext n (v-to-nat (v-adder t a (v-not b))))
                    (logext n (- (v-to-nat a) (v-to-nat b)))))
    :hints (("Goal"
             :in-theory (disable logext)
             :use (:instance ripple-adder-2-comp-sub-aux-1
                             (a (v-to-nat a))
                             (b (v-to-nat b))))))
  )

(defthm ripple-add/sub$value-correct-1
  (implies (and (ripple-add/sub& netlist n)
                (natp n)
                (equal n (len a))
                (equal c NIL) ;; Add
                (bv2p a b))
           (equal (v-to-nat
                   (se (si 'ripple-add/sub n)
                       (cons c (append a b))
                       sts
                       netlist))
                  (+ (v-to-nat a) (v-to-nat b)))))

(defthm ripple-add/sub$value-correct-2
  (implies (and (ripple-add/sub& netlist n)
                (posp n)    ;; n must be positive.
                (equal n (len a))
                (equal c T) ;; Sub
                (bv2p a b))
           (equal (logext n
                          (v-to-nat
                           (se (si 'ripple-add/sub n)
                               (cons c (append a b))
                               sts
                               netlist)))
                  (logext n (- (v-to-nat a) (v-to-nat b)))))
  :hints (("Goal" :in-theory (disable logext
                                      v-adder-works
                                      v-adder-sub-works))))

(in-theory (disable ripple-add/sub$value-1
                    ripple-add/sub$value-2
                    ripple-add/sub$value-correct-1
                    ripple-add/sub$value-correct-2))
