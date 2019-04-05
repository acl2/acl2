;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;;  January 2019

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

(module-generator
 ripple-add/sub* (n)
 (si 'ripple-add/sub n)          ; Name
 (cons (si 'carry 0)             ; Inputs are
       (append (sis 'a 0 n)      ; (carry_0 a_0    a_1    ... a_n-1
               (sis 'b-in 0 n))) ;          b-in_0 b-in_1 ... b-in_n-1)
 (append (sis 'sum 0 n)          ; Outputs are
         (list (si 'carry n)))   ; (sum_0 sum_1 ... sum_n-1 carry_n)
 ()                              ; State
 (ripple-add/sub-body 0 n)       ; Occurrences
 (declare (xargs :guard (natp n))))

(defund ripple-add/sub$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (ripple-add/sub* n)
        *full-adder*))

(defund ripple-add/sub& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'ripple-add/sub n) netlist)
              (ripple-add/sub* n))
       (full-adder& (delete-to-eq (si 'ripple-add/sub n)
                                  netlist))))

(local
 (defthmd check-ripple-add/sub$netlist-64
   (and (net-syntax-okp (ripple-add/sub$netlist 64))
        (net-arity-okp (ripple-add/sub$netlist 64))
        (ripple-add/sub& (ripple-add/sub$netlist 64) 64))))

(defun ripple-add/sub-body-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      wire-alist
    (ripple-add/sub-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 3
                      (ripple-add/sub-body m n)
                      wire-alist
                      st-alist
                      netlist)
     st-alist
     netlist)))

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
                 (equal m+n (+ m n))
                 (equal (assoc-eq-value (si 'carry 0) wire-alist)
                        NIL) ;; Add
                 (3vp (assoc-eq-value (si 'carry m) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum m n)
                                            (list (si 'carry m+n)))
                                    (se-occ (ripple-add/sub-body m n)
                                            wire-alist
                                            st-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (assoc-eq-values (sis 'b-in m n) wire-alist))))
   :hints (("Goal"
            :induct (ripple-add/sub-body-induct m n
                                                wire-alist st-alist
                                                netlist)
            :in-theory (e/d* (de-rules
                              fv-adder
                              sis)
                             ((si)))))))

(local
 (defthm ripple-add/sub-body$value-2
   (implies (and (full-adder& netlist)
                 (natp m)
                 (natp n)
                 (equal m+n (+ m n))
                 (equal (assoc-eq-value (si 'carry 0) wire-alist)
                        T) ;; Sub
                 (3vp (assoc-eq-value (si 'carry m) wire-alist)))
            (equal (assoc-eq-values (append (sis 'sum m n)
                                            (list (si 'carry m+n)))
                                    (se-occ (ripple-add/sub-body m n)
                                            wire-alist
                                            st-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (fv-not
                     (assoc-eq-values (sis 'b-in m n) wire-alist)))))
   :hints (("Goal"
            :induct (ripple-add/sub-body-induct m n
                                                wire-alist st-alist
                                                netlist)
            :in-theory (e/d* (de-rules
                              fv-adder
                              fv-not
                              sis)
                             ((si)))))))

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
                                            st-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (assoc-eq-values (sis 'b-in 0 n) wire-alist))))))

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
                                            st-alist
                                            netlist))
                   (fv-adder
                    (assoc-eq-value (si 'carry 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (fv-not
                     (assoc-eq-values (sis 'b-in 0 n) wire-alist)))))))

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
                      st
                      netlist)
                  (fv-adder nil a b)))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'ripple-add/sub n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             ripple-add/sub&
                             ripple-add/sub*$destructure)
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
                      st
                      netlist)
                  (fv-adder t a (fv-not b))))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'ripple-add/sub n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             ripple-add/sub&
                             ripple-add/sub*$destructure)
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

  (local
   (defthm v-to-nat-of-repeat-nil-is-zero
     (equal (v-to-nat (repeat n nil)) 0)
     :hints (("Goal" :in-theory (enable v-to-nat repeat)))))

  (local
   (defthm v-to-nat-of-take
     (implies (<= 0 n)
              (equal (v-to-nat (take n l))
                     (- (v-to-nat l)
                        (* (expt 2 n) (v-to-nat (nthcdr n l))))))
     :hints (("Goal" :in-theory (enable bvp v-to-nat)))))

  (local
   (defun nthcdr-v-adder-sub-induct (n c a b)
     (if (zp n)
         (list c a b)
       (nthcdr-v-adder-sub-induct (1- n)
                                  (b-or3 (b-and (car a) (not (car b)))
                                         (b-and (car a) c)
                                         (b-and (not (car b)) c))
                                  (cdr a)
                                  (cdr b)))))

  (local
   (defthm nthcdr-v-adder-sub-1
     (implies (and (natp n)
                   (booleanp c)
                   (equal n (len a))
                   (equal (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (nthcdr n (v-adder c a (v-not b)))
                     (list c)))
     :hints (("Goal"
              :in-theory (enable bvp v-adder v-not)))))

  (local
   (defthm nthcdr-v-adder-sub-2
     (implies (and (natp n)
                   (booleanp c)
                   (equal n (len a))
                   (< (v-to-nat b) (v-to-nat a))
                   (bv2p a b))
              (equal (nthcdr n (v-adder c a (v-not b)))
                     (list t)))
     :hints (("Goal"
              :induct (nthcdr-v-adder-sub-induct n c a b)
              :in-theory (enable bvp v-adder v-to-nat v-not)))))

  (defthm v-to-nat-of-take-of-v-adder-sub
    (implies (and (natp n)
                  (equal n (len a))
                  (<= (v-to-nat b) (v-to-nat a))
                  (bv2p a b))
             (equal (v-to-nat (v-adder-output t a (v-not b)))
                    (- (v-to-nat a)
                       (v-to-nat b))))
    :hints (("Goal"
             :in-theory (enable v-adder-output)
             :use (:instance nthcdr-v-adder-sub-2
                             (c t)))))

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
                       st
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
                               st
                               netlist)))
                  (logext n (- (v-to-nat a) (v-to-nat b)))))
  :hints (("Goal" :in-theory (disable logext
                                      v-adder-works
                                      v-adder-sub-works))))
