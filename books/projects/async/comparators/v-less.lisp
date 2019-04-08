;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2018

;; An n-bit, big-endian "less than" comparator

(in-package "ADE")

(include-book "../unbound")

;; ======================================================================

(module-generator
 1-bit-<* ()
 '1-bit-<
 '(ind-in flag-in a b)
 '(ind-out flag-out)
 ()
 '((xnor (x) b-xnor (a b))
   (f (flag-out) b-and (x flag-in))
   (neg (a~) b-not (a))
   (g (c) b-and3 (flag-in a~ b))
   (h (ind-out) b-or (c ind-in)))
 (declare (xargs :guard t)))

(defund 1-bit-<$netlist ()
  (declare (xargs :guard t))
  (list (1-bit-<*)))

(defund 1-bit-<& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc '1-bit-< netlist)
         (1-bit-<*)))

(local
 (defthmd check-1-bit-<$netlist
   (and (net-syntax-okp (1-bit-<$netlist))
        (net-arity-okp (1-bit-<$netlist))
        (1-bit-<& (1-bit-<$netlist)))))

(defthm 1-bit-<$value
  (implies (1-bit-<& netlist)
           (equal (se '1-bit-< (list ind-in flag-in a b) st netlist)
                  (list (f-or (f-and3 flag-in (f-not a) b)
                              ind-in)
                        (f-and (f-xnor a b) flag-in))))
  :hints (("Goal"
           :expand (:free (inputs)
                          (se '1-bit-< inputs st netlist))
           :in-theory (enable de-rules 1-bit-<&))))

;; ======================================================================

(defun fv-< (ind flag a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      (3v-fix ind)
    (fv-< (f-or (f-and3 flag (f-not (car a)) (car b))
                ind)
          (f-and (f-xnor (car a) (car b))
                 flag)
          (cdr a)
          (cdr b))))

(defthm 3v-fix-fv-<
  (equal (3v-fix (fv-< ind flag a b))
         (fv-< ind flag a b)))

(defthm fv-<-of-f-buf-canceled
  (and (equal (fv-< (f-buf ind) flag a b)
              (fv-< ind flag a b))
       (equal (fv-< ind (f-buf flag) a b)
              (fv-< ind flag a b))))

(defthm fv-<-of-v-threefix-canceled-1
  (equal (fv-< ind flag (v-threefix a) b)
         (fv-< ind flag a b))
  :hints (("Goal" :in-theory (enable 3vp f-gates))))

(defthm fv-<-of-v-threefix-canceled-2
  (equal (fv-< ind flag a (v-threefix b))
         (fv-< ind flag a b))
  :hints (("Goal" :in-theory (enable f-gates))))

(in-theory (disable fv-<))

(defun v-< (ind flag a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      (bool-fix ind)
    (v-< (b-or (b-and3 flag (b-not (car a)) (car b))
               ind)
         (b-and (b-xnor (car a) (car b))
                flag)
         (cdr a)
         (cdr b))))

(defthm booleanp-v-<
  (booleanp (v-< ind flag a b))
  :rule-classes :type-prescription)

(defthm fv-<=v-<
  (implies (and (booleanp ind)
                (booleanp flag)
                (bvp a)
                (bvp b))
           (equal (fv-< ind flag a b)
                  (v-< ind flag a b)))
  :hints (("Goal" :in-theory (enable bvp fv-<))))

(local
 (defthm v-<-lemma
   (and (implies ind
                 (equal (v-< ind flag a b) t))
        (implies (not flag)
                 (equal (v-< ind flag a b)
                        (bool-fix ind))))))

(local
 (defthm v-<-append
   (implies (bv2p x1 x2)
            (equal (v-< ind flag (append x1 y1) (append x2 y2))
                   (or (v-< ind flag x1 x2)
                       (and (equal x1 x2)
                            (v-< ind flag y1 y2)))))
   :hints (("Goal" :in-theory (enable bool-fix bvp)))))

;; (defthmd v-<-works
;;   (implies (and (bv2p a b)
;;                 (v-< ind flag (rev a) (rev b)))
;;            (or ind
;;                (< (v-to-nat a) (v-to-nat b))))
;;   :hints (("Goal"
;;            :induct (v-<-works-induct a b)
;;            :in-theory (enable bvp v-to-nat))))

;; (defthm v-<-correct
;;   (implies (and (bv2p a b)
;;                 (v-< nil t (rev a) (rev b)))
;;            (< (v-to-nat a) (v-to-nat b)))
;;   :hints (("Goal" :use (:instance v-<-works
;;                                   (ind nil)
;;                                   (flag t))))
;;   :rule-classes :linear)

(defun v-<-correct-induct (a b)
  (if (atom a)
      b
    (v-<-correct-induct (cdr a) (cdr b))))

(defthm v-<-correct-1
  (implies (and (bv2p a b)
                (v-< nil t (rev a) (rev b)))
           (< (v-to-nat a) (v-to-nat b)))
  :hints (("Goal"
           :induct (v-<-correct-induct a b)
           :in-theory (enable bvp v-to-nat)))
  :rule-classes (:rewrite :linear))

(defthm v-<-correct-2
  (implies (and (bv2p a b)
                (not (v-< nil t (rev a) (rev b))))
           (>= (v-to-nat a) (v-to-nat b)))
  :hints (("Goal"
           :induct (v-<-correct-induct a b)
           :in-theory (enable bvp v-to-nat)))
  :rule-classes (:rewrite :linear))

(in-theory (disable v-<))

(defun v-<-body (m n)
  (declare (xargs :guard (and (natp m)
                              (natp n))))
  ;; m is the current index and n is the number of occurrences.
  (if (zp n)
      nil
    (list*
     (list
      ;; occurrence name
      (si 'g m)
      ;; outputs
      (list (si 'ind (1+ m))
            (si 'flag (1+ m)))
      ;; inferior module reference
      '1-bit-<
      ;; inputs
      (list (si 'ind m)
            (si 'flag m)
            (si 'a m)
            (si 'b m)))

     (v-<-body (1+ m) (1- n)))))

(module-generator
 v-<* (n)
 (si 'v-< n)
 (append (sis 'a 0 n)
         (sis 'b 0 n))
 (list (si 'ind n))
 ()
 (list*
  (list 'ind-in (list (si 'ind 0)) 'vss ())
  (list 'flag-in (list (si 'flag 0)) 'vdd ())
  (v-<-body 0 n))
 (declare (xargs :guard (natp n))))

(defund v-<$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (v-<* n)
        (1-bit-<$netlist)))

(defund v-<& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (and (equal (assoc (si 'v-< n) netlist)
              (v-<* n))
       (1-bit-<& (delete-to-eq (si 'v-< n)
                               netlist))))

(local
 (defthmd check-v-<$netlist-64
   (and (net-syntax-okp (v-<$netlist 64))
        (net-arity-okp (v-<$netlist 64))
        (v-<& (v-<$netlist 64) 64))))

(defun v-<-body-induct (m n wire-alist st-alist netlist)
  (if (zp n)
      wire-alist
    (v-<-body-induct
     (1+ m)
     (1- n)
     (se-occ-bindings 1
                      (v-<-body m n)
                      wire-alist
                      st-alist
                      netlist)
     st-alist
     netlist)))

(local
 (defthm v-<-body$value
   (implies (and (1-bit-<& netlist)
                 (natp m)
                 (natp n)
                 (equal m+n (+ m n))
                 ;; We need the following hypothesis for the case of (zp n)
                 (3vp (assoc-eq-value (si 'ind m) wire-alist)))
            (equal (assoc-eq-value (si 'ind m+n)
                                   (se-occ (v-<-body m n)
                                           wire-alist
                                           st-alist
                                           netlist))
                   (fv-<
                    (assoc-eq-value (si 'ind m) wire-alist)
                    (assoc-eq-value (si 'flag m) wire-alist)
                    (assoc-eq-values (sis 'a m n) wire-alist)
                    (assoc-eq-values (sis 'b m n) wire-alist))))
   :hints (("Goal"
            :in-theory (enable de-rules
                               fv-<
                               sis)
            :induct (v-<-body-induct m n
                                     wire-alist
                                     st-alist
                                     netlist)))))

(local
 (defthm v-<-body$value-m=0
   (implies (and (1-bit-<& netlist)
                 (natp n)
                 (3vp (assoc-eq-value (si 'ind 0) wire-alist)))
            (equal (assoc-eq-value (si 'ind n)
                                   (se-occ (v-<-body 0 n)
                                           wire-alist
                                           st-alist
                                           netlist))
                   (fv-<
                    (assoc-eq-value (si 'ind 0) wire-alist)
                    (assoc-eq-value (si 'flag 0) wire-alist)
                    (assoc-eq-values (sis 'a 0 n) wire-alist)
                    (assoc-eq-values (sis 'b 0 n) wire-alist))))))

(defthm v-<$value
  (implies (and (v-<& netlist n)
                (natp n)
                (true-listp a)
                (true-listp b)
                (equal (len a) n)
                (equal (len b) n))
           (equal (se (si 'v-< n)
                      (append a b)
                      st
                      netlist)
                  (list (fv-< nil t a b))))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'v-< n) inputs st netlist))
           :in-theory (e/d* (de-rules
                             v-<&
                             v-<*$destructure)
                            (de-module-disabled-rules)))))
