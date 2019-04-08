;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

;; An n-bit equality circuit -- An XOR vector and a zero detector.

(in-package "ADE")

(include-book "t-or-nor")
(include-book "../vector-module")

;; ======================================================================

(module-generator
 v-equal* (n)
 (si 'v-equal n)
 (append (sis 'A 0 n) (sis 'B 0 n))
 '(EQUAL)
 nil
 (list
  (list 'G0
        (sis 'X 0 n)
        (si 'V-XOR n)
        (append (sis 'A 0 n) (sis 'B 0 n)))
  (list 'G1
        '(EQUAL)
        (si 'TV-ZP (tree-number (make-tree n)))
        (sis 'X 0 n)))
 (declare (xargs :guard (natp n))))

(defund v-equal$netlist (n)
  (declare (xargs :guard (natp n)))
  (cons (v-equal* n)
        (union$ (v-xor$netlist n)
                (tv-zp$netlist (make-tree n))
                :test 'equal)))

(defund v-equal& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n))))
  (b* ((subnetlist (delete-to-eq (si 'V-EQUAL n) netlist)))
    (and (equal (assoc (si 'V-EQUAL n) netlist)
                (v-equal* n))
         (v-xor& subnetlist n)
         (tv-zp& subnetlist (make-tree n)))))

(defund f$v-equal (a b)
  (f$tv-zp (fv-xor a b) (make-tree (len a))))

(defthm f$v-equal-of-v-threefix-canceled
 (and (equal (f$v-equal (v-threefix a) b)
             (f$v-equal a b))
      (equal (f$v-equal a (v-threefix b))
             (f$v-equal a b)))
 :hints (("Goal" :in-theory (enable f$v-equal))))

(defthm v-equal$value
  (implies (and (v-equal& netlist n)
                (< 0 n)
                (true-listp a) (true-listp b)
                (equal (len a) n)
                (equal (len b) n))
           (equal (se (si 'v-equal n) (append a b) st netlist)
                  (list (f$v-equal a b))))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'v-equal n) inputs st netlist))
           :in-theory (e/d (de-rules
                            v-equal&
                            v-equal*$destructure
                            f$v-equal)
                           (de-module-disabled-rules)))))

(defthm f$v-equal=equal*
  (implies (and (< 0 (len a))
                (bvp a)
                (bvp b)
                (equal (len a) (len b)))
           (equal (f$v-equal a b)
                  (equal a b)))
  :hints (("Goal" :in-theory (enable v-zp f$v-equal))))
