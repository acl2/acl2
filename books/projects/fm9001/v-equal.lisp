;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; An n-bit equality circuit -- An XOR vector and a zero detector.

(in-package "FM9001")

(include-book "t-or-nor")
(include-book "vector-module")

;; ======================================================================

(module-generator
 v-equal* (n)
 (si 'V-EQUAL n)
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
 :guard (natp n))

(defund v-equal& (netlist n)
  (and (equal (assoc (si 'V-EQUAL n) netlist)
              (v-equal* n))
       (let ((netlist (delete-to-eq (si 'V-EQUAL n) netlist)))
         (and (v-xor& netlist n)
              (tv-zp& netlist (make-tree n))))))

(defun v-equal$netlist (n)
  (cons (v-equal* n)
        (union$ (v-xor$netlist n)
                (tv-zp$netlist (make-tree n))
                :test 'equal)))

(defund f$v-equal (a b)
  (f$tv-zp (fv-xor a b) (make-tree (len a))))

(not-primp-lemma v-equal)

(defthmd v-equal$value
  (implies (and (v-equal& netlist n)
                (< 0 n)
                (true-listp a) (true-listp b)
                (equal (len a) n)
                (equal (len b) n))
           (equal (se (si 'V-EQUAL n) (append a b) sts netlist)
                  (list (f$v-equal a b))))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                            v-equal&
                            v-equal*$destructure
                            not-primp-v-equal
                            f$v-equal
                            v-xor$value
                            tv-zp$value)
                           (tv-disabled-rules)))))

(defthm f$v-equal=equal*
  (implies (and (< 0 (len a))
                (bvp a)
                (bvp b)
                (equal (len a) (len b)))
           (equal (f$v-equal a b)
                  (equal a b)))
  :hints (("Goal" :in-theory (enable v-zp f$v-equal))))
