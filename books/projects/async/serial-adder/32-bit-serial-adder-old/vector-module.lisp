;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

;; Automatic definition and proofs for simple linear vector modules of
;; primitives or other modules.  VECTOR-MODULE is defined in
;; "vector-macros.lisp".

(in-package "ADE")

(include-book "unbound")
(include-book "../../vector-macros")

;; ======================================================================

;; VECTOR-MODULE-INDUCTION
;; The induction scheme for vector modules.

(defun vector-module-induction (body m n wire-alist st-alist netlist)
  (if (zp n)
      (list body m wire-alist st-alist netlist)
    (vector-module-induction
     (cdr body)
     (1+ m)
     (1- n)
     (se-occ-bindings 1 body wire-alist st-alist netlist)
     st-alist
     netlist)))

;; V-BUF
;; V-NOT
;; V-AND
;; V-OR
;; V-XOR
;; V-PULLUP
;; VFT-WIRE

(vector-module v-buf (g (y) b-buf (a)) ((v-threefix a)))

(vector-module v-not (g (y) b-not (a)) ((fv-not a)) :enable (fv-not))

(vector-module v-and (g (y) b-and (a b)) ((fv-and a b)) :enable (fv-and))

(vector-module v-or (g (y) b-or (a b)) ((fv-or a b)) :enable (fv-or))

(vector-module v-xor (g (y) b-xor (a b)) ((fv-xor a b)) :enable (fv-xor))

(vector-module v-pullup (g (y) pullup (a)) ((v-pullup a)) :enable (v-pullup))

(vector-module vft-wire (g (y) t-wire (a b)) ((vft-wire a b))
               :enable (vft-wire))

;; V-WIRE

(defun v-wire-body (m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (if (zp n)
      nil
    (cons (list (si 'g m)
                (list (si 'y m))
                'wire
                (list (si 'a m)))
          (v-wire-body (1+ m) (1- n)))))

(module-generator
 v-wire* (n)
 (si 'v-wire n)
 (sis 'a 0 n)
 (sis 'y 0 n)
 nil
 (v-wire-body 0 n)
 (declare (xargs :guard (natp n))))

(defund v-wire& (netlist n)
  (declare (xargs :guard (and (alistp netlist) (natp n))))
  (equal (assoc (si 'v-wire n) netlist)
         (v-wire* n)))

(defund v-wire$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (v-wire* n)))

(local
 (defthm v-wire$unbound-in-body
   (implies (and (natp l) (natp m) (< l m))
            (unbound-in-body (si 'y l)
                             (v-wire-body m n)))
   :hints (("Goal" :in-theory (enable occ-outs)))))

(local
 (defthm v-wire-body$value
   (implies
    (and (natp m)
         (equal body (v-wire-body m n)))
    (equal (assoc-eq-values (sis 'y m n)
                            (se-occ body wire-alist st-alist netlist))
           (assoc-eq-values (sis 'a m n)
                            wire-alist)))
   :hints (("Goal"
            :induct (vector-module-induction
                     body m n wire-alist st-alist netlist)
            :in-theory (enable de-rules sis)))))

(defthm v-wire$value
  (implies (and (v-wire& netlist n)
                (true-listp a)
                (equal (len a) n))
           (equal (se (si 'v-wire n) a st netlist)
                  a))
  :hints (("Goal"
           :expand (:free (n)
                          (se (si 'v-wire n) a st netlist))
           :in-theory (enable de-rules v-wire& v-wire*$destructure))))

;; V-IF

(defun v-if-body (m n)
  (declare (xargs :guard (and (natp m) (natp n))))
  (if (zp n)
      nil
    (cons (list (si 'g m)
                (list (si 'y m))
                'b-if
                (list 'c (si 'a m) (si 'b m)))
          (v-if-body (1+ m) (1- n)))))

(module-generator
 v-if* (n)
 (si 'v-if n)
 (cons 'c
       (append (sis 'a 0 n) (sis 'b 0 n)))
 (sis 'y 0 n)
 nil
 (v-if-body 0 n)
 (declare (xargs :guard (natp n))))

(defund v-if& (netlist n)
  (declare (xargs :guard (and (alistp netlist) (natp n))))
  (equal (assoc (si 'v-if n) netlist)
         (v-if* n)))

(defund v-if$netlist (n)
  (declare (xargs :guard (natp n)))
  (list (v-if* n)))

(local
 (defthm v-if$unbound-in-body
   (implies (and (natp l) (natp m) (< l m))
            (unbound-in-body (si 'y l)
                             (v-if-body m n)))
   :hints (("Goal" :in-theory (enable occ-outs)))))

(local
 (defthm v-if-body$value
   (implies
    (and (natp m)
         (equal body (v-if-body m n)))
    (equal (assoc-eq-values (sis 'y m n)
                            (se-occ body wire-alist st-alist netlist))
           (fv-if (assoc-eq-value 'c wire-alist)
                  (assoc-eq-values (sis 'a m n) wire-alist)
                  (assoc-eq-values (sis 'b m n) wire-alist))))
   :hints (("Goal"
            :induct (vector-module-induction
                     body m n wire-alist st-alist netlist)
            :in-theory (enable de-rules sis fv-if)))))

(defthm v-if$value
  (implies (and (v-if& netlist n)
                (true-listp a) (equal (len a) n)
                (true-listp b) (equal (len b) n))
           (equal (se (si 'v-if n) (cons c (append a b)) st netlist)
                  (fv-if c a b)))
  :hints (("Goal"
           :expand (:free (inputs n)
                          (se (si 'v-if n) inputs st netlist))
           :in-theory (enable de-rules v-if& v-if*$destructure))))
