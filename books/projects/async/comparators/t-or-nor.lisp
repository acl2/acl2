;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

;; A tree based, reducing OR-NOR

(in-package "ADE")

(include-book "../de")
(include-book "../tree-number")

;; ======================================================================

(defun t-or-nor-body (tree parity)
  (declare (xargs :guard (listp tree)))
  (let ((a-names (sis 'a 0 (tree-size tree))))
    (let ((left-a-names (tfirstn a-names tree))
          (right-a-names (trestn a-names tree)))
      (if (atom tree)
          (list (list 'leaf
                      (list 'out)
                      (if parity 'b-not 'b-buf)
                      (list (si 'a 0))))

        (if (and (atom (car tree))
                 (atom (cdr tree)))
            (list (list 'leaf
                        (list 'out)
                        (if parity 'b-nor 'b-or)
                        (list (si 'a 0) (si 'a 1))))
          (list
           ;;  The LHS tree.
           (list 'left
                 (list 'left-out)
                 (si (if parity 't-or 't-nor) (tree-number (car tree)))
                 left-a-names)
           ;;  The RHS tree.
           (list 'right
                 (list 'right-out)
                 (si (if parity 't-or 't-nor) (tree-number (cdr tree)))
                 right-a-names)
           (list 'output
                 (list 'out)
                 (if parity 'b-nor 'b-nand)
                 (list 'left-out 'right-out))))))))

(module-generator
 t-or-nor* (tree parity)
 ;; Name
 (si (if parity 't-nor 't-or) (tree-number tree))
 ;; Inputs
 (sis 'a 0 (tree-size tree))
 ;; Outputs
 (list 'out)
 ;; States
 nil
 ;; Occurrences
 (t-or-nor-body tree parity)
 (declare (xargs :guard (listp tree))))

(defund t-or-nor$netlist (tree parity)
  (declare (xargs :guard (tv-guard tree)))
  (if (or (atom tree)
          (and (atom (car tree))
               (atom (cdr tree))))
      (list (t-or-nor* tree parity))
    (cons (t-or-nor* tree parity)
          (union$ (t-or-nor$netlist (car tree) (not parity))
                  (t-or-nor$netlist (cdr tree) (not parity))
                  :test 'equal))))

(defund t-or-nor& (netlist tree parity)
  (declare (xargs :guard (and (alistp netlist)
                              (tv-guard tree))))
  (let ((delete-result (delete-to-eq (si (if parity 't-nor 't-or)
                                         (tree-number tree))
                                     netlist))
        (lookup-okp (equal (assoc (si (if parity 't-nor 't-or)
                                      (tree-number tree))
                                  netlist)
                           (t-or-nor* tree parity))))

    (if (or (atom tree)
            (and (atom (car tree))
                 (atom (cdr tree))))
        lookup-okp
      (and lookup-okp
           (t-or-nor& delete-result (car tree) (not parity))
           (t-or-nor& delete-result (cdr tree) (not parity))))))

(defun t-or-nor-induction (tree parity call-name a st netlist)
  (if (or (atom tree)
          (and (atom (car tree))
               (atom (cdr tree))))
      (list call-name a st netlist)
    (and (t-or-nor-induction (car tree)
                             (not parity)
                             (if (not parity) 't-nor 't-or)
                             (tfirstn a tree)
                             nil
                             (delete-to-eq (si (if parity 't-nor 't-or)
                                               (tree-number tree))
                                           netlist))
         (t-or-nor-induction (cdr tree)
                             (not parity)
                             (if (not parity) 't-nor 't-or)
                             (trestn a tree)
                             nil
                             (delete-to-eq (si (if parity 't-nor 't-or)
                                               (tree-number tree))
                                           netlist)))))

(defund tr-or-nor (a parity tree)
  (declare (xargs :measure (acl2-count tree)
                  :guard (and (true-listp a)
                              (tv-guard tree))))
  (if (atom tree)
      (if parity (f-not (car a)) (f-buf (car a)))
    (if (and (atom (car tree))
             (atom (cdr tree)))
        (if parity
            (f-nor (car a) (cadr a))
          (f-or (car a) (cadr a)))
      (if parity
          (f-nor (tr-or-nor (tfirstn a tree) (not parity) (car tree))
                 (tr-or-nor (trestn a tree) (not parity) (cdr tree)))
        (f-nand (tr-or-nor (tfirstn a tree) (not parity) (car tree))
                (tr-or-nor (trestn a tree) (not parity) (cdr tree)))))))

(local
 (defthm tr-or-nor-of-v-threefix-canceled-aux
   (implies (not (booleanp (car (v-threefix x))))
            (not (booleanp (car x))))))

(defthm tr-or-nor-of-v-threefix-canceled
  (equal (tr-or-nor (v-threefix a) parity tree)
         (tr-or-nor a parity tree))
  :hints (("Goal" :in-theory (enable f-or
                                     f-nor
                                     f-not
                                     tr-or-nor))))

(not-primp-lemma t-or)
(not-primp-lemma t-nor)

(defthm t-or-nor$value
  (implies (and (t-or-nor& netlist tree parity)
                (equal call-name (if parity 't-nor 't-or))
                (true-listp a)
                (equal (len a) (tree-size tree)))
           (equal (se (si call-name (tree-number tree))
                      a st netlist)
                  (list (tr-or-nor a parity tree))))
  :hints (("Goal"
           :induct (t-or-nor-induction tree parity call-name a st netlist)
           :in-theory (e/d (de-rules
                            open-se
                            t-or-nor&
                            t-or-nor*$destructure
                            tr-or-nor
                            tree-size)
                           (de-module-disabled-rules)))))

(defund btr-or-nor (a parity tree)
  (declare (xargs :measure (acl2-count tree)
                  :guard (and (true-listp a)
                              (tv-guard tree))))
  (if (atom tree)
      (if parity (b-not (car a)) (b-buf (car a)))
    (if (and (atom (car tree))
             (atom (cdr tree)))
        (if parity
            (b-nor (car a) (cadr a))
          (b-or (car a) (cadr a)))
      (if parity
          (b-nor (btr-or-nor (tfirstn a tree) (not parity) (car tree))
                 (btr-or-nor (trestn a tree) (not parity) (cdr tree)))
        (b-nand (btr-or-nor (tfirstn a tree) (not parity) (car tree))
                (btr-or-nor (trestn a tree) (not parity) (cdr tree)))))))

(defthm tr-or-nor=btr-or-nor
  (implies (bvp a)
           (equal (tr-or-nor a parity tree)
                  (btr-or-nor a parity tree)))
  :hints (("Goal"
           :in-theory (enable bvp tr-or-nor btr-or-nor))))

(defthm btr-or-nor-is-v-zp-nzp
  (implies (and (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (btr-or-nor a parity tree)
                  (if parity
                      (v-zp a)
                    (v-nzp a))))
  :hints (("Goal"
           :in-theory (enable btr-or-nor
                              tree-size
                              bvp
                              v-zp
                              v-nzp))))

;; ======================================================================

;; TV-ZP* tree

;; A zero-detector module built from T-OR-NOR*.  The choice of implementation
;; is optimized for balanced trees.

(module-generator
 tv-zp* (tree)
 ;; Name
 (si 'tv-zp (tree-number tree))
 ;; Inputs
 (sis 'in 0 (tree-size tree))
 ;; Output
 '(out)
 ;; States
 nil
 ;; Body
 (if (equal (mod (tree-height tree) 2) 1)
     (list
      (list 'g0
            '(out-)
            (si 't-or (tree-number tree))
            (sis 'in 0 (tree-size tree)))
      (list 'g1 '(out)  'b-not '(out-)))
   (list
    (list 'g0
          '(out)
          (si 't-nor (tree-number tree))
          (sis 'in 0 (tree-size tree)))))
 (declare (xargs :guard t)))

(defund tv-zp$netlist (tree)
  (declare (xargs :guard (tv-guard tree)))
  (let ((odd-height (equal (mod (tree-height tree) 2) 1)))
    (cons (tv-zp* tree)
          (t-or-nor$netlist tree (not odd-height)))))

(defund tv-zp& (netlist tree)
  (declare (xargs :guard (and (alistp netlist)
                              (tv-guard tree))))
  (b* ((odd-height (equal (mod (tree-height tree) 2) 1))
       (subnetlist (delete-to-eq (si 'tv-zp (tree-number tree)) netlist)))
    (and (equal (assoc (si 'tv-zp (tree-number tree)) netlist)
                (tv-zp* tree))
         (t-or-nor& subnetlist tree (not odd-height)))))

(defund f$tv-zp (a tree)
  (declare (xargs :guard (and (true-listp a)
                              (tv-guard tree))))
  (let ((odd-height (equal (mod (tree-height tree) 2) 1)))
    (if odd-height
        (f-not (tr-or-nor a nil tree))
      (tr-or-nor a t tree))))

(defthm tv-zp$value
  (implies (and (tv-zp& netlist tree)
                (equal (len a) (tree-size tree))
                (true-listp a))
           (equal (se (si 'tv-zp (tree-number tree)) a st netlist)
                  (list (f$tv-zp a tree))))
  :hints (("Goal"
           :expand (:free (n)
                          (se (si 'tv-zp n)
                              a
                              st
                              netlist))
           :in-theory (e/d (de-rules
                            tv-zp&
                            tv-zp*$destructure
                            f$tv-zp)
                           (de-module-disabled-rules)))))

(defthm f$tv-zp=v-zp
  (implies (and (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (f$tv-zp a tree)
                  (v-zp a)))
  :hints (("Goal" :in-theory (enable f$tv-zp v-zp))))
