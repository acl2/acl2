;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "de")
(include-book "tree-number")

(local (include-book "arithmetic-5/top" :dir :system))

;; ======================================================================

;; TV-IF is a vector multiplexor which buffers the control line according to
;; the TREE argument.  Buffers are inserted whenever a tree has ((TREE-HEIGHT
;; tree) modulo 3) = 0.

;; This generator creates modules which are to be used as in this sample module
;; occurence, where n = (tree-size tree):

;; (LIST <occurence-name>
;;       <output list (n elements)>
;;       (SI 'TV-IF (TREE-NUMBER tree))
;;       (CONS <control signal>
;;             <A input bus (n elements)>
;;             <B input bus (n elements)>))

;; The predicate is (TV-IF& tree), and the netlist is (TV-IF$NETLIST tree).

;; For a balanced tree of n leaves, use tree = (MAKE-TREE n).

(defun tv-if-body (tree)
  (declare (xargs :guard (listp tree)))
  (let ((a-names (sis 'a 0 (tree-size tree)))
        (b-names (sis 'b 0 (tree-size tree)))
        (out-names (sis 'out 0 (tree-size tree))))
    (let ((left-a-names (tfirstn a-names tree))
          (right-a-names (trestn a-names tree))
          (left-b-names (tfirstn b-names tree))
          (right-b-names (trestn b-names tree))
          (left-out-names (tfirstn out-names tree))
          (right-out-names (trestn out-names tree)))
      (if (atom tree)
          (list
           (list 'leaf
                 (list (si 'out 0))
                 'b-if
                 (list 'c (si 'a 0) (si 'b 0))))
        ;; The control line is heuristically buffered.
        (let ((buffer? (zp (mod (tree-height tree) 3))))
          (let ((c-name (if buffer? 'c-buf 'c)))
            (append
             ;; The buffer.
             (if buffer?
                 '((c-buf (c-buf) b-buf (c)))
               nil)
             (list
              ;; The LHS tree.
              (list 'left
                    left-out-names
                    (si 'tv-if (tree-number (car tree)))
                    (cons c-name (append left-a-names left-b-names)))
              ;; The RHS tree.
              (list 'right
                    right-out-names
                    (si 'tv-if (tree-number (cdr tree)))
                    (cons c-name (append right-a-names right-b-names)))))))))))

(module-generator
 tv-if* (tree)
 ;; Name
 (si 'tv-if (tree-number tree))
 ;; Inputs
 (cons 'c (append (sis 'a 0 (tree-size tree))
                  (sis 'b 0 (tree-size tree))))
 ;; Outputs
 (sis 'out 0 (tree-size tree))
 ;; States
 nil
 ;; Occurrences
 (tv-if-body tree)
 (declare (xargs :guard (listp tree))))

(defund tv-if$netlist (tree)
  (declare (xargs :guard (tv-guard tree)))
  (if (atom tree)
      (list (tv-if* tree))
    (cons (tv-if* tree)
          (union$ (tv-if$netlist (car tree))
                  (tv-if$netlist (cdr tree))
                  :test 'equal))))

;; Note that both the netlist generator and the netlist predicate are
;; recursive.

(defund tv-if& (netlist tree)
  (declare (xargs :guard (and (alistp netlist)
                              (tv-guard tree))))
  (if (atom tree)
      (equal (assoc (si 'tv-if (tree-number tree)) netlist)
             (tv-if* tree))
    (and (equal (assoc (si 'tv-if (tree-number tree)) netlist)
                (tv-if* tree))
         (tv-if& (delete-to-eq (si 'tv-if (tree-number tree)) netlist)
                 (car tree))
         (tv-if& (delete-to-eq (si 'tv-if (tree-number tree)) netlist)
                 (cdr tree)))))

;; Sanity check

(local
 (defthmd check-tv-if$netlist-64
   (and (net-syntax-okp (tv-if$netlist (make-tree 64)))
        (net-arity-okp (tv-if$netlist (make-tree 64)))
        (tv-if& (tv-if$netlist (make-tree 64))
                (make-tree 64)))))

;; The proofs require this special induction scheme.

(defun tv-if-induction (tree n c a b st netlist)
  (if (atom tree)
      (list n c a b st netlist)
    (and
     (tv-if-induction
      (car tree)
      (tree-number (car tree))
      c
      (tfirstn a tree)
      (tfirstn b tree)
      nil
      (delete-to-eq (si 'tv-if (tree-number tree)) netlist))
     (tv-if-induction
      (car tree)
      (tree-number (car tree))
      *x*
      (tfirstn a tree)
      (tfirstn b tree)
      nil
      (delete-to-eq (si 'tv-if (tree-number tree)) netlist))
     (tv-if-induction
      (cdr tree)
      (tree-number (cdr tree))
      c
      (trestn a tree)
      (trestn b tree)
      nil
      (delete-to-eq (si 'tv-if (tree-number tree)) netlist))
     (tv-if-induction
      (cdr tree)
      (tree-number (cdr tree))
      *x*
      (trestn a tree)
      (trestn b tree)
      nil
      (delete-to-eq (si 'tv-if (tree-number tree)) netlist)))))

;; This lemma is necessary to force consideration of the output vector as an
;; APPEND of two sublists, based on the tree specification.  Expressions such
;; as this would normally be rewritten the other way.

;; (defthmd tv-if-lemma-crock
;;   (implies (<= (tree-size (car tree))
;;                (nfix n))
;;            (equal (assoc-eq-values (sis 'out 0 n)
;;                                    alist)
;;                   (append (assoc-eq-values (take (tree-size (car tree))
;;                                                  (sis 'out 0 n))
;;                                            alist)
;;                           (assoc-eq-values (nthcdr (tree-size (car tree))
;;                                                    (sis 'out 0 n))
;;                                            alist))))
;;   :hints (("Goal"
;;            :use (:instance assoc-eq-values-splitting-crock
;;                            (l (sis 'out 0 n))
;;                            (n (tree-size (car tree)))))))

(local
 (defthm cdr-append-singleton
   (implies (equal (len x) 1)
            (equal (cdr (append x y))
                   y))
   :hints (("Goal"
            :expand (append (cdr x) y)))))

(local
 (defthm tv-if$value-aux
   (implies (and (no-duplicatesp keys)
                 (true-listp x)
                 (true-listp y)
                 (equal (len keys)
                        (+ (len x) (len y)))
                 (equal i
                        (len y))
                 (<= i (len keys)))
            (equal
             (assoc-eq-values keys
                              (append (pairlis$ (nthcdr i keys)
                                                x)
                                      (pairlis$ (take i keys)
                                                y)
                                      z))
             (append y x)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable assoc-eq-values-splitting-crock)
            :use (:instance assoc-eq-values-splitting-crock
                            (n i)
                            (l keys)
                            (alist (append (pairlis$ (nthcdr i keys)
                                                     x)
                                           (pairlis$ (take i keys)
                                                     y)
                                           z)))))))

(defthm tv-if$value
  (implies (and (tv-if& netlist tree)
                (equal n (tree-number tree))
                (true-listp a) (true-listp b)
                (equal (len a) (tree-size tree))
                (equal (len b) (tree-size tree)))
           (equal (se (si 'tv-if n)
                      (cons c (append a b))
                      st
                      netlist)
                  (fv-if c a b)))
  :hints (("Goal"
           :induct (tv-if-induction tree n c a b st netlist)
           :expand (:free (inputs n)
                          (se (si 'tv-if n) inputs st netlist))
           :in-theory (e/d (de-rules
                            tv-if&
                            tv-if*$destructure
                            f-if
                            tree-size
                            open-v-threefix
                            fv-if-rewrite)
                           (not
                            3v-fix
                            de-module-disabled-rules)))))



