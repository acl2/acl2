#|

   Leftist Trees, Version 0.1
   Copyright (C) 2012 by Ben Selfridge <benself@cs.utexas.edu>

 leftist-tree-defthms.lisp

   This file contains the basic theory of leftist trees,
   proving the basic operations correct. 

   This implementation follows "Purely Functional Data
   Structures" by Chris Okasaki.

|#

(in-package "ACL2")
(include-book "leftist-tree-defuns")

;; We need this much arithmetic to prove theorems about the
;; rank of the tree.

(local (include-book "arithmetic-5/top" :dir :system))

(defdoc leftist-tree-thms
  ":doc-section leftist-trees
Useful theorems about leftist trees.~/~/
~/")

;;;;;;;;;;;;;;;;;;;
;; MISCELLANEOUS ;;
;;;;;;;;;;;;;;;;;;;

(defdoc leftist-tree-misc-thms
  ":doc-section leftist-tree-thms
Miscellaneous theorems~/~/
Includes proofs that the rank, length of right spine, and length of
the shortest path to an empty node are all equal. We also prove that
the rank and size of a tree are always natp, as this is helpful in
a later theorem.~/")

(defthm lrt-equals-rank-lt
  (implies (proper-lt tree)
           (equal (length-right-spine-lt tree)
                  (rank-lt tree)))
  :doc ":doc-section leftist-tree-misc-thms 
~/~/
(length-right-spine-lt tree) ==> (rank-lt tree)~/")

(defthm ltn-equals-rank-lt
  (implies (proper-lt tree)
           (equal (length-to-nil-lt tree)
                  (rank-lt tree)))
  :doc ":doc-section leftist-tree-misc-thms
~/~/
(length-to-nil-lt tree) ==> (rank-lt tree)~/")

(defthm member-insert-lt
  (implies (proper-lt tree)
           (member-lt x (insert-lt x tree)))
  :doc ":doc-section leftist-tree-misc-thms
~/~/
(proper-lt tree) ==> (member-lt x (insert-lt x tree))~/")

; rank and size are naturals
(defthm rank-is-natp-lt
  (implies (proper-lt tree)
           (natp (rank-lt tree)))
  :doc ":doc-section leftist-tree-misc-thms
~/~/
(proper-lt tree) ==> (natp (rank-lt tree))~/")

(defthm size-is-natp-lt
  (implies (proper-lt tree)
           (natp (size-lt tree)))
  :doc ":doc-section leftist-tree-misc-thms
~/~/
(proper-lt tree) ==> (natp (size-lt tree))~/")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BASIC OPERATIONS RESPECT STRUCTURE ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdoc leftist-tree-structure-thms
  ":doc-section leftist-tree-thms
Theorems proving that the basic operations respect PROPER-LT~/~/~/")

(local 
 (defthmd proper-merge-lt-L1
   (implies (and (consp right_tree1)
                 (consp tree2)
                 (proper-lt right_tree1)
                 (proper-lt tree2)
                 (lexorder x (root-lt right_tree1))
                 (lexorder x (root-lt tree2)))
            (lexorder x (root-lt (merge-lt right_tree1 tree2))))
   :hints (("Goal"
            :induct (merge-lt right_tree1 tree2)))))

(local
 (defthmd proper-merge-lt-L2
   (implies (and (consp tree1)
                 (consp right_tree2)
                 (proper-lt tree1)
                 (proper-lt right_tree2)
                 (not (lexorder (root-lt tree1) x))
                 (lexorder x (root-lt right_tree2)))
            (lexorder x (root-lt (merge-lt tree1 right_tree2))))
   :hints (("Goal"
            :induct (merge-lt tree1 right_tree2)))))

(local
 (defthmd proper-merge-lt-L3
   (implies (and (consp (right-lt tree1))
                 (consp tree2)
                 (proper-lt (right-lt tree1))
                 (proper-lt tree2)
                 (lexorder (root-lt tree1)
                           (root-lt (right-lt tree1)))
                 (lexorder (root-lt tree1)
                           (root-lt tree2)))
            (lexorder (root-lt tree1)
                      (root-lt (merge-lt (right-lt tree1) tree2))))
   :hints (("Goal"
            :use ((:instance proper-merge-lt-L1
                             (right_tree1 (cadddr tree1))
                             (tree2 tree2)
                             (x (cadr tree1))))))))

(local
 (defthmd proper-merge-lt-L4
   (implies (and (consp tree1)
                 (consp (right-lt tree2))
                 (proper-lt tree1)
                 (proper-lt (right-lt tree2))
                 (not (lexorder (root-lt tree1)
                                (root-lt tree2)))
                 (lexorder (root-lt tree2) (root-lt (right-lt tree2))))
            (lexorder (root-lt tree2)
                      (root-lt (merge-lt tree1 (right-lt tree2)))))
   :hints (("Goal"
            :use ((:instance proper-merge-lt-L2
                             (tree1 tree1)
                             (right_tree2 (cadddr tree2))
                             (x (cadr tree2))))))))

(defthm proper-merge-lt
  (implies (and (proper-lt tree1)
                (proper-lt tree2))
           (proper-lt (merge-lt tree1 tree2)))
  :hints (("Goal"
           :in-theory (enable proper-merge-lt-L3 proper-merge-lt-L4)
           :induct (merge-lt tree1 tree2)))
  :doc ":doc-section leftist-tree-structure-thms
~/~/
(and (proper-lt tree1) (proper-lt tree2)) 
    ==> (proper-lt (merge-lt tree1 tree2))~/")

(defthm proper-insert-lt
  (implies (proper-lt tree)
           (proper-lt (insert-lt x tree)))
  :doc ":doc-section leftist-tree-structure-thms
~/~/
(proper-lt tree) ==> (proper-lt (insert-lt x tree))~/")

(defthm proper-build-lt
  (proper-lt (build-lt l))
  :doc ":doc-section leftist-tree-structure-thms
~/~/
(proper-lt (build-lt l))~/")

(defthm proper-delete-min-lt
  (implies (proper-lt tree)
           (proper-lt (delete-min-lt tree)))
  :doc ":doc-section leftist-tree-structure-thms
~/~/
(proper-lt tree) ==> (proper-lt (delete-min-lt tree))~/")

;;;;;;;;;;;;;;;;;;;
;; RANK THEOREMS ;;
;;;;;;;;;;;;;;;;;;;

(defdoc leftist-tree-rank-thms
  ":doc-section leftist-tree-thms
Theorems about the rank of leftist trees~/~/~/")

(local
 (defthmd size-rank-lt-L1
   (implies (and (natp b)
                 (natp c)
                 (natp p)
                 (natp q)
                 (natp r)
                 (equal p (+ 1 r))
                 (<= (expt 2 q) (+ b 1))
                 (<= (expt 2 r) (+ c 1))
                 (<= r q))
            (<= (expt 2 p) (+ 2 b c)))
   :hints (("Goal"
            :use ((:instance (:theorem (implies (and (<= x y)
                                                     (<= y z))
                                                (<= x z)))
                             (x (expt 2 p))
                             (y (+ (expt 2 q) (expt 2 r)))
                             (z (+ 2 b c))))))))

(defthm size-rank-lt
  (implies (proper-lt tree)
           (<= (- (expt 2 (rank-lt tree)) 1)
               (size-lt tree)))
  :hints (("Goal"
           :induct (size-lt tree))
          ("Subgoal *1/2.11''"
           :use ((:instance size-rank-lt-L1
                            (b (size-lt (caddr tree)))
                            (c (size-lt (cadddr tree)))
                            (p (car tree))
                            (q (caaddr tree))
                            (r (caaddr (cdr tree))))))
          ("Subgoal *1/2.6''"
           :use ((:instance rank-is-natp-lt
                            (tree (caddr tree))))))
  :doc ":doc-section leftist-tree-rank-thms
~/~/
(proper-lt tree)
    ==> (<= (- (expt 2 (rank-lt tree)) 1)
            (size-lt tree))~/")