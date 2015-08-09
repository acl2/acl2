#|

   Leftist Trees, Version 0.1
   Copyright (C) 2012 by Ben Selfridge <benself@cs.utexas.edu>

  License: (An MIT/X11-style license)

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.

 leftist-tree-defthms.lisp

   This file contains the basic theory of leftist trees,
   proving the basic operations correct.

   This implementation follows "Purely Functional Data
   Structures" by Chris Okasaki.

|#

(in-package "ACL2")
(include-book "leftist-tree-defuns")

; NOTE: Legacy doc strings defined in this file were replaced Nov. 2014 by the
; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.

;; We need this much arithmetic to prove theorems about the
;; rank of the tree.

(local (include-book "arithmetic-5/top" :dir :system))

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-thms
;   ":doc-section leftist-trees
; Useful theorems about leftist trees.~/~/
; ~/")



;;;;;;;;;;;;;;;;;;;
;; MISCELLANEOUS ;;
;;;;;;;;;;;;;;;;;;;

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-misc-thms
;   ":doc-section leftist-tree-thms
; Miscellaneous theorems~/~/
; Includes proofs that the rank, length of right spine, and length of
; the shortest path to an empty node are all equal. We also prove that
; the rank and size of a tree are always natp, as this is helpful in
; a later theorem.~/")

(defthm lrt-equals-rank-lt
  (implies (proper-lt tree)
           (equal (length-right-spine-lt tree)
                  (rank-lt tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-misc-thms
; ~/~/
; (length-right-spine-lt tree) ==> (rank-lt tree)~/"
  )

(defthm ltn-equals-rank-lt
  (implies (proper-lt tree)
           (equal (length-to-nil-lt tree)
                  (rank-lt tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-misc-thms
; ~/~/
; (length-to-nil-lt tree) ==> (rank-lt tree)~/"
  )

(defthm member-insert-lt
  (implies (proper-lt tree)
           (member-lt x (insert-lt x tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-misc-thms
; ~/~/
; (proper-lt tree) ==> (member-lt x (insert-lt x tree))~/"
  )

; rank and size are naturals
(defthm rank-is-natp-lt
  (implies (proper-lt tree)
           (natp (rank-lt tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-misc-thms
; ~/~/
; (proper-lt tree) ==> (natp (rank-lt tree))~/"
  )

(defthm size-is-natp-lt
  (implies (proper-lt tree)
           (natp (size-lt tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-misc-thms
; ~/~/
; (proper-lt tree) ==> (natp (size-lt tree))~/"
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BASIC OPERATIONS RESPECT STRUCTURE ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-structure-thms
;   ":doc-section leftist-tree-thms
; Theorems proving that the basic operations respect PROPER-LT~/~/~/")

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
   (implies (and (consp (cadddr tree1))
                 (consp tree2)
                 (proper-lt (cadddr tree1))
                 (proper-lt tree2)
                 (lexorder (cadr tree1)
                           (cadadr (cddr tree1)))
                 (lexorder (cadr tree1)
                           (cadr tree2)))
            (lexorder (cadr tree1)
                      (cadr (merge-lt (cadddr tree1) tree2))))
   :hints (("Goal"
            :use ((:instance proper-merge-lt-L1
                             (right_tree1 (cadddr tree1))
                             (tree2 tree2)
                             (x (cadr tree1))))))))

(local
 (defthmd proper-merge-lt-L4
   (implies (and (consp tree1)
                 (consp (cadddr tree2))
                 (proper-lt tree1)
                 (proper-lt (cadddr tree2))
                 (not (lexorder (cadr tree1)
                                (cadr tree2)))
                 (lexorder (cadr tree2) (cadadr (cddr tree2))))
            (lexorder (cadr tree2)
                      (cadr (merge-lt tree1 (cadddr tree2)))))
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
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-structure-thms
; ~/~/
; (and (proper-lt tree1) (proper-lt tree2))
;     ==> (proper-lt (merge-lt tree1 tree2))~/"
  )

(defthm proper-insert-lt
  (implies (proper-lt tree)
           (proper-lt (insert-lt x tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-structure-thms
; ~/~/
; (proper-lt tree) ==> (proper-lt (insert-lt x tree))~/"
  )

(defthm proper-build-lt
  (proper-lt (build-lt l))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-structure-thms
; ~/~/
; (proper-lt (build-lt l))~/"
  )

(defthm proper-delete-min-lt
  (implies (proper-lt tree)
           (proper-lt (delete-min-lt tree)))
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-structure-thms
; ~/~/
; (proper-lt tree) ==> (proper-lt (delete-min-lt tree))~/"
  )

;;;;;;;;;;;;;;;;;;;
;; RANK THEOREMS ;;
;;;;;;;;;;;;;;;;;;;

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-rank-thms
;   ":doc-section leftist-tree-thms
; Theorems about the rank of leftist trees~/~/~/")

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
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":doc-section leftist-tree-rank-thms
; ~/~/
; (proper-lt tree)
;     ==> (<= (- (expt 2 (rank-lt tree)) 1)
;             (size-lt tree))~/"
  )
