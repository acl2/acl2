; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "binary-tree"))
(local (include-book "bst"))
(local (include-book "bst-order"))
(local (include-book "cardinality"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable bst<-rules)))

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rotations
  :parents (implementation)
  :short "Left and right tree rotations."
  ;;      x         left rotation →         y
  ;;    ↙   ↘       ← right rotation      ↙   ↘
  ;;  a       y                         x       c
  ;;        ↙   ↘                     ↙   ↘
  ;;      b       c                 a       b
  :long
  (xdoc::topstring
    (xdoc::p
      "Rotations preserve the binary search tree property while rotating up the
       head of one or the other subtrees."))
  :set-as-default-parent t

  (define rotate-left
    ((tree binary-tree-p))
    :guard (not (tree-emptyp (tree-right tree)))
    :returns (tree$ binary-tree-p)
    :short "Perform a left tree rotation."
    :long
    (xdoc::topstring
     (xdoc::p
       "When the right subtree is empty (contrary to the guard), we logically
        just return the tree."))
    (if (mbt (not (tree-emptyp (tree-right tree))))
        (tree-node (tree-head (tree-right tree))
                   (tree-node (tree-head tree)
                              (tree-left tree)
                              (tree-left (tree-right tree)))
                   (tree-right (tree-right tree)))
      (tree-fix tree))
    :inline t)

  (define rotate-right
    ((tree binary-tree-p))
    :guard (not (tree-emptyp (tree-left tree)))
    :returns (tree$ binary-tree-p)
    :short "Perform a right tree rotation."
    :long
    (xdoc::topstring
     (xdoc::p
       "When the left subtree is empty (contrary to the guard), we logically
        just return the tree."))
    (if (mbt (not (tree-emptyp (tree-left tree))))
        (tree-node (tree-head (tree-left tree))
                   (tree-left (tree-left tree))
                   (tree-node (tree-head tree)
                              (tree-right (tree-left tree))
                              (tree-right tree)))
      (tree-fix tree))
    :inline t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rotate-left-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (rotate-left x)
                  (rotate-left y)))
  :rule-classes :congruence
  :enable (tree-equiv
           rotate-left))

(defrule rotate-right-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (rotate-right x)
                  (rotate-right y)))
  :rule-classes :congruence
  :enable (tree-equiv
           rotate-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rotate-left-of-rotate-right-when-not-tree-emptyp-of-tree-left
  (implies (not (tree-emptyp (tree-left tree)))
           (equal (rotate-left (rotate-right tree))
                  tree))
  :enable (rotate-left
           rotate-right))

(defrule rotate-right-of-rotate-left-when-not-tree-emptyp-of-tree-right
  (implies (not (tree-emptyp (tree-right tree)))
           (equal (rotate-right (rotate-left tree))
                  tree))
  :enable (rotate-right
           rotate-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-emptyp-of-rotate-left
  (equal (tree-emptyp (rotate-left tree))
         (tree-emptyp tree))
  :enable rotate-left)

(defrule tree-emptyp-of-rotate-right
  (equal (tree-emptyp (rotate-right tree))
         (tree-emptyp tree))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-rotate-left
  (equal (tree-in x (rotate-left tree))
         (tree-in x tree))
  :enable rotate-left)

(defrule tree-in-of-rotate-right
  (equal (tree-in x (rotate-right tree))
         (tree-in x tree))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-head-of-rotate-left
  (equal (tree-head (rotate-left tree))
         (if (tree-emptyp (tree-right tree))
             (tree-head tree)
           (tree-head (tree-right tree))))
  :enable rotate-left)

(defrule tree-head-of-rotate-right
  (equal (tree-head (rotate-right tree))
         (if (tree-emptyp (tree-left tree))
             (tree-head tree)
           (tree-head (tree-left tree))))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-left-of-rotate-left
  (equal (tree-left (rotate-left tree))
         (if (tree-emptyp (tree-right tree))
             (tree-left tree)
           (tree-node (tree-head tree)
                      (tree-left tree)
                      (tree-left (tree-right tree)))))
  :enable (rotate-left
           ;; TODO: shouldn't be necessary
           tree-fix
           ))

(defrule tree-left-of-rotate-right
  (equal (tree-left (rotate-right tree))
         (if (tree-emptyp (tree-left tree))
             (tree-left tree)
           (tree-left (tree-left tree))))
  :enable (rotate-right
           ;; TODO: shouldn't be necessary
           tree-fix
           ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-right-of-rotate-left
  (equal (tree-right (rotate-left tree))
         (if (tree-emptyp (tree-right tree))
             (tree-right tree)
           (tree-right (tree-right tree))))
  :enable (rotate-left
           ;; TODO: shouldn't be necessary
           tree-fix
           ))

(defrule tree-right-of-rotate-right
  (equal (tree-right (rotate-right tree))
         (if (tree-emptyp (tree-left tree))
             (tree-right tree)
           (tree-node (tree-head tree)
                      (tree-right (tree-left tree))
                      (tree-right tree))))
  :enable (rotate-right
           ;; TODO: shouldn't be necessary
           tree-fix
           ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-l-of-rotate-left
  (equal (bst<-all-l (rotate-left tree) x)
         (bst<-all-l tree x))
  :enable rotate-left)

(defrule bst<-all-l-of-rotate-right
  (equal (bst<-all-l (rotate-right tree) x)
         (bst<-all-l tree x))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;

(defrule bst<-all-r-of-arg1-and-rotate-left
  (equal (bst<-all-r x (rotate-left tree))
         (bst<-all-r x tree))
  :enable rotate-left)

(defrule bst<-all-r-of-arg1-and-rotate-right
  (equal (bst<-all-r x (rotate-right tree))
         (bst<-all-r x tree))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-rotate-left
  (equal (heap<-all-l (rotate-left tree) x)
         (heap<-all-l tree x))
  :enable rotate-left)

(defrule heap<-all-l-of-rotate-right
  (equal (heap<-all-l (rotate-right tree) x)
         (heap<-all-l tree x))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bst-p-of-rotate-left
  (equal (bst-p (rotate-left tree))
         (bst-p tree))
  :enable (rotate-left
           bst<-all-extra-rules))

(defrule bst-p-of-rotate-right
  (equal (bst-p (rotate-right tree))
         (bst-p tree))
  :enable (rotate-right
           bst<-all-extra-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heapp-of-rotate-left
  (equal (heapp (rotate-left tree))
         (if (tree-emptyp (tree-right tree))
             (heapp tree)
           (and (heapp (tree-left tree))
                (heapp (tree-left (tree-right tree)))
                (heapp (tree-right (tree-right tree)))
                (heap< (tree-head tree)
                       (tree-head (tree-right tree)))
                (heap<-all-l (tree-left tree)
                             (tree-head tree))
                (heap<-all-l (tree-left (tree-right tree))
                             (tree-head tree))
                (heap<-all-l (tree-left (tree-right tree))
                             (tree-head (tree-right tree)))
                (heap<-all-l (tree-right (tree-right tree))
                             (tree-head (tree-right tree))))))
  :enable (rotate-left
           heap<-all-l-extra-rules))

(defrule heapp-of-rotate-left-when-not-tree-emptyp-of-tree-right
  (implies (not (tree-emptyp (tree-right tree)))
           (equal (heapp (rotate-left tree))
                  (and (heapp (tree-left tree))
                       (heapp (tree-left (tree-right tree)))
                       (heapp (tree-right (tree-right tree)))
                       (heap< (tree-head tree)
                              (tree-head (tree-right tree)))
                       (heap<-all-l (tree-left tree)
                                    (tree-head tree))
                       (heap<-all-l (tree-left (tree-right tree))
                                    (tree-head tree))
                       (heap<-all-l (tree-left (tree-right tree))
                                    (tree-head (tree-right tree)))
                       (heap<-all-l (tree-right (tree-right tree))
                                    (tree-head (tree-right tree))))))
  :enable heapp-of-rotate-left)

;;;;;;;;;;;;;;;;;;;;

(defruled heapp-of-rotate-right
  (equal (heapp (rotate-right tree))
         (if (tree-emptyp (tree-left tree))
             (heapp tree)
           (and (heapp (tree-right tree))
                (heapp (tree-left (tree-left tree)))
                (heapp (tree-right (tree-left tree)))
                (heap< (tree-head tree)
                       (tree-head (tree-left tree)))
                (heap<-all-l (tree-right tree)
                             (tree-head tree))
                (heap<-all-l (tree-right (tree-left tree))
                             (tree-head tree))
                (heap<-all-l (tree-left (tree-left tree))
                             (tree-head (tree-left tree)))
                (heap<-all-l (tree-right (tree-left tree))
                             (tree-head (tree-left tree))))))
  :enable (rotate-right
           heap<-all-l-extra-rules))

(defrule heapp-of-rotate-right-when-not-tree-emptyp-of-tree-left
  (implies (not (tree-emptyp (tree-left tree)))
           (equal (heapp (rotate-right tree))
                  (and (heapp (tree-right tree))
                       (heapp (tree-left (tree-left tree)))
                       (heapp (tree-right (tree-left tree)))
                       (heap< (tree-head tree)
                              (tree-head (tree-left tree)))
                       (heap<-all-l (tree-right tree)
                                    (tree-head tree))
                       (heap<-all-l (tree-right (tree-left tree))
                                    (tree-head tree))
                       (heap<-all-l (tree-left (tree-left tree))
                                    (tree-head (tree-left tree)))
                       (heap<-all-l (tree-right (tree-left tree))
                                    (tree-head (tree-left tree))))))
  :enable heapp-of-rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-rotate-left
  (equal (tree-nodes-count (rotate-left tree))
         (tree-nodes-count tree))
  :enable (tree-nodes-count
           rotate-left))

(defrule tree-nodes-count-of-rotate-right
  (equal (tree-nodes-count (rotate-right tree))
         (tree-nodes-count tree))
  :enable (tree-nodes-count
           rotate-right))
