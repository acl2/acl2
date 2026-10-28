; ACL2-2026 Workshop Paper on DEFINDUCTIVE
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/definductive" :dir :system)

(local (include-book "std/basic/inductions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains details of the NAT-TREES example in Section 4.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Define natural numbers and finitely branching trees of natural numbers.

(definductive nat-trees
  :preds ((nat n) (tree tr) (trees trs))
  :irules ((zero ()
                 (nat 0))
           (succ ((nat n))
                 (nat (1+ n)))
           (leaf ((nat n))
                 (tree n))
           (branch ((nat n)
                    (trees trs))
                   (tree (cons n trs)))
           (empty ()
                  (trees nil))
           (cons ((tree tr)
                  (trees trs))
                 (trees (cons tr trs))))
  :verify-guards nil)

; The inductively defined NAT is equivalent to ACL2's NATP.

(defruled natp-when-nat-proof-validp
  (implies (nat-proof-validp proof n)
           (natp n))
  :induct t
  :enable (nat-proof-validp
           nat-zero-validp
           nat-succ-validp))

(defruled natp-when-nat
  (implies (nat n)
           (natp n))
  :enable (nat natp-when-nat-proof-validp))

(defruled nat-pred ; derived inference rule
  (implies (and (not (zp n))
                (nat (1- n)))
           (nat n))
  :use (:instance nat-succ (n (1- n))))

(defruled nat-when-natp
  (implies (natp n)
           (nat n))
  :induct (dec-induct n)
  :enable (nat-zero nat-pred))

(defrule nat-is-natp
  (equal (nat n)
         (natp n))
  :enable (natp-when-nat nat-when-natp))

; An alternative definition of finitely branching trees of natural numbers,
; using mutually recursive functions that recognize them.

(defines treep/treesp
  (define treep (tr)
    (or (natp tr)
        (and (consp tr)
             (natp (car tr))
             (treesp (cdr tr)))))
  (define treesp (trs)
    (or (equal trs nil)
        (and (consp trs)
             (treep (car trs))
             (treesp (cdr trs)))))
  :flag-local nil)

; The inductively defined TREE and TREES are equivalent to
; the recursively defined recognizers.

(defthm-tree-proof-validp-clique-flag
  (defthmd treep-when-tree-proof-validp
    (implies (tree-proof-validp proof _tr)
             (treep _tr))
    :flag tree-proof-validp)
  (defthmd treesp-when-trees-proof-validp
    (implies (trees-proof-validp proof _trs)
             (treesp _trs))
    :flag trees-proof-validp)
  :hints (("Goal" :in-theory (enable tree-proof-validp
                                     trees-proof-validp
                                     tree-leaf-validp
                                     tree-branch-validp
                                     trees-empty-validp
                                     trees-cons-validp
                                     treep
                                     treesp
                                     natp-when-nat-proof-validp))))

(defruled treep-when-tree
  (implies (tree tr)
           (treep tr))
  :enable (tree treep-when-tree-proof-validp))

(defruled treesp-when-trees
  (implies (trees trs)
           (treesp trs))
  :enable (trees treesp-when-trees-proof-validp))

(defthm-treep/treesp-flag
  (defthmd tree-when-treep
    (implies (treep tr)
             (tree tr))
    :flag treep)
  (defthmd trees-when-treesp
    (implies (treesp trs)
             (trees trs))
    :flag treesp)
  :hints (("Goal" :in-theory (enable treep
                                     treesp
                                     tree-leaf
                                     tree-branch
                                     trees-empty
                                     trees-cons))))

(defruled tree-is-treep
  (equal (tree tr)
         (treep tr))
  :use (tree-when-treep treep-when-tree))

(defruled trees-is-treesp
  (equal (trees trs)
         (treesp trs))
  :use (trees-when-treesp treesp-when-trees))
