; Centaur AIG Library
; Copyright (C) 2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "tools/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)

; Given two AIGs, A and B, we say that A is "better" than B if:
;
;  (1) A has fewer unique AND nodes than B, or
;  (2) A,B have the same number of unique AND nodes, but A has fewer
;        total nodes than B.
;
; We introduce two main functions.
;
; 1. (AIG-LIST-BEST X) is given a non-empty AIG List and returns the best AIG
;    within it.
;
; 2. (AIG-LIST-LIST-BEST X) is given a list of non-empty AIG Lists, say (L1 L2
;    ... Ln), and returns (B1 B2 ... Bn) where Bi is the best AIG from each Li.
;
; Logically AIG-LIST-LIST-BEST is just the ordinary "map" or projection of
; AIG-LIST-BEST, but it takes advantage of more structure sharing and
; memoization than the naive projection would and hence may be much more
; efficient.
;
; Implementation.
;
; It is tricky to directly count "unique nodes" in a memoized way, but there
; is a very easy way to do it indirectly.
;
; First, we assign a number to every unique AIG node in sight, which (assuming
; constant-time hashing) is linear in the sizes of the input AIGs.  We call
; these numbers labels.
;
; Next, we can write memoized functions to gather the sets of labels for all of
; the AND nodes within an AIG, and similarly for all of the nodes.  We just use
; regular ordered sets to represent these sets.  Importantly, these collection
; functions can be easily memoized.
;
; Finally, to count the number of ANDs (or all nodes) in an AIG, we just
; collect the labels for its ANDs (or all nodes) and see how many labels were
; found.

(defund aig-label-nodes (x free map)
  "Returns (MV FREE' MAP')"
  (declare (xargs :guard (natp free) :verify-guards nil))
  ;; X is the AIG to traverse.
  ;; FREE is the smallest label that hasn't been assigned to any node yet.
  ;; MAP is the fast alist from AIG nodes to labels that we're constructing.
  (b* (((when (atom x))
        (mv (lnfix free) map))
       ((when (hons-get x map))
        (mv (lnfix free) map))
       ((mv free map) (aig-label-nodes (car x) free map))
       ((mv free map) (aig-label-nodes (cdr x) free map))
       (map           (hons-acons x free map))
       (free          (+ 1 free)))
    (mv free map)))

(defthm natp-of-aig-label-nodes
  (natp (mv-nth 0 (aig-label-nodes x free map)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable aig-label-nodes))))

(verify-guards aig-label-nodes)



(defund aig-list-label-nodes (x free map)
  "Returns (MV FREE' MAP')"
  (declare (xargs :guard (natp free) :verify-guards nil))
  ;; Extends AIG-LABEL-NODES to an AIG List.
  (if (atom x)
      (mv (nfix free) map)
    (b* (((mv free map) (aig-label-nodes (car x) free map))
         ((mv free map) (aig-list-label-nodes (cdr x) free map)))
      (mv free map))))

(defthm natp-of-aig-list-label-nodes
  (natp (mv-nth 0 (aig-list-label-nodes x free map)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable aig-list-label-nodes))))

(verify-guards aig-list-label-nodes)



(defund aig-list-list-label-nodes (x free map)
  "Returns (MV FREE' MAP')"
  (declare (xargs :guard (natp free) :verify-guards nil))
  ;; Extends AIG-LABEL-NODES to an AIG List List.
  (if (atom x)
      (mv (nfix free) map)
    (b* (((mv free map) (aig-list-label-nodes (car x) free map))
         ((mv free map) (aig-list-list-label-nodes (cdr x) free map)))
      (mv free map))))

(defthm natp-of-aig-list-list-label-nodes
  (natp (mv-nth 0 (aig-list-list-label-nodes x free map)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable aig-list-list-label-nodes))))

(verify-guards aig-list-list-label-nodes)



(defund aig-collect-andnode-labels (x map)
  "Returns INDEX-SET"
  (declare (xargs :guard t))
  ;; X is an AIG.
  ;; MAP is the mapping from AIG nodes to labels.
  ;; We collect the set of labels for all AND nodes in X.
  (cond ((atom x)
         nil)
        ((not (cdr x))
         (aig-collect-andnode-labels (car x) map))
        (t
         (let ((x-label    (cdr (hons-get x map)))
               (car-labels (aig-collect-andnode-labels (car x) map))
               (cdr-labels (aig-collect-andnode-labels (cdr x) map)))
           (sets::insert x-label (sets::union car-labels cdr-labels))))))

(memoize 'aig-collect-andnode-labels :condition '(and (consp x) (cdr x)))

(defthm setp-of-aig-collect-andnode-labels
  (sets::setp (aig-collect-andnode-labels x map))
  :hints(("Goal" :in-theory (enable aig-collect-andnode-labels))))

(defund aig-count-andnode-labels (x map)
  (declare (xargs :guard t))
  (sets::cardinality (aig-collect-andnode-labels x map)))



(defund aig-collect-labels (x map)
  "Returns INDEX-SET"
  (declare (xargs :guard t))
  ;; X is an AIG.
  ;; MAP is the mapping from AIG nodes to labels.
  ;; We collect the set of labels for all nodes in X.
  (cond ((atom x)
         nil)
        (t
         (let ((x-label    (cdr (hons-get x map)))
               (car-labels (aig-collect-labels (car x) map))
               (cdr-labels (aig-collect-labels (cdr x) map)))
           (sets::insert x-label
                         (sets::union car-labels cdr-labels))))))

(memoize 'aig-collect-labels :condition '(and (consp x) (cdr x)))

(defthm setp-of-aig-collect-labels
  (sets::setp (aig-collect-labels x map))
  :hints(("Goal" :in-theory (enable aig-collect-labels))))

(defund aig-count-labels (x map)
  (declare (xargs :guard t))
  (sets::cardinality (aig-collect-labels x map)))




(defund aig-list-best-aux1 (x best best-ands map)
  (declare (xargs :guard (natp best-ands)))
  (if (atom x)
      best
    (b* ((ands (aig-count-andnode-labels (car x) map)))
      (if (or (< ands best-ands)
              (and (= best-ands ands)
                   (< (aig-count-labels (car x) map)
                      (aig-count-labels best map))))
          (aig-list-best-aux1 (cdr x) (car x) ands map)
        (aig-list-best-aux1 (cdr x) best best-ands map)))))

(defund aig-list-best-aux (x map)
  (declare (xargs :guard t))
  (if (atom x)
      (er hard? 'aig-list-best-aux "Expected at least one aig.")
    (aig-list-best-aux1 (cdr x)
                        (car x)
                        (aig-count-andnode-labels (car x) map)
                        map)))

(defund aig-list-list-best-aux (x map)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (aig-list-best-aux (car x) map)
          (aig-list-list-best-aux (cdr x) map))))


(defund aig-list-best (x)
  ; X is an AIG List.
  (declare (xargs :guard t))
  (b* (((mv ?free map) (cwtime (aig-list-label-nodes x 0 nil)
                               :mintime 1/2))
       (ret (cwtime (aig-list-best-aux x map)
                    :mintime 1/2)))
    (fast-alist-free map)
    (clear-memoize-table 'aig-collect-andnode-labels)
    (clear-memoize-table 'aig-collect-labels)
    ret))

(defund aig-list-list-best (x)
  ; X is an AIG List List.
  (declare (xargs :guard t))
  (b* (((mv ?free map) (cwtime (aig-list-list-label-nodes x 0 nil)
                               :mintime 1))
       (ret (cwtime (aig-list-list-best-aux x map)
                    :mintime 1)))
    (fast-alist-free map)
    (clear-memoize-table 'aig-collect-andnode-labels)
    (clear-memoize-table 'aig-collect-labels)
    ret))
