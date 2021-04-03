; Tools to rebuild DAGs while applying node translations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "worklist-array")
(include-book "translation-array")
(include-book "dag-array-builders")
(include-book "def-dag-builder-theorems")
(include-book "sortedp-less-than-or-equal")
(include-book "all-less-than-or-equal-all")
(include-book "less-than-or-equal-all")
(local (include-book "merge-sort-less-than-rules"))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local
 (defthm integerp-of-if
  (equal (integerp (if x y z))
         (if x
             (integerp y)
           (integerp z)))))

(local
 (defthm acl2-numberp-when-integerp
   (implies (integerp x)
            (acl2-numberp x))))

;dup
(defthmd natp-of-+-of-1-alt
  (implies (integerp x)
           (equal (natp (+ 1 x))
                  (<= -1 x))))

(defthm <=-of-0-and-car-of-last-when-all-natp
  (implies (and (all-natp x)
                (consp x))
           (<= 0 (car (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defthm <-of--1-and-car-of-last-when-all-natp
  (implies (and (all-natp x)
                (consp x))
           (< -1 (car (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defthm <-of-car-of-last-and--1-when-all-natp
  (implies (and (all-natp x)
                (consp x))
          (not  (< (car (last x)) -1)))
  :hints (("Goal" :in-theory (enable last))))

(encapsulate ()
  (local (include-book "kestrel/lists-light/memberp" :dir :system))
;move
  (defcong perm iff (member-equal x y) 2
    :hints (("Goal" :in-theory (enable member-equal perm)))))

;move
(defcong perm equal (subsetp-equal x y) 2
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-merge-sort-<
  (equal (subsetp-equal x (merge-sort-< x))
         (subsetp-equal x x)))

;disble?
(defthm natp-of-car-when-nat-listp-type
  (implies (and (nat-listp x)
                (consp x))
           (natp (car x)))
  :rule-classes :type-prescription)

(defthm integerp-of-car-of-last-when-all-natp
  (implies (and (all-natp x)
                (consp x))
           (integerp (car (last x))))
  :hints (("Goal" :in-theory (enable last))))

(defthm nat-listp-when-all-natp
  (implies (all-natp x)
           (equal (nat-listp x)
                  (true-listp x)))
  :hints (("Goal" :in-theory (enable nat-listp all-natp))))

(defthmd <-of-car-when-all-<
  (implies (and (all-< items x)
                (consp items))
           (< (car items) x))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm <-of-car-when-all-<-cheap
  (implies (and (all-< items x)
                (consp items))
           (< (car items) x))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm all-<-of-+-of-1
  (implies (and (syntaxp (not (quotep y)))
                (all-integerp x)
                (integerp y))
           (equal (all-< x (+ 1 y))
                  (all-<= x y)))
  :hints (("Goal" :in-theory (enable all-<= all-<))))

(defthm all-<=-of-car-of-last-when-sortedp-<=-2
  (implies (and (sortedp-<= x)
                (subsetp-equal y x))
           (all-<= y (car (last x))))
  :hints (("Goal" :in-theory (enable ALL-<=
                                     SUBSETP-EQUAL
                                     sortedp-<=))))

;;move to rational-lists.lisp
(defthm all-<=-of-maxelem
  (all-<= lst (maxelem lst))
  :hints (("Goal" :in-theory (enable all-<=))))

(defthmd dargp-of-car-when-all-natp
  (implies (all-natp x)
           (equal (dargp (car x))
                  (consp x))))

(defthm all-<=-all-of-get-unexamined-nodenum-args
  (implies (and (all-<=-all (keep-atoms args) worklist)
                (all-<=-all acc worklist))
           (all-<=-all (get-unexamined-nodenum-args args worklist-array acc) worklist))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args keep-atoms))))

(defthm all-<=-of-keep-atoms
  (implies (and (all-dargp-less-than args (+ 1 nodenum))
                (natp nodenum))
           (all-<= (keep-atoms args) nodenum))
  :hints (("Goal" :in-theory (enable all-dargp-less-than keep-atoms))))

(defthm all-<=-of-keep-atoms-of-dargs
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (consp (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))
                (NOT (EQUAL 'QUOTE (CAR (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))))
                (natp nodenum)
                (< nodenum dag-len))
           (all-<= (keep-atoms (dargs (aref1 'dag-array dag-array nodenum)))
                   nodenum))
  :hints (("Goal" :use (:instance all-<=-of-keep-atoms (args (dargs (aref1 'dag-array dag-array nodenum))))
           :in-theory (disable all-<=-of-keep-atoms))))

(defthm ALL-<=-ALL-when-ALL-<=-ALL-of-cdr-arg2
  (implies (and (ALL-<=-ALL x (cdr y))
                )
           (equal (ALL-<=-ALL x y)
                  (or (not (consp y))
                      (all-<= x (car y)))))
  :hints (("Goal" :in-theory (enable ALL-<=-ALL))))

(defthm all-<=-all-of-keep-atoms-of-dargs
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (consp (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))
                (NOT (EQUAL 'QUOTE (CAR (AREF1 'DAG-ARRAY DAG-ARRAY NODENUM))))
                (natp nodenum)
                (< nodenum dag-len)
                (<=-all nodenum nodenums)
                )
           (all-<=-all (keep-atoms (dargs (aref1 'dag-array dag-array nodenum)))
                       nodenums))
  :hints (("goal" :in-theory (enable <=-all)
           :induct (<=-all nodenum nodenums))
          ("subgoal *1/2"
           :use (:instance all-<=-of-keep-atoms-of-dargs)
           :in-theory (e/d (<=-all)
                           (ALL-<-OF-KEEP-ATOMS
                            all-<=-of-keep-atoms-of-dargs
                            all-<=-of-keep-atoms
                            all-<-of-keep-atoms-of-dargs-when-bounded-dag-exprp
                            ;;all-dargp-less-than-of-args-when-bounded-dag-exprp
                            )))))
;dup
(defthm all-<=-when-all-<
  (implies (all-< x bound)
           (all-<= x bound))
  :hints (("Goal" :in-theory (enable all-< all-<=))))

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing the substitution indicated by TRANSLATION-ARRAY.
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; TODO: this could compute ground terms - but the caller would need to check for quoteps in the result
;; TODO: We could stop once we hit a node smaller than any node which is changed in the translation-array?  track the smallest node with a pending change.  no smaller node needs to be changed?
;; TODO: Instead of mapping unchanged nodes to themselves, could simply leave them mapped to nil?
(defund rebuild-nodes-aux (worklist ;nodenums, should be sorted
                           translation-array ;maps each nodenum to nil (unhandled) or a nodenum (maybe the nodenum itself) [or a quotep - no, not currently]
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                           worklist-array)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                              (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                              (= (alen1 'worklist-array worklist-array)
                                 (alen1 'translation-array translation-array)))
                  ;; For the measure, we first check whether the number of
                  ;; examined nodes goes up.  If not, we check that the length
                  ;; of the worklist goes down.
                  :measure (make-ord 1 (+ 1 (- (nfix (alen1 'worklist-array worklist-array))
                                               (num-examined-nodes (+ -1 (alen1 'worklist-array worklist-array))
                                                                   'worklist-array worklist-array)))
                                     (len worklist))
                  :verify-guards nil ; done below
                  ))
  (if (or (endp worklist)
          ;; for termination:
          (not (and (mbt (array1p 'worklist-array worklist-array))
                    (mbt (all-natp worklist))
                    (mbt (all-< worklist (alen1 'worklist-array worklist-array))))))
      (mv (erp-nil) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let ((nodenum (first worklist)))
      (if (aref1 'translation-array translation-array nodenum) ;todo: can we do this less often if we know we are replacing only vars?
          ;;This nodenum is being replaced (todo: what if it's being replaced by
          ;;itself?), so we don't need to build any new nodes (and it is
          ;;already bound in translation-array):
          (rebuild-nodes-aux (rest worklist) translation-array
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                             ;; We mark the node as "examined" so it doesn't get added again (TODO: Can we avoid this, instead doing it for initial nodes in the caller?):
                             (aset1 'worklist-array worklist-array nodenum :examined))
        (let ((expr (aref1 'dag-array dag-array nodenum)))
          (if (atom expr)
              ;;it's a variable, so no nodes need to be rebuilt:
              (rebuild-nodes-aux (rest worklist)
                                 (aset1 'translation-array translation-array nodenum nodenum)
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 ;; We mark the node as "examined" so it doesn't get added again:
                                 (aset1 'worklist-array worklist-array nodenum :examined))
            (if (fquotep expr)
                ;;it's a constant, so no nodes need to be rebuilt:
                (rebuild-nodes-aux (rest worklist)
                                   (aset1 'translation-array translation-array nodenum
                                               nodenum ;todo: i'd like to say expr here, but that could cause translation-array to map nodes to things other than nodenums (which the callers would need to handle -- e.g., if a literal maps to a quotep)
                                               )
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                   ;; We mark the node as "examined" so it doesn't get added again:
                                   (aset1 'worklist-array worklist-array nodenum :examined))
              ;;it's a function call:
              (let ((res (aref1 'worklist-array worklist-array nodenum)))
                (if (eq res :examined)
                    ;; The node has been examined, and since we are back to handling
                    ;; it again, we know that its children have already been examined
                    ;; and processed. So now we can process this node:
                    (b* (((mv erp new-args changep)
                          (translate-args-with-changep (dargs expr) translation-array))
                         ((when erp) (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                      (if changep
                          ;; TODO: It would be nice to evaluate ground terms here,
                          ;; but that could cause translation-array to map nodes to
                          ;; things other than nodenums (which the callers would
                          ;; need to handle -- e.g., if a literal maps to a quotep).
                          (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                            (add-function-call-expr-to-dag-array (ffn-symb expr) new-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                            (if erp
                                (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                              (rebuild-nodes-aux (rest worklist)
                                                 (aset1 'translation-array translation-array nodenum new-nodenum)
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                 worklist-array)))
                        ;; No change, so the node maps to itself:
                        (rebuild-nodes-aux (rest worklist)
                                           (aset1 'translation-array translation-array nodenum nodenum) ; can we avoid this (using the lack of a mapping for the node to mean no change)?
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                           worklist-array)))
                  ;; We expand the node. This node's children have not
                  ;; necessarily been processed, but if they've been examined,
                  ;; they've been fully processed.
                  (let* ((unexamined-args (get-unexamined-nodenum-args (dargs expr) worklist-array nil))
                         ;; TODO: Optimze the case where unexamined-args is nil?
                         ;; TODO: Maybe combine the sorting with get-unexamined-nodenum-args?  usually the number of nodenum args will be very small
                         (sorted-unexamined-args (merge-sort-< unexamined-args)))
                    (rebuild-nodes-aux (append sorted-unexamined-args worklist) ; we could perhaps save this append by making the worklist a list of lists, or we could combine this append with the merge-sort-<
                                       translation-array
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                       (aset1 'worklist-array worklist-array nodenum :examined))))))))))))

(verify-guards rebuild-nodes-aux :hints (("Goal" :in-theory (e/d (<-of-car-when-all-< dargp-of-car-when-all-natp
                                                                                      all-<=-when-all-<)
                                                                 (dargp
                                                                  dargp-less-than
                                                                  SORTEDP-<=)))))

(def-dag-builder-theorems
  (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-aux))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-aux))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                (= (alen1 'worklist-array worklist-array)
                   (alen1 'translation-array translation-array)))
           (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                   (mv-nth '1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-aux) (dargp)))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                (= (alen1 'worklist-array worklist-array)
                   (alen1 'translation-array translation-array)))
           (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                           (mv-nth 1 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))
                                           (mv-nth 3 (rebuild-nodes-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-aux) (dargp)))))

;;;
;;; rebuild-nodes
;;;

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing
;; the substitution indicated by TRANSLATION-ARRAY.
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where the result of rebuilding a
;; given node can be found by looking it up in the translation-array returned.
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; Smashes 'worklist-array.
(defund rebuild-nodes (worklist ;should be sorted
                       translation-array ;maps each nodenum to nil (no replacement, unless a child is to be replaced) or a nodenum (maybe the nodenum itself?) [or a quotep - no, not currently]
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (consp worklist)
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))))
  (rebuild-nodes-aux worklist
                     translation-array
                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                     (make-empty-array 'worklist-array (alen1 'translation-array translation-array))))

(def-dag-builder-theorems
  (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                (nat-listp worklist)
                (consp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (translation-arrayp-aux n
                                   (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                (nat-listp worklist)
                (consp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (bounded-translation-arrayp-aux n
                                           (mv-nth 1 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                           (mv-nth 3 (rebuild-nodes worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes))))

;;;
;;; rebuild-nodes-with-var-subst-aux
;;;

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing the substitution to variable nodes indicated by TRANSLATION-ARRAY (which, as we go, also tracks changes to function call nodes that depend on those var nodes).
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; TODO: this could compute ground terms - but the caller would need to check for quoteps in the result
;; TODO: We could stop once we hit a node smaller than any node which is changed in the translation-array?  track the smallest node with a pending change.  no smaller node needs to be changed?
(defund rebuild-nodes-with-var-subst-aux (worklist ;nodenums, should be sorted
                                          translation-array ;maps each nodenum to nil (no change or not yet :examined) or a nodenum other than itself [or a quotep - no, not currently]
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                          worklist-array)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                              (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                              (= (alen1 'worklist-array worklist-array)
                                 (alen1 'translation-array translation-array)))
                  ;; For the measure, we first check whether the number of
                  ;; examined nodes goes up.  If not, we check that the length
                  ;; of the worklist goes down.
                  :measure (make-ord 1 (+ 1 (- (nfix (alen1 'worklist-array worklist-array))
                                               (num-examined-nodes (+ -1 (alen1 'worklist-array worklist-array))
                                                                   'worklist-array worklist-array)))
                                     (len worklist))
                  :verify-guards nil ; done below
                  ))
  (if (or (endp worklist)
          ;; for termination: -- still needed?
          (not (and (mbt (array1p 'worklist-array worklist-array))
                    (mbt (all-natp worklist))
                    (mbt (all-< worklist (alen1 'worklist-array worklist-array))))))
      (mv (erp-nil) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((nodenum (first worklist))
           (expr (aref1 'dag-array dag-array nodenum)))
      (if (atom expr)
          ;;it's a variable, so either it was marked for replacement in the
          ;;initial translation array (and is still so marked), or it's not
          ;;being replaced
          (rebuild-nodes-with-var-subst-aux (rest worklist)
                                            translation-array ;; no change in either case
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            ;; We mark the node as "examined" so it doesn't get added again:
                                            (aset1 'worklist-array worklist-array nodenum :examined))
        (if (fquotep expr)
            ;;it's a constant (rare), so it's not being replaced (currently, but see todo below)
            (rebuild-nodes-with-var-subst-aux (rest worklist)
                                              ;;todo: i'd like to set nodenum to expr in this, to inline the constant, but that would cause translation-array to map nodes to things other than nodenums (which the callers would need to handle -- e.g., if a literal maps to a quotep):
                                              translation-array
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              ;; We mark the node as "examined" so it doesn't get added again:
                                              (aset1 'worklist-array worklist-array nodenum :examined))
          ;; it's a function call:
          (if (eq :examined (aref1 'worklist-array worklist-array nodenum))
              ;; The node has been examined, and since we are back to handling
              ;; it again, we know that its children have already been examined
              ;; and processed.  So now we can process this node:
              (let* ((args (dargs expr))
                     (new-args (maybe-translate-args args translation-array)))
                (if (not (equal args new-args)) ; since, if new-args=args (often), they should be eq, since maybe-translate-args calls cons-with-hint
                    ;; TODO: It would be nice to evaluate ground terms here,
                    ;; but that could cause translation-array to map nodes to
                    ;; quoteps (which the callers would need to handle -- e.g.,
                    ;; if a literal maps to a quotep).
                    ;; Something changed, so we have to add the new expr to the dag:
                    (b* (((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                          (add-function-call-expr-to-dag-array (ffn-symb expr) new-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                         ((when erp) (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                      (rebuild-nodes-with-var-subst-aux (rest worklist)
                                                        ;; Record what NODENUM was changed to:
                                                        (aset1 'translation-array translation-array nodenum new-nodenum)
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                        worklist-array ; nodenum is already :examined
                                                        ))
                  ;; Args did not change, so no change to this node:
                  (rebuild-nodes-with-var-subst-aux (rest worklist) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)))
            ;; The node is not yet :examined, so we "expand" it. Its children
            ;; have not necessarily been processed, but if they've been
            ;; examined, they've been fully processed.
            (let* ((unexamined-args (get-unexamined-nodenum-args (dargs expr) worklist-array nil))
                   ;; TODO: Optimze the case where unexamined-args is nil?
                   ;; TODO: Maybe combine the sorting with get-unexamined-nodenum-args?  usually the number of nodenum args will be very small
                   (sorted-unexamined-args (merge-sort-< unexamined-args)))
              (rebuild-nodes-with-var-subst-aux (append sorted-unexamined-args worklist) ; we could perhaps save this append by making the worklist a list of lists, or we could combine this append with the merge-sort-<
                                                translation-array
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                ;; This node has now been examined:
                                                (aset1 'worklist-array worklist-array nodenum :examined)))))))))

(verify-guards rebuild-nodes-with-var-subst-aux :hints (("Goal" :in-theory (e/d (<-of-car-when-all-< dargp-of-car-when-all-natp
                                                                                      all-<=-when-all-<)
                                                                 (dargp
                                                                  dargp-less-than
                                                                  SORTEDP-<=)))))
(def-dag-builder-theorems
  (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst-aux))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst-aux))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                (= (alen1 'worklist-array worklist-array)
                   (alen1 'translation-array translation-array)))
           (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                   (mv-nth '1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-with-var-subst-aux) (dargp)))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst-aux
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                (= (alen1 'worklist-array worklist-array)
                   (alen1 'translation-array translation-array)))
           (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array))
                                           (mv-nth 1 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))
                                           (mv-nth 3 (rebuild-nodes-with-var-subst-aux worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist worklist-array))))
  :hints (("Goal" :in-theory (e/d (rebuild-nodes-with-var-subst-aux) (dargp)))))

;;;
;;; rebuild-nodes-with-var-subst
;;;

;; Rebuilds all the nodes in WORKLIST, and their supporters, while performing
;; the substitution indicated by TRANSLATION-ARRAY.
;; Returns (mv erp translation-array dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where the result of rebuilding a
;; given node can be found by looking it up in the translation-array returned.
;; This doesn't change any existing nodes in the dag (just builds new ones).
;; Smashes 'worklist-array.
(defund rebuild-nodes-with-var-subst (worklist ;should be sorted
                                      translation-array ;maps each nodenum to nil (no replacement, unless a child is to be replaced) or a nodenum (maybe the nodenum itself?) [or a quotep - no, not currently]
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp worklist)
                              (sortedp-<= worklist)
                              (consp worklist)
                              (all-< worklist dag-len)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< worklist (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))))
  (rebuild-nodes-with-var-subst-aux worklist
                                    translation-array
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    (make-empty-array 'worklist-array (alen1 'translation-array translation-array))))

(def-dag-builder-theorems
  (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((nat-listp worklist)
         (all-< worklist dag-len)
         (array1p 'translation-array translation-array)
         ;;(all-< (strip-cdrs dag-constant-alist) dag-len)
         (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
         (all-< worklist (alen1 'translation-array translation-array))
         (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
         ))

(defthm array1p-of-mv-nth-1-of-rebuild-nodes-with-var-subst
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (array1p 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

(defthm alen1-of-mv-nth-1-of-rebuild-nodes-with-var-subst
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (equal (alen1 'translation-array (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

(defthm translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                (nat-listp worklist)
                (consp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (translation-arrayp-aux n
                                   (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

(defthm bounded-translation-arrayp-aux-of-mv-nth-1-of-rebuild-nodes-with-var-subst
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (equal n (+ -1 (alen1 'translation-array translation-array))) ;done as hyp to allow better matching
                (nat-listp worklist)
                (consp worklist)
                (all-< worklist dag-len)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< worklist (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len))
           (bounded-translation-arrayp-aux n
                                           (mv-nth 1 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                           (mv-nth 3 (rebuild-nodes-with-var-subst worklist translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable rebuild-nodes-with-var-subst))))

;;;
;;; rebuild-literals-with-substitution
;;;

;; Returns (mv erp literal-nodenums dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where the literal-nodenums are in
;; arbitrary order.
;; Smashes 'translation-array and 'worklist-array.
;ffixme can the literal-nodenums returned ever contain a quotep?
;this could compute ground terms - but the caller would need to check for quoteps in the result
;doesn't change any existing nodes in the dag (just builds new ones)
;; TODO: Consider making a version of this for prover depth 0 which rebuilds
;; the array from scratch (since we can change existing nodes when at depth 0).
(defund rebuild-literals-with-substitution (literal-nodenums
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                            nodenum-to-replace ; must be the nodenum of a var
                                            new-nodenum ;fixme allow this to be a quotep?
                                            )
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (natp nodenum-to-replace)
                              (< nodenum-to-replace dag-len)
                              (natp new-nodenum)
                              (< new-nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (all-integerp-when-all-natp all-rationalp-when-all-natp)
                                                        (myquotep dargp dargp-less-than))))))
  (b* (((when (not (consp literal-nodenums))) ;must check since we take the max below
        (mv (erp-nil) ;or perhaps this is an error.  can it happen?
            literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (sorted-literal-nodenums (merge-sort-< literal-nodenums)) ;; todo: somehow avoid doing this sorting over and over?  keep the list sorted?
       (max-literal-nodenum (car (last sorted-literal-nodenums)))
       ((when (< max-literal-nodenum nodenum-to-replace)) ;; may only happen when substituting for a var that doesn't appear in any other literal
        ;;No change, since nodenum-to-replace does not appear in any literal:
        (mv (erp-nil)
            literal-nodenums ;; the original literal-nodenums (so that the order is the same)
            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (translation-array (make-empty-array 'translation-array (+ 1 max-literal-nodenum)))
       ;; Mark nodenum-to-replace to be replaced by new-nodenum:
       (translation-array (aset1 'translation-array translation-array nodenum-to-replace new-nodenum))
       ;; Rebuild all the literals, and their supporters, with the substitution applied:
       ((mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (rebuild-nodes-with-var-subst sorted-literal-nodenums ;; initial worklist
                                      translation-array
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((when erp) (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ;; Look up the possibly-new nodes that represent the literals:
       ((mv changed-literal-nodenums
            unchanged-literal-nodenums)
        (translate-literals literal-nodenums ;; could use sorted-literal-nodenums instead
                         translation-array
                         nil nil)))
    (mv (erp-nil)
        ;; We put the changed nodes first, in the hope that we will use them to
        ;; substitute next, creating a slightly larger term, and so on.  The
        ;; unchanged-literal-nodenums here got reversed wrt the input, so if
        ;; we had a bad ordering last time, we may have a good ordering this
        ;; time:
        (append changed-literal-nodenums unchanged-literal-nodenums)
        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm len-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (not (mv-nth 0 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
           (equal (len (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                  (len literal-nodenums)))
  :hints (("Goal" :in-theory (enable rebuild-literals-with-substitution))))

(local (in-theory (enable all-integerp-when-all-natp
                          natp-of-+-of-1-alt))) ;for the call of def-dag-builder-theorems just below

(def-dag-builder-theorems
  (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)
  (mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((nat-listp literal-nodenums)
         (all-< literal-nodenums dag-len)
         (natp nodenum-to-replace)
         (< nodenum-to-replace dag-len)
         (natp new-nodenum)
         (< new-nodenum dag-len)))

;gen?
(defthm nat-listp-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp nodenum-to-replace)
                (nat-listp acc)
                (natp new-nodenum)
                (< new-nodenum dag-len)
                ;; (not (mv-nth 0 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                )
           (nat-listp (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))

(defthm true-listp-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (true-listp literal-nodenums)
           (true-listp (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))

(defthm all-<-of-mv-nth-1-of-rebuild-literals-with-substitution
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp nodenum-to-replace)
                (< nodenum-to-replace dag-len)
                (nat-listp acc)
                (natp new-nodenum)
                (< new-nodenum dag-len)
                ;; (not (mv-nth 0 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum)))
                (all-< acc dag-len)
                )
           (all-< (mv-nth 1 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))
                  (mv-nth 3 (rebuild-literals-with-substitution literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist nodenum-to-replace new-nodenum))))
  :hints (("Goal" :in-theory (e/d (rebuild-literals-with-substitution reverse-becomes-reverse-list) (;REVERSE-REMOVAL
                                                                                                     natp)))))
