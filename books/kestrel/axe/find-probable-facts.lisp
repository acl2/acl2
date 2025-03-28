; Finding likely facts to break down a proof (legacy version)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also find-probable-facts-simple.lisp

(include-book "find-probable-facts-common")
(include-book "evaluate-test-case") ; has skip-proofs
(include-book "kestrel/utilities/print-levels" :dir :system)
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/greater-than-or-equal-len" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))

(local (in-theory (e/d (acl2-numberp-when-natp) (natp))))

;; Returns (mv alist unused-nodes).
;; Only for nodes that are not :unused.
(defund initial-node-to-value-alist (n len array-name array alist-acc unused-nodes-acc)
  (declare (xargs :guard (and (array1p array-name array)
                              (natp n)
                              (natp len)
                              (<= n (+ 1 len))
                              ;; (alistp alist-acc)
                              ;; (nat-listp unused-nodes-acc)
                              (<= len (alen1 array-name array)))
                  :measure (nfix (+ 1 (- len n)))
                  :split-types t
                  :hints (("Goal" :in-theory (enable natp))))
           (type (integer 0 *) n len))
  (if (or (<= len n)
          ;; for termination:
          (not (mbt (and (natp n)
                         (natp len)))))
      (mv alist-acc unused-nodes-acc)
    (let ((val (aref1 array-name array n)))
      (mv-let (alist-acc unused-nodes-acc)
        (if (eq val :unused)
            (mv alist-acc (cons n unused-nodes-acc))
          (mv (acons-fast n val alist-acc) unused-nodes-acc))
        (initial-node-to-value-alist (+ 1 n) len array-name array alist-acc unused-nodes-acc)))))

(local
  (defthm initial-node-to-value-alist-return-type
    (implies (and (natp n)
                  (alistp alist-acc)
                  (all-< (strip-cars alist-acc) len)
                  (nat-listp (strip-cars alist-acc))
                  (nat-listp unused-nodes-acc)
                  (all-< unused-nodes-acc len))
             (mv-let (alist unused-nodes)
               (initial-node-to-value-alist n len array-name array alist-acc unused-nodes-acc)
               (and (alistp alist)
                    (nat-listp (strip-cars alist))
                    (all-< (strip-cars alist) len)
                    (nat-listp unused-nodes)
                    (all-< unused-nodes len))))
    :hints (("Goal" :in-theory (enable initial-node-to-value-alist)))))

(local
  (defthm initial-node-to-value-alist-return-type-corollary
    (implies (and (<= len bound)
                  (natp n)
                  (alistp alist-acc)
                  (all-< (strip-cars alist-acc) len)
                  (nat-listp (strip-cars alist-acc))
                  (nat-listp unused-nodes-acc)
                  (all-< unused-nodes-acc len))
             (mv-let (alist unused-nodes)
               (initial-node-to-value-alist n len array-name array alist-acc unused-nodes-acc)
               (and (all-< (strip-cars alist) bound)
                    (all-< unused-nodes bound))))
    :hints (("Goal" :use initial-node-to-value-alist-return-type
             :in-theory (disable initial-node-to-value-alist-return-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm all-consp-when-alistp
    (implies (alistp x) (all-consp x))
    :hints (("Goal" :in-theory (enable all-consp alistp)))))

(local
  (defthm true-listp-when-alistp
    (implies (alistp x) (true-listp x))
    :hints (("Goal" :in-theory (enable alistp)))))

;; Assumes the TEST-CASE-ARRAY gives values for the current test case to all nodes below DAG-LEN.
;; Returns (mv probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes).
(defund initial-probable-facts (dag-len test-case-array-name test-case-array)
  (declare (xargs :guard (and (array1p test-case-array-name test-case-array)
                              (natp dag-len)
                              (<= dag-len (alen1 test-case-array-name test-case-array)))))
  (mv-let (node-to-value-alist never-used-nodes)
    (initial-node-to-value-alist 0 dag-len test-case-array-name test-case-array nil nil)
    (let* (;; We sort here just to group entries with the same value together:
           (sorted-node-to-value-alist (merge-sort-lexorder-of-cdrs node-to-value-alist))
           (num-never-used-nodes (len never-used-nodes)))
      (mv-let (probably-equal-node-sets singleton-count probably-constant-node-alist)
        (initial-probable-facts-aux sorted-node-to-value-alist nil 0 nil)
        (mv (if (<= 2 num-never-used-nodes)
                (cons never-used-nodes probably-equal-node-sets)
              probably-equal-node-sets)
            (if (equal 1 num-never-used-nodes)
                (+ 1 singleton-count)
              singleton-count)
            probably-constant-node-alist
            never-used-nodes)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-initial-probable-facts
   (implies (and (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 (<= dag-len bound))
            (all-all-< (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array)) bound))
   :hints (("Goal" :in-theory (enable initial-probable-facts)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-initial-probable-facts
;;   (implies (and (array1p test-case-array-name test-case-array)
;;                 (natp dag-len)
;;                 (<= dag-len (alen1 test-case-array-name test-case-array))
;;                 )
;;            (all-consp (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array))))
;;   :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
  (defthm all->=-len-of-mv-nth-0-of-initial-probable-facts
    (all->=-len (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array)) 2)
    :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-list-listp (mv-nth 0 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm natp-of-mv-nth-1-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (natp (mv-nth 1 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (e/d (initial-probable-facts) (natp))))))

(local
 (defthm alistp-of-mv-nth-2-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (alistp (mv-nth 2 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-2-of-initial-probable-facts
   (implies (and (<= dag-len bound)
                 (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 )
            (all-< (strip-cars (mv-nth 2 (initial-probable-facts dag-len test-case-array-name test-case-array)))
                   bound))
   :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-2-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-listp (strip-cars (mv-nth 2 (initial-probable-facts dag-len test-case-array-name test-case-array)))))
  :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm nat-listp-of-mv-nth-3-of-initial-probable-facts
  (implies (and (array1p test-case-array-name test-case-array)
                (natp dag-len)
                (<= dag-len (alen1 test-case-array-name test-case-array))
                )
           (nat-listp (mv-nth 3 (initial-probable-facts dag-len test-case-array-name test-case-array))))
  :hints (("Goal" :in-theory (enable initial-probable-facts)))))

(local
 (defthm all-<-of-mv-nth-3-of-initial-probable-facts
   (implies (and (<= dag-len bound)
                 (array1p test-case-array-name test-case-array)
                 (natp dag-len)
                 (<= dag-len (alen1 test-case-array-name test-case-array))
                 )
            (all-< (mv-nth 3 (initial-probable-facts dag-len test-case-array-name test-case-array)) bound))
   :hints (("Goal" :in-theory (enable initial-probable-facts)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-val-other-than (val nodenums test-case-array-name test-case-array)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (array1p test-case-array-name test-case-array)
                              (all-< nodenums (alen1 test-case-array-name test-case-array)))))
  (if (endp nodenums)
      nil ;failed to find such a val
    (let* ((nodenum (first nodenums))
           (val2 (aref1 test-case-array-name test-case-array nodenum)))
      (if (equal val val2)
          ;;keep looking:
          (find-val-other-than val (cdr nodenums) test-case-array-name test-case-array)
        ;;we found a difference:
        t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;returns an alist pairing values with nodenum lists
;; ;the alist may include shadowed pairs
;; ;fixme think about :unused nodes
;; (defund test-case-alist-for-set (set test-case-array-name test-case-array acc)
;;   (declare (xargs :guard (and (nat-listp set)
;;                               (array1p test-case-array-name test-case-array)
;;                               (all-< set (alen1 test-case-array-name test-case-array))
;;                               (alistp acc))))
;;   (if (endp set)
;;       acc
;;     (let* ((nodenum (first set))
;;            (value (aref1 test-case-array-name test-case-array nodenum))
;;            (nodes-for-value (lookup-equal value acc)))
;;       (test-case-alist-for-set (cdr set) test-case-array-name test-case-array
;;                                (acons-fast value (cons nodenum nodes-for-value) acc)))))

;; (local
;;  (defthm alistp-of-test-case-alist-for-set
;;    (implies (alistp acc)
;;             (alistp (test-case-alist-for-set set test-case-array-name test-case-array acc)))
;;    :hints (("Goal" :in-theory (enable test-case-alist-for-set)))))

;; (local
;;  (defthm all-consp-of-strip-cdrs-of-test-case-alist-for-set
;;    (implies (all-consp (strip-cdrs acc))
;;             (all-consp (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc))))
;;    :hints (("Goal" :in-theory (enable test-case-alist-for-set)))))

;; (local
;;  (defthm all-all-<-of-strip-cdrs-of-test-case-alist-for-set
;;    (implies (and (nat-listp set)
;;                  (array1p test-case-array-name test-case-array)
;;                  (all-< set (alen1 test-case-array-name test-case-array))
;;                  (alistp acc)
;;                  (all-all-< (strip-cdrs acc) bound)
;;                  (<= (alen1 test-case-array-name test-case-array) bound))
;;             (all-all-< (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc)) bound))
;;    :hints (("Goal" :in-theory (enable test-case-alist-for-set all-all-<)))))

;; (local
;;  (defthm nat-list-listp-of-strip-cdrs-of-test-case-alist-for-set
;;    (implies (and (nat-listp set)
;;                  (array1p test-case-array-name test-case-array)
;;                  (all-< set (alen1 test-case-array-name test-case-array))
;;                  (alistp acc)
;;                  (NAT-LIST-LISTP (STRIP-CDRS ACC)))
;;             (nat-list-listp (strip-cdrs (test-case-alist-for-set set test-case-array-name test-case-array acc))))
;;    :hints (("Goal" :in-theory (enable test-case-alist-for-set nat-list-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv alist unused-nodes) where alist is the node-to-value-alist for the nodes in the set.
;; Also returns, separately, the list of nodes that are not :unused.
(defund node-to-value-alist-for-set (nodenums array-name array alist-acc unused-nodes-acc)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (array1p array-name array)
                              (all-< nodenums (alen1 array-name array))
                              ;; (alistp alist-acc)
                              ;; (nat-listp unused-nodes-acc)
                              )))
  (if (endp nodenums)
      (mv alist-acc unused-nodes-acc) ; probably no need to reverse these
    (let* ((nodenum (first nodenums))
           (val (aref1 array-name array nodenum)))
      (mv-let (alist-acc unused-nodes-acc)
        (if (eq val :unused)
            (mv alist-acc (cons nodenum unused-nodes-acc))
          (mv (acons-fast nodenum val alist-acc) unused-nodes-acc))
        (node-to-value-alist-for-set (rest nodenums) array-name array alist-acc unused-nodes-acc)))))

(local
  (defthm node-to-value-alist-for-set-return-type
    (implies (and (nat-listp nodenums)
                  (all-< nodenums len)
                  (alistp alist-acc)
                  (all-< (strip-cars alist-acc) len)
                  (nat-listp (strip-cars alist-acc))
                  (nat-listp unused-nodes-acc)
                  (all-< unused-nodes-acc len))
             (mv-let (alist unused-nodes)
               (node-to-value-alist-for-set nodenums array-name array alist-acc unused-nodes-acc)
               (and (alistp alist)
                    (nat-listp (strip-cars alist))
                    (all-< (strip-cars alist) len)
                    (nat-listp unused-nodes)
                    (all-< unused-nodes len))))
    :hints (("Goal" :in-theory (enable node-to-value-alist-for-set)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;takes a set and adds zero or more sets to acc (also returns a new singleton count)
;returns (mv acc new-singleton-count change-flg)
;set should have at least two elements
;should not return singletons or empty sets
;most of the time, this won't be able to distinguish any nodes and so will return (list set) - we try to make that case fast (don't recons the whole set)...
;inline this?
(defund try-to-split-set (set test-case-array-name test-case-array print acc)
  (declare (xargs :guard (and (nat-listp set)
                              (consp set)
                              (array1p test-case-array-name test-case-array)
                              (print-levelp print)
                              (all-< set (alen1 test-case-array-name test-case-array))
                              (nat-list-listp acc))
                  :guard-hints (("Goal" :in-theory (enable true-listp-when-nat-list-listp)))))
  (let* ((first-nodenum (first set))
         (first-val (aref1 test-case-array-name test-case-array first-nodenum))
         (need-to-splitp (find-val-other-than first-val (rest set) test-case-array-name test-case-array)))
    (if (not need-to-splitp)
        ;;in this case we don't recons the whole set
        (mv (cons set acc) 0 nil)
      (b* ((- (and print (cw "~% (Splitting a set of ~x0 nodes.)" (len set))))
           ((mv node-to-value-alist unused-nodes)
            (node-to-value-alist-for-set set test-case-array-name test-case-array nil nil))
           ;; to group nodes with similar values:
           (node-to-value-alist (merge-sort-lexorder-of-cdrs node-to-value-alist))
           ((mv acc singleton-count)
            (group-nodes-by-value node-to-value-alist acc 0))
           (num-unused-nodes (len unused-nodes)))
        (mv (if (<= 2 num-unused-nodes)
                (cons unused-nodes acc)
              acc)
            (if (equal 1 num-unused-nodes)
                (+ 1 singleton-count)
              singleton-count)
            t)))))

;; (local
;;  (defthm true-listp-of-mv-nth-0-of-try-to-split-set
;;    (implies (true-listp acc)
;;             (true-listp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
;;    :rule-classes :type-prescription
;;    :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 ;(consp set)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc))
            (nat-list-listp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm all->=-len-of-mv-nth-0-of-try-to-split-set
   (implies (and (<= 2 (len set))
                 (all->=-len acc 2))
            (all->=-len (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc)) 2))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-try-to-split-set
;;    (implies (and (nat-listp set)
;;                  (consp set)
;;                  (array1p test-case-array-name test-case-array)
;;                  ;; print
;;                  (all-< set (alen1 test-case-array-name test-case-array))
;;                  (true-listp acc)
;;                  (nat-list-listp acc)
;;                  (all-consp acc))
;;             (all-consp (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))))
;;    :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-try-to-split-set
   (implies (and (nat-listp set)
                 (all-< set bound)
                 (array1p test-case-array-name test-case-array)
                 ;; print
                 (all-< set (alen1 test-case-array-name test-case-array))
                 (true-listp acc)
                 (nat-list-listp acc)
                 (all-all-< acc bound)
                 (<= (alen1 test-case-array-name test-case-array) bound)
                 )
            (all-all-< (mv-nth 0 (try-to-split-set set test-case-array-name test-case-array print acc))
                       bound))
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm natp-of-mv-nth-1-of-try-to-split-set
   (natp (mv-nth 1 (try-to-split-set set test-case-array-name test-case-array print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

(local
 (defthm booleanp-of-mv-nth-2-of-try-to-split-set
   (booleanp (mv-nth 2 (try-to-split-set set test-case-array-name test-case-array print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to split the sets using test-case-array.
;; Returns (mv new-sets new-singleton-count changep),
;sets are moved from SETS to ACC.  as they are moved they are split if indicated by this test case.
;sets are lists of nodenums.  each set has length at least 2 (singleton sets are dropped).
(defund update-probably-equal-node-sets (sets test-case-array acc singleton-count-acc print test-case-array-name changep)
  (declare (xargs :guard (and (nat-list-listp sets)
                              (all->=-len sets 2)
                              (array1p test-case-array-name test-case-array)
                              (nat-list-listp acc)
                              (natp singleton-count-acc)
                              (print-levelp print)
                              (all-all-< sets (alen1 test-case-array-name test-case-array))
                              (booleanp changep))
                  :guard-hints (("Goal" :in-theory (enable all-all-<)))))
  (if (endp sets)
      (mv acc singleton-count-acc changep)
    (let* ((set (first sets)))
      (mv-let (acc ;has the new sets appended onto it
                new-singleton-count change-flg-for-this-set)
        (try-to-split-set set test-case-array-name test-case-array print acc)
        (update-probably-equal-node-sets (rest sets)
                                         test-case-array
                                         acc
                                         (+ singleton-count-acc new-singleton-count)
                                         print
                                         test-case-array-name
                                         (or changep change-flg-for-this-set))))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-update-probably-equal-node-sets
   (implies (and (nat-list-listp sets)
                 (nat-list-listp acc)
          ;                (all-consp acc)
               ;;  (all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (nat-list-listp (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

(local
 (defthm all->=-len-of-mv-nth-0-of-update-probably-equal-node-sets
   (implies (and (all->=-len sets 2)
                 (all->=-len acc 2))
            (all->=-len (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep)) 2))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-update-probably-equal-node-sets
;;    (implies (and (nat-list-listp sets)
;;                  (nat-list-listp acc)
;;                  (all-consp acc)
;;                  (all-consp sets)
;;                  (array1p test-case-array-name test-case-array)
;;                  (natp singleton-count-acc)
;;                  ;; print
;;                  (all-all-< sets (alen1 test-case-array-name test-case-array))
;;                  (booleanp changep))
;;             (all-consp (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
;;    :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-update-probably-equal-node-sets
   (implies (and (<= (alen1 test-case-array-name test-case-array) dag-len)
                 (nat-list-listp sets)
                 (nat-list-listp acc)
                 ;;(all-consp acc)
                 ;;(all-consp sets)
                 (array1p test-case-array-name test-case-array)
                 (natp singleton-count-acc)
                 (ALL-ALL-< ACC DAG-LEN)
                 ;; print
                 (all-all-< sets (alen1 test-case-array-name test-case-array))
                 (booleanp changep))
            (all-all-< (mv-nth 0 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))
                       dag-len))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets all-all-<)))))

(local
 (defthm natp-of-mv-nth-1-of-update-probably-equal-node-sets
   (implies (natp singleton-count-acc)
            (natp (mv-nth 1 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets)))))

(local
 (defthm booleanp-of-mv-nth-2-of-update-probably-equal-node-sets
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (update-probably-equal-node-sets sets test-case-array acc singleton-count-acc print test-case-array-name changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Handles nodes that are used on this test case but have not been used on a previous test case.
;Such nodes are moved from the never-used-nodes list to the probably-constant-node-alist, where they are paired with their value on this test case.
;Returns (mv never-used-nodes probably-constant-node-alist changep) where changep remains true if it was initially true.
(defund handle-newly-used-nodes (never-used-nodes ;these are moved to acc or get entries in the alist
                                 probably-constant-node-alist ;;pairs nodenums with probable constants
                                 test-case-array-name test-case-array
                                 acc
                                 changep)
  (declare (xargs :guard (and (nat-listp never-used-nodes)
                              (alistp probably-constant-node-alist)
                              (array1p test-case-array-name test-case-array)
                              (all-< never-used-nodes (alen1 test-case-array-name test-case-array))
                              ;; acc
                              (booleanp changep))))
  (if (endp never-used-nodes)
      (mv acc probably-constant-node-alist changep)
    (let* ((nodenum (first never-used-nodes))
           (value (aref1 test-case-array-name test-case-array nodenum)))
      (if (eq :unused value)
          ;; the node is still unused:
          (handle-newly-used-nodes (rest never-used-nodes)
                                   probably-constant-node-alist
                                   test-case-array-name test-case-array
                                   (cons nodenum acc)
                                   changep)
        ;;the node is used for the first time on this test case:
        (handle-newly-used-nodes (rest never-used-nodes)
                                 (acons-fast nodenum value probably-constant-node-alist)
                                 test-case-array-name test-case-array
                                 acc
                                 t)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp acc))
            (nat-listp (mv-nth 0 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm all-<-of-mv-nth-0-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist)
                 (array1p test-case-array-name test-case-array)
                 (all-< never-used-nodes (alen1 test-case-array-name test-case-array))
                 (all-< never-used-nodes dag-len)
                 (all-< acc dag-len)
                 (booleanp changep))
            (all-< (mv-nth 0 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))
                   dag-len))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm alistp-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (alistp probably-constant-node-alist)
            (alistp (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp (strip-cars probably-constant-node-alist)))
            (nat-listp (strip-cars (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep)))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes
   (implies (and (all-< never-used-nodes bound)
                 (all-< (strip-cars probably-constant-node-alist) bound))
            (all-< (strip-cars (mv-nth 1 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

(local
 (defthm booleanp-of-mv-nth-2-of-handle-newly-used-nodes
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this function drops any pairs which are invalidated by the current test case
;this rebuilds the whole alist - hope that is okay...
;returns (mv probably-constant-node-alist changep)
;fixme might be faster to process more than 1 test case at a time
;every node in probably-constant-node-alist has been used on at least one test case
(defund update-probably-constant-alist (probably-constant-node-alist ;;pairs nodenums with probable constants
                                        test-case-array-name test-case-array
                                        acc ;pairs are moved from probably-constant-node-alist to this
                                        changep)
  (declare (xargs :guard (and (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (array1p test-case-array-name test-case-array)
                              (all-< (strip-cars probably-constant-node-alist)
                                     (alen1 test-case-array-name test-case-array))
                              ;; acc
                              (booleanp changep))))
  (if (endp probably-constant-node-alist)
      (mv acc changep)
    (let* ((pair (first probably-constant-node-alist))
           (nodenum (car pair))
           (probable-value (cdr pair))
           (value-for-this-test-case (aref1 test-case-array-name test-case-array nodenum)))
      (if (or (eq :unused value-for-this-test-case)
              (equal probable-value value-for-this-test-case))
          ;; this test case doesn't invalidate the pair:
          (update-probably-constant-alist (rest probably-constant-node-alist) test-case-array-name test-case-array
                                          (cons pair acc) changep)
        ;; the node is used and the value is different from the value in the alist, so drop the pair:
        (update-probably-constant-alist (rest probably-constant-node-alist) test-case-array-name test-case-array
                                        acc t)))))

(local
 (defthm alistp-of-mv-nth-0-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 ;; (nat-listp (strip-cars probably-constant-node-alist))
                 ;; (array1p test-case-array-name test-case-array)
                 ;; (all-< (strip-cars probably-constant-node-alist)
                 ;;        (alen1 test-case-array-name test-case-array))
                 ;; (nat-listp (strip-cars acc))
                 (alistp acc)
                 ;; (booleanp changep)
                 )
            (alistp (mv-nth 0 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

(local
 (defthm booleanp-of-mv-nth-1-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (alistp acc)
                 (booleanp changep))
            (booleanp (mv-nth 1 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-0-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (booleanp changep))
            (nat-listp (strip-cars (mv-nth 0 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep)))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-0-of-update-probably-constant-alist
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (array1p test-case-array-name test-case-array)
                 (all-< (strip-cars probably-constant-node-alist)
                        (alen1 test-case-array-name test-case-array))
                 (nat-listp (strip-cars acc))
                 (ALL-< (STRIP-CARS ACC) BOUND)
                 (booleanp changep)
                 (<= (alen1 test-case-array-name test-case-array) bound)
                 )
            (all-< (strip-cars (mv-nth 0 (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; run test cases and use them to split probably-equal-node-sets and eliminate probable constants
;; returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist), where test-case-array-alist is valid iff keep-test-casesp is non-nil
;ffixme think about what to do with nodes that are unreachable (don't influence the top node, because of ifs) on a single test case, or on all test cases.  maybe i now handle that?
;now the tests come in randomized?
(defund update-probable-facts-with-test-cases (test-cases
                                               singleton-count
                                               dag-array-name dag-array dag-len
                                               probably-equal-node-sets
                                               never-used-nodes
                                               probably-constant-node-alist
                                               interpreted-function-alist print
                                               test-case-array-name-base
                                               keep-test-casesp
                                               test-case-array-alist
                                               test-case-number
                                               debug-nodes
                                               num-of-last-interesting-test-case)
  (declare (xargs :guard (and (test-casesp test-cases)
                              (natp singleton-count)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (nat-list-listp probably-equal-node-sets)
                              (all->=-len probably-equal-node-sets 2)
                              ;(all-consp probably-equal-node-sets)
                              (all-all-< probably-equal-node-sets dag-len)
                              (nat-listp never-used-nodes)
                              (all-< never-used-nodes dag-len)
                              (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (all-< (strip-cars probably-constant-node-alist) dag-len)
                              (interpreted-function-alistp interpreted-function-alist)
                              (print-levelp print)
                              (symbolp test-case-array-name-base)
                              (booleanp keep-test-casesp)
                              (alistp test-case-array-alist)
                              (natp test-case-number)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes dag-len)
                              (or (null num-of-last-interesting-test-case)
                                  (natp num-of-last-interesting-test-case)))
                  :guard-hints (("Goal" :in-theory (disable natp strip-cars)))))
  (if (or (endp test-cases)
          ;;stop if we've done at least 100 test cases and nothing has happened in the last 90% of them:
          ;;fixme could allow the user to change the 10 and the 100 here:
          (if (and t ;abandon-testing-when-boringp ;(or t abandon-testing-when-boringp)
                   num-of-last-interesting-test-case
                   (<= 100 test-case-number)
                   (<= (* 10 num-of-last-interesting-test-case) test-case-number))
              (prog2$ (cw "(Abandoning testing because nothing interesting is happening.)")
                      t)
            nil))
      (mv t ; all tests passed
          probably-equal-node-sets never-used-nodes probably-constant-node-alist
          (reverse test-case-array-alist) ;new; keeps this in sync with the test cases (or do non-interesting ones get dropped?)
          )
    (b* ((- ;;TODO: Only print when things change?:
          (cw "(Test ~x0 (~x1 total sets, ~x2 singletons, ~x3 constants)"
              test-case-number
              (+ singleton-count (len probably-equal-node-sets)) ;slow? could keep a count?
              singleton-count
              (len probably-constant-node-alist) ;slow?
              ))
         (test-case (first test-cases))
         (test-case-array-name (if keep-test-casesp
                                   (pack$ test-case-array-name-base '- (nat-to-string test-case-number))
                                 ;;if we are not keeping test cases (e.g., because they'd take too much memory), reuse the same array:
                                 test-case-array-name-base))
         ;; Evaluate the test case and ensure the top node is true:
         (test-case-array
          (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist
                                        test-case-array-name
                                        debug-nodes))
         ((when (not test-case-array)) ; some test failed! (rare)
          (mv nil probably-equal-node-sets never-used-nodes probably-constant-node-alist nil))
         (changep nil) ; track whether this test case was interesting
         ;; Update the probably-equal-node-sets:
         ((mv new-sets new-singleton-count changep)
          (update-probably-equal-node-sets probably-equal-node-sets test-case-array nil 0 print test-case-array-name changep))
         ;; Maybe invalidate some probable constants (done before handle-newly-used-nodes, which may add new probable constants):
         ((mv probably-constant-node-alist changep)
          (update-probably-constant-alist probably-constant-node-alist test-case-array-name test-case-array nil changep))
         ;; Handle nodes that are used for the first time on this test case (they become probable constants):
         ((mv never-used-nodes probably-constant-node-alist changep)
          (handle-newly-used-nodes never-used-nodes probably-constant-node-alist test-case-array-name test-case-array nil changep))
         (- (if (and (or (eq print :verbose)
                         (eq print :verbose!))
                     changep) ; todo: use this value to decide whether to keep the test case? maybe keep the first few boring ones so we have enough..
                (cw "~%interesting test case ~x0.)~%" test-case)
              (cw ")~%"))))
      (update-probable-facts-with-test-cases (rest test-cases)
                                             (+ singleton-count new-singleton-count)
                                             dag-array-name dag-array dag-len
                                             new-sets
                                             never-used-nodes
                                             probably-constant-node-alist
                                             interpreted-function-alist print test-case-array-name-base keep-test-casesp
                                             (if keep-test-casesp
                                                 (acons-fast test-case-array-name
                                                             test-case-array
                                                             test-case-array-alist)
                                               nil)
                                             (+ 1 test-case-number)
                                             debug-nodes
                                             (if changep
                                                 test-case-number
                                               num-of-last-interesting-test-case)))))

(local
 (defthm booleanp-of-mv-nth-0-of-update-probable-facts-with-test-cases
   (implies (nat-listp never-used-nodes)
            (booleanp (mv-nth 0 (update-probable-facts-with-test-cases test-cases
                                                                       singleton-count
                                                                       dag-array-name dag-array dag-len
                                                                       probably-equal-node-sets
                                                                       never-used-nodes
                                                                       probably-constant-node-alist
                                                                       interpreted-function-alist print
                                                                       test-case-array-name-base
                                                                       keep-test-casesp
                                                                       test-case-array-alist
                                                                       test-case-number
                                                                       debug-nodes
                                                                       num-of-last-interesting-test-case))))
   :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases)))))

(local
 (defthm nat-list-listp-of-mv-nth-1-of-update-probable-facts-with-test-cases
   (implies (and (test-casesp test-cases)
                 (natp singleton-count)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (< 0 dag-len)
                 (nat-list-listp probably-equal-node-sets)
                ;; (all-consp probably-equal-node-sets)
                 (all-all-< probably-equal-node-sets dag-len)
                 (nat-listp never-used-nodes)
                 (all-< never-used-nodes dag-len)
                 (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (all-< (strip-cars probably-constant-node-alist) dag-len)
                 (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                 (symbolp test-case-array-name-base)
;                (booleanp keep-test-casesp)
                 (alistp test-case-array-alist)
                 (natp test-case-number)
                 (nat-listp debug-nodes)
                 (all-< debug-nodes dag-len)
                 (or (null num-of-last-interesting-test-case)
                     (natp num-of-last-interesting-test-case)))
            (nat-list-listp (mv-nth 1 (update-probable-facts-with-test-cases test-cases
                                                                             singleton-count
                                                                             dag-array-name dag-array dag-len
                                                                             probably-equal-node-sets
                                                                             never-used-nodes
                                                                             probably-constant-node-alist
                                                                             interpreted-function-alist print
                                                                             test-case-array-name-base
                                                                             keep-test-casesp
                                                                             test-case-array-alist
                                                                             test-case-number
                                                                             debug-nodes
                                                                             num-of-last-interesting-test-case))))
   :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases)))))

(local
 (defthm all->=-len-of-mv-nth-1-of-update-probable-facts-with-test-cases
   (implies (and (test-casesp test-cases)
                 (natp singleton-count)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (< 0 dag-len)
                 (nat-list-listp probably-equal-node-sets)
                ;; (all-consp probably-equal-node-sets)
                 (ALL->=-LEN PROBABLY-EQUAL-NODE-SETS 2)
                 (all-all-< probably-equal-node-sets dag-len)
                 (nat-listp never-used-nodes)
                 (all-< never-used-nodes dag-len)
                 (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))
                 (all-< (strip-cars probably-constant-node-alist) dag-len)
                 (interpreted-function-alistp interpreted-function-alist)
                              ;; print
                 (symbolp test-case-array-name-base)
;                (booleanp keep-test-casesp)
                 (alistp test-case-array-alist)
                 (natp test-case-number)
                 (nat-listp debug-nodes)
                 (all-< debug-nodes dag-len)
                 (or (null num-of-last-interesting-test-case)
                     (natp num-of-last-interesting-test-case)))
            (all->=-len (mv-nth 1 (update-probable-facts-with-test-cases test-cases
                                                                         singleton-count
                                                                         dag-array-name dag-array dag-len
                                                                         probably-equal-node-sets
                                                                         never-used-nodes
                                                                         probably-constant-node-alist
                                                                         interpreted-function-alist print
                                                                         test-case-array-name-base
                                                                         keep-test-casesp
                                                                         test-case-array-alist
                                                                         test-case-number
                                                                         debug-nodes
                                                                         num-of-last-interesting-test-case))
                        2))
   :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases)))))

(local
 (defthm nat-listp-of-mv-nth-2-of-update-probable-facts-with-test-cases
   (implies (nat-listp never-used-nodes)
            (nat-listp (mv-nth 2 (update-probable-facts-with-test-cases test-cases
                                                                        singleton-count
                                                                        dag-array-name dag-array dag-len
                                                                        probably-equal-node-sets
                                                                        never-used-nodes
                                                                        probably-constant-node-alist
                                                                        interpreted-function-alist print
                                                                        test-case-array-name-base
                                                                        keep-test-casesp
                                                                        test-case-array-alist
                                                                        test-case-number
                                                                        debug-nodes
                                                                        num-of-last-interesting-test-case))))
   :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases)))))

(local
 (defthm alistp-of-mv-nth-3-of-update-probable-facts-with-test-cases
   (implies (alistp probably-constant-node-alist)
            (alistp (mv-nth 3 (update-probable-facts-with-test-cases test-cases
                                                                     singleton-count
                                                                     dag-array-name dag-array dag-len
                                                                     probably-equal-node-sets
                                                                     never-used-nodes
                                                                     probably-constant-node-alist
                                                                     interpreted-function-alist print
                                                                     test-case-array-name-base
                                                                     keep-test-casesp
                                                                     test-case-array-alist
                                                                     test-case-number
                                                                     debug-nodes
                                                                     num-of-last-interesting-test-case))))
   :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Repeatedly evaluates a test case and then uses it to split probably-equal node sets and eliminate probably-constant nodes.
;; Returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist),
;; where PROBABLY-EQUAL-NODE-SETS includes nodes believed to be constant and probably-constant-node-alist pairs nodes with the constants they seem to be equal to
;; and test-case-array-alist is valid iff keep-test-casesp is non-nil and pairs array names with arrays that give values to all the nodes.
;todo: should this return the used test cases (I guess they can be extracted from the test-case-array-alist)?
(defund find-probable-facts (miter-array-name ; todo: rename these?
                             miter-array
                             miter-len
                             miter-depth ; used to ensure a non-clashing array name
                             test-cases ;each test case gives values to the input vars (there may be more here than we want to use..) ;; TODO: Make them on demand
                             interpreted-function-alist
                             print
                             keep-test-casesp
                             debug-nodes)
  (declare (xargs :guard (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                              (< 0 miter-len)
                              (natp miter-depth)
                              (test-casesp test-cases)
                              (interpreted-function-alistp interpreted-function-alist)
                              (print-levelp print)
                              (booleanp keep-test-casesp)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes miter-len))
                  :guard-hints (("Goal" :in-theory (disable natp)))))
  (b* ((test-cases test-cases ;(firstn 1024 test-cases) ;Thu Feb 17 20:25:10 2011
                   )
       (- (cw "(Evaluating test cases (keep-test-casesp is ~x0):~%" keep-test-casesp))
       ;; use the first test case to make initial-probably-equal-node-sets (I think this is faster than starting with one huge set and then splitting it):
       (- (cw "(Test 0 (initial)"))
       (test-case-array-name-base (pack$ 'test-case-array-depth- miter-depth '-)) ;using the depth is new
       (first-test-case-array-name (pack$ test-case-array-name-base 0))
       (test-case-array
        (evaluate-and-check-test-case (first test-cases)
                                      miter-array-name
                                      miter-array
                                      miter-len
                                      interpreted-function-alist
                                      first-test-case-array-name
                                      debug-nodes))
       ((when (not test-case-array)) ; actually, a hard error will have already been thrown
        (mv nil                      ; all-passedp
            nil nil nil nil))
       ((mv initial-probably-equal-node-sets
            initial-singleton-count
            initial-probably-constant-node-alist ;pairs nodenums used on the first test case with their values
            initial-never-used-nodes)
        (initial-probable-facts miter-len first-test-case-array-name test-case-array))
       ;;((array-to-alist first-test-case-array-name test-case-array miter-len)) ;slow?
       ;;save the first test case in the test-case-array-alist:
       (test-case-array-alist (if keep-test-casesp
                                  (acons-fast first-test-case-array-name test-case-array nil)
                                nil))
       (- (cw ")~%"))
       ;;use additional test cases to split the sets and update the probable constant facts:
       ((mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist)
        (update-probable-facts-with-test-cases (rest test-cases)
                                               initial-singleton-count
                                               miter-array-name
                                               miter-array
                                               miter-len
                                               initial-probably-equal-node-sets
                                               initial-never-used-nodes
                                               initial-probably-constant-node-alist
                                               interpreted-function-alist
                                               print
                                               test-case-array-name-base
                                               keep-test-casesp ;just check whether test-case-array-alist is nil?
                                               test-case-array-alist
                                               1 ;test case number
                                               debug-nodes
                                               nil ;;number of last interesting test case
                                               ))
       (probably-equal-node-sets (remove-set-of-unused-nodes probably-equal-node-sets never-used-nodes nil)) ;TODO: could try to prove that these are really unused (could give interesting counterexamples)
       (- (cw ")~%")))
    (mv all-passedp
        probably-equal-node-sets
        never-used-nodes
        probably-constant-node-alist
        test-case-array-alist)))

(defthm booleanp-of-mv-nth-0-of-find-probable-facts
  (implies (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                (< 0 miter-len)
                (natp miter-depth)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
;                (booleanp keep-test-casesp)
                (nat-listp debug-nodes)
                (all-< debug-nodes miter-len))
           (booleanp (mv-nth 0 (find-probable-facts miter-array-name miter-array miter-len
                                                    miter-depth
                                                    test-cases
                                                    interpreted-function-alist print keep-test-casesp
                                                    debug-nodes))))
  :hints (("Goal" :in-theory (enable find-probable-facts))))

(defthm nat-list-listp-of-mv-nth-1-of-find-probable-facts
  (implies (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                (< 0 miter-len)
                (natp miter-depth)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
 ;               (booleanp keep-test-casesp)
                (nat-listp debug-nodes)
                (all-< debug-nodes miter-len))
           (nat-list-listp (mv-nth 1 (find-probable-facts miter-array-name miter-array miter-len
                                                          miter-depth
                                                          test-cases
                                                          interpreted-function-alist print keep-test-casesp
                                                          debug-nodes))))
  :hints (("Goal" :in-theory (enable find-probable-facts))))

;; Each probably-equal-node-set has at least 2 nodes
(defthm all->=-len-of-mv-nth-1-of-find-probable-facts
  (implies (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                (< 0 miter-len)
                (natp miter-depth)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
  ;              (booleanp keep-test-casesp)
                (nat-listp debug-nodes)
                (all-< debug-nodes miter-len))
           (all->=-len (mv-nth 1 (find-probable-facts miter-array-name miter-array miter-len
                                                      miter-depth
                                                      test-cases
                                                      interpreted-function-alist print keep-test-casesp
                                                      debug-nodes))
                       2))
  :hints (("Goal" :in-theory (enable find-probable-facts))))

(defthm nat-listp-of-mv-nth-2-of-find-probable-facts
  (implies (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                (< 0 miter-len)
                (natp miter-depth)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
   ;             (booleanp keep-test-casesp)
                (nat-listp debug-nodes)
                (all-< debug-nodes miter-len))
           (nat-listp (mv-nth 2 (find-probable-facts miter-array-name miter-array miter-len miter-depth test-cases interpreted-function-alist print keep-test-casesp debug-nodes))))
  :hints (("Goal" :in-theory (enable find-probable-facts))))

(defthm alistp-of-mv-nth-3-of-find-probable-facts
  (implies (and (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                (< 0 miter-len)
                (natp miter-depth)
                (test-casesp test-cases)
                (interpreted-function-alistp interpreted-function-alist)
    ;            (booleanp keep-test-casesp)
                (nat-listp debug-nodes)
                (all-< debug-nodes miter-len))
           (alistp (mv-nth 3 (find-probable-facts miter-array-name miter-array miter-len miter-depth test-cases interpreted-function-alist print keep-test-casesp debug-nodes))))
  :hints (("Goal" :in-theory (enable find-probable-facts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns (mv all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist).
;; ;; Only used to compute the facts for printing, since usually we have a dag-array rather than a dag.
;; (defund find-probable-facts-for-dag (dag
;;                                      test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
;;                                      interpreted-function-alist
;;                                      ;print
;;                                      keep-test-casesp
;;                                      ;debug-nodes
;;                                      )
;;   (declare (xargs :guard (and (pseudo-dagp dag)
;;                               (<= (len dag) *max-1d-array-length*)
;;                               (test-casesp test-cases)
;;                               (interpreted-function-alistp interpreted-function-alist)
;;                               (booleanp keep-test-casesp))))
;;   (let* ((miter-array-name 'probable-facts-array)
;;          (miter-array (make-into-array miter-array-name dag))
;;          (miter-len (len dag)))
;;     (find-probable-facts miter-array-name
;;                          miter-array
;;                          miter-len
;;                          0 ; miter-depth
;;                          test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
;;                          interpreted-function-alist
;;                          nil ; print
;;                          keep-test-casesp
;;                          nil ; debug-nodes
;;                          )))

;; (local
;;  (defthm booleanp-of-mv-nth-0-of-find-probable-facts-for-dag
;;    (implies (and (pseudo-dagp dag)
;;                  (<= (len dag) *max-1d-array-length*)
;;                  (test-casesp test-cases)
;;                  (interpreted-function-alistp interpreted-function-alist)
;; ;                (booleanp keep-test-casesp)
;;                  )
;;             (booleanp (mv-nth 0 (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp))))
;;    :hints (("Goal" :in-theory (enable find-probable-facts-for-dag)))))

;; (local
;;  (defthm nat-list-listp-of-mv-nth-1-of-find-probable-facts-for-dag
;;    (implies (and (pseudo-dagp dag)
;;                  (<= (len dag) *max-1d-array-length*)
;;                  (test-casesp test-cases)
;;                  (interpreted-function-alistp interpreted-function-alist)
;; ;                (booleanp keep-test-casesp)
;;                  )
;;             (nat-list-listp (mv-nth 1 (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp))))
;;    :hints (("Goal" :in-theory (enable find-probable-facts-for-dag)))))

;; (local
;;  (defthm all->=-len-of-mv-nth-1-of-find-probable-facts-for-dag
;;    (implies (and (pseudo-dagp dag)
;;                  (<= (len dag) *max-1d-array-length*)
;;                  (test-casesp test-cases)
;;                  (interpreted-function-alistp interpreted-function-alist)
;; ;                (booleanp keep-test-casesp)
;;                  )
;;             (all->=-len (mv-nth 1 (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp)) 2))
;;    :hints (("Goal" :in-theory (enable find-probable-facts-for-dag)))))

;; (local
;;  (defthm nat-listp-of-mv-nth-2-of-find-probable-facts-for-dag
;;    (implies (and (pseudo-dagp dag)
;;                  (<= (len dag) *max-1d-array-length*)
;;                  (test-casesp test-cases)
;;                  (interpreted-function-alistp interpreted-function-alist)
;; ;                (booleanp keep-test-casesp)
;;                  )
;;             (nat-listp (mv-nth 2 (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp))))
;;    :hints (("Goal" :in-theory (enable find-probable-facts-for-dag)))))

;; (local
;;  (defthm alistp-of-mv-nth-3-of-find-probable-facts-for-dag
;;    (implies (and (pseudo-dagp dag)
;;                  (<= (len dag) *max-1d-array-length*)
;;                  (test-casesp test-cases)
;;                  (interpreted-function-alistp interpreted-function-alist)
;; ;                (booleanp keep-test-casesp)
;;                  )
;;             (alistp (mv-nth 3 (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp))))
;;    :hints (("Goal" :in-theory (enable find-probable-facts-for-dag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; todo: combine with the function below?
;; (defund print-probable-facts-for-test-cases (dag
;;                                              test-cases ;each test case gives values to the input vars (there may be more here than we want to use..)
;;                                              interpreted-function-alist
;;                                              keep-test-casesp)
;;   (declare (xargs :guard (and (pseudo-dagp dag)
;;                               (<= (len dag) *max-1d-array-length*)
;;                               (test-casesp test-cases)
;;                               (interpreted-function-alistp interpreted-function-alist)
;;                               (booleanp keep-test-casesp))
;;                   :guard-hints (("Goal" :in-theory (enable true-listp-when-nat-list-listp
;;                                                            all-nat-listp-when-nat-list-listp)))))
;;   (mv-let (all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-array-alist)
;;     (find-probable-facts-for-dag dag test-cases interpreted-function-alist keep-test-casesp)
;;     ;(declare (ignore test-case-array-alist))
;;     (prog2$ (print-probable-info all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist)
;;             ;; Do we always want to print this one?:
;;             (cw "test-case-array-alist: ~x0.~%" test-case-array-alist))))

;; ;; Just prints the probable facts for a DAG (e.g., for examination to find new rewrite rules).
;; ;; Returns rand.
;; (defund print-probable-facts-for-dag (dag test-case-count test-case-type-alist interpreted-fns keep-test-casesp wrld rand)
;;   (declare (xargs :guard (and (pseudo-dagp dag)
;;                               (<= (len dag) *max-1d-array-length*)
;;                               (natp test-case-count)
;;                               (test-case-type-alistp test-case-type-alist)
;;                               (symbol-listp interpreted-fns)
;;                               (booleanp keep-test-casesp)
;;                               (plist-worldp wrld))
;;                   :stobjs rand))
;;   (b* (((mv erp test-cases rand)
;;         (make-test-cases test-case-count test-case-type-alist nil rand))
;;        ((when erp) (cw "Error making test cases.") rand)
;;        (- (print-probable-facts-for-test-cases dag test-cases (make-interpreted-function-alist interpreted-fns wrld) keep-test-casesp))
;;        )
;;     rand))
