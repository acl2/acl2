; Finding likely facts to break down a proof (simple version)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "find-probable-facts-common")
(include-book "evaluate-test-case-simple")
(include-book "interpreted-function-alists")
(include-book "kestrel/utilities/with-local-stobjs" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/utilities/greater-than-or-equal-len" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))

(local (in-theory (e/d (true-listp-when-nat-listp-rewrite
                        true-listp-when-nat-list-listp
                        ;;true-listp-when-alistp
                        acl2-numberp-when-natp
                        )
                       (plist-worldp
                        SYMBOL-LISTP
                        natp
                        ALL->=-LEN))))


(local
  (defthm not-<-of-len-of-car-when-all->=-len
    (implies (and (all->=-len x n)
                  (natp n)
                  (consp x))
             (not (< (LEN (CAR x)) N)))
    :hints (("Goal" :in-theory (enable ALL->=-LEN)))))

(local
  (defthm all->=-len-of-cons
    (equal (all->=-len (cons a x) n)
           (and (>=-len a n)
                (all->=-len x n)))
    :hints (("Goal" :induct (all->=-len x n)
             :in-theory (enable all->=-len)))))

;; (local
;;   (defthm all-consp-when-all->=-len-of-2
;;     (implies (all->=-len x 2)
;;              (all-consp x))
;;     :hints (("Goal" :in-theory (enable all->=-len all-consp)))))


;dup
(local
  (defthm true-listp-when-alistp
    (implies (alistp x) (true-listp x))
    :hints (("Goal" :in-theory (enable alistp)))))

;; since merge-sort-lexorder-of-cdrs has a guard that calls all-consp
;dup
(local
  (defthm all-consp-when-alistp
    (implies (alistp x) (all-consp x))
    :hints (("Goal" :in-theory (enable all-consp alistp)))))

;; Returns (mv alist unused-nodes).
;; Only for nodes that are not unused.
(defund initial-node-to-value-alist-simple (n len test-case-stobj alist-acc unused-nodes-acc)
  (declare (xargs :guard (and (natp n)
                              (natp len)
                              (<= n (+ 1 len))
                              ;; (alistp alist-acc)
                              ;; (nat-listp unused-nodes-acc)
                              (= len (node-val-array-length test-case-stobj))
                              (= len (done-node-array-length test-case-stobj)))
                  :measure (nfix (+ 1 (- len n)))
                  :stobjs test-case-stobj
                  :split-types t
                  :hints (("Goal" :in-theory (enable natp))))
           (type (integer 0 *) n len))
  (if (or (<= len n)
          ;; for termination:
          (not (mbt (and (natp n)
                         (natp len)))))
      (mv alist-acc unused-nodes-acc)
    (let ((val (node-val-arrayi n test-case-stobj))
          (done (done-node-arrayi n test-case-stobj)))
      (mv-let (alist-acc unused-nodes-acc)
        (if done
            (mv (acons-fast n val alist-acc) unused-nodes-acc)
          ;; not done means the node was not used on this test case
          (mv alist-acc (cons n unused-nodes-acc)))
        (initial-node-to-value-alist-simple (+ 1 n) len test-case-stobj alist-acc unused-nodes-acc)))))

(local
  (defthm initial-node-to-value-alist-simple-return-type
    (implies (and (natp n)
                  (alistp alist-acc)
                  (all-< (strip-cars alist-acc) len)
                  (nat-listp (strip-cars alist-acc))
                  (nat-listp unused-nodes-acc)
                  (all-< unused-nodes-acc len))
             (mv-let (alist unused-nodes)
               (initial-node-to-value-alist-simple n len test-case-stobj alist-acc unused-nodes-acc)
               (and (alistp alist)
                    (nat-listp (strip-cars alist))
                    (all-< (strip-cars alist) len)
                    (nat-listp unused-nodes)
                    (all-< unused-nodes len))))
    :hints (("Goal" :in-theory (enable initial-node-to-value-alist-simple)))))

(local
  (defthm initial-node-to-value-alist-simple-return-type-corollary
    (implies (and (<= len bound)
                  (natp n)
                  (alistp alist-acc)
                  (all-< (strip-cars alist-acc) len)
                  (nat-listp (strip-cars alist-acc))
                  (nat-listp unused-nodes-acc)
                  (all-< unused-nodes-acc len))
             (mv-let (alist unused-nodes)
               (initial-node-to-value-alist-simple n len test-case-stobj alist-acc unused-nodes-acc)
               (and (all-< (strip-cars alist) bound)
                    (all-< unused-nodes bound))))
    :hints (("Goal" :use initial-node-to-value-alist-simple-return-type
             :in-theory (disable initial-node-to-value-alist-simple-return-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assumes the TEST-CASE-ARRAY gives values for the current test case to all nodes below DAG-LEN.
;; Returns (mv probably-equal-node-sets singleton-count probably-constant-node-alist never-used-nodes).
(defund initial-probable-facts-simple (len test-case-stobj)
  (declare (xargs :guard (and (natp len)
                              (= len (node-val-array-length test-case-stobj))
                              (= len (done-node-array-length test-case-stobj)))
                  :stobjs test-case-stobj))
  (mv-let (node-to-value-alist never-used-nodes)
    (initial-node-to-value-alist-simple 0 len test-case-stobj nil nil)
    (let (;; We sort here just to group entries with the same value together:
          (node-to-value-alist (merge-sort-lexorder-of-cdrs node-to-value-alist))
          (num-never-used-nodes (len never-used-nodes)))
      (mv-let (probably-equal-node-sets singleton-count probably-constant-node-alist)
        (initial-probable-facts-aux node-to-value-alist nil 0 nil)
        (mv (if (<= 2 num-never-used-nodes)
                (cons never-used-nodes probably-equal-node-sets)
              probably-equal-node-sets)
            (if (equal 1 num-never-used-nodes)
                (+ 1 singleton-count)
              singleton-count)
            probably-constant-node-alist
            never-used-nodes)))))

(local
  (defthm all-all-<-of-mv-nth-0-of-initial-probable-facts-simple
    (implies (and; (test-case-stobjp test-case-stobj)
                  (natp len)
                  (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                  (<= len bound))
             (all-all-< (mv-nth 0 (initial-probable-facts-simple len test-case-stobj)) bound))
    :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

;; implied by the below
;; (local
;;  (defthm all-consp-of-mv-nth-0-of-initial-probable-facts-simple
;;   (implies (and ;(test-case-stobjp test-case-stobj)
;;                 (natp len)
;;                 (= len (node-val-array-length test-case-stobj))
;;                   (= len (done-node-array-length test-case-stobj))
;;                 )
;;            (all-consp (mv-nth 0 (initial-probable-facts-simple len test-case-stobj))))
;;   :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
  (defthm all->=-len-of-mv-nth-0-of-initial-probable-facts-simple
    (implies (and ;(test-case-stobjp test-case-stobj)
               (natp len)
               (= len (node-val-array-length test-case-stobj))
               (= len (done-node-array-length test-case-stobj))
               )
             (all->=-len (mv-nth 0 (initial-probable-facts-simple len test-case-stobj)) 2))
    :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-initial-probable-facts-simple
  (implies (and ;(test-case-stobjp test-case-stobj)
                (natp len)
                (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                )
           (nat-list-listp (mv-nth 0 (initial-probable-facts-simple len test-case-stobj))))
  :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
 (defthm natp-of-mv-nth-1-of-initial-probable-facts-simple
  (implies (and ;(test-case-stobjp test-case-stobj)
                (natp len)
                (= len (node-val-array-length test-case-stobj))
                (= len (done-node-array-length test-case-stobj))
                )
           (natp (mv-nth 1 (initial-probable-facts-simple len test-case-stobj))))
  :hints (("Goal" :in-theory (e/d (initial-probable-facts-simple) (natp))))))

(local
 (defthm alistp-of-mv-nth-2-of-initial-probable-facts-simple
  (implies (and ;(test-case-stobjp test-case-stobj)
                (natp len)
                (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                )
           (alistp (mv-nth 2 (initial-probable-facts-simple len test-case-stobj))))
  :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-2-of-initial-probable-facts-simple
   (implies (and (<= len bound)
                 ;(test-case-stobjp test-case-stobj)
                 (natp len)
                 (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                 )
            (all-< (strip-cars (mv-nth 2 (initial-probable-facts-simple len test-case-stobj)))
                   bound))
   :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-2-of-initial-probable-facts-simple
  (implies (and ;(test-case-stobjp test-case-stobj)
                (natp len)
                (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                )
           (nat-listp (strip-cars (mv-nth 2 (initial-probable-facts-simple len test-case-stobj)))))
  :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
 (defthm nat-listp-of-mv-nth-3-of-initial-probable-facts-simple
  (implies (and ;(test-case-stobjp test-case-stobj)
                (natp len)
                (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                )
           (nat-listp (mv-nth 3 (initial-probable-facts-simple len test-case-stobj))))
  :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

(local
 (defthm all-<-of-mv-nth-3-of-initial-probable-facts-simple
   (implies (and (<= len bound)
                 ;(test-case-stobjp test-case-stobj)
                 (natp len)
                 (= len (node-val-array-length test-case-stobj))
                  (= len (done-node-array-length test-case-stobj))
                 )
            (all-< (mv-nth 3 (initial-probable-facts-simple len test-case-stobj)) bound))
   :hints (("Goal" :in-theory (enable initial-probable-facts-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund find-val-other-than-simple (val nodenums test-case-stobj)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (all-< nodenums (node-val-array-length test-case-stobj)))
                  :stobjs test-case-stobj))
  (if (endp nodenums)
      nil ;failed to find such a val
    (let* ((nodenum (first nodenums))
           (val2 (node-val-arrayi nodenum test-case-stobj)))
      (if (equal val val2)
          ;;keep looking:
          (find-val-other-than-simple val (cdr nodenums) test-case-stobj)
        ;;we found a difference:
        t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv alist unused-nodes) where alist is the node-to-value-alist for the nodes in the set.
;; Also returns, separately, the list of nodes that are not unused.
(defund node-to-value-alist-for-set-simple (nodenums test-case-stobj alist-acc unused-nodes-acc)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (all-< nodenums (node-val-array-length test-case-stobj))
                              (equal (node-val-array-length test-case-stobj)
                                     (done-node-array-length test-case-stobj))
                              ;; (alistp alist-acc)
                              ;; (nat-listp unused-nodes-acc)
                              )
                  :stobjs test-case-stobj))
  (if (endp nodenums)
      (mv alist-acc unused-nodes-acc) ; probably no need to reverse these
    (let* ((nodenum (first nodenums))
           (val (node-val-arrayi nodenum test-case-stobj))
           (done (node-val-arrayi nodenum test-case-stobj)))
      (mv-let (alist-acc unused-nodes-acc)
        (if (not done)
            (mv alist-acc (cons nodenum unused-nodes-acc))
          (mv (acons-fast nodenum val alist-acc) unused-nodes-acc))
        (node-to-value-alist-for-set-simple (rest nodenums) test-case-stobj alist-acc unused-nodes-acc)))))

(local
  (defthm node-to-value-alist-for-set-simple-return-type
    (implies (and (nat-listp nodenums)
                  (all-< nodenums len)
                  (alistp alist-acc)
                  (all-< (strip-cars alist-acc) len)
                  (nat-listp (strip-cars alist-acc))
                  (nat-listp unused-nodes-acc)
                  (all-< unused-nodes-acc len))
             (mv-let (alist unused-nodes)
               (node-to-value-alist-for-set-simple nodenums test-case-stobj alist-acc unused-nodes-acc)
               (and (alistp alist)
                    (nat-listp (strip-cars alist))
                    (all-< (strip-cars alist) len)
                    (nat-listp unused-nodes)
                    (all-< unused-nodes len))))
    :hints (("Goal" :in-theory (enable node-to-value-alist-for-set-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;takes a set and adds zero or more sets to acc (also returns a new singleton count)
;returns (mv acc new-singleton-count change-flg)
;set should have at least two elements
;should not return singletons or empty sets
;most of the time, this won't be able to distinguish any nodes and so will return (list set) - we try to make that case fast (don't recons the whole set)...
;inline this?
(defund try-to-split-set-simple (set test-case-stobj print acc)
  (declare (xargs :guard (and (nat-listp set)
                              ;; (consp set)
                              (<= 2 (len set))
                              (print-levelp print)
                              (all-< set (node-val-array-length test-case-stobj))
                              (equal (node-val-array-length test-case-stobj)
                                     (done-node-array-length test-case-stobj))
                              (nat-list-listp acc))
                  :guard-hints (("Goal" :in-theory (enable true-listp-when-nat-list-listp)))
                  :stobjs test-case-stobj))
  (let* ((first-nodenum (first set))
         (first-val (node-val-arrayi first-nodenum test-case-stobj))
         (need-to-splitp (find-val-other-than-simple first-val (rest set) test-case-stobj)))
    (if (not need-to-splitp)
        ;;in this case we don't recons the whole set
        (mv (cons set acc) 0 nil)
      (b* ((- (and print (cw "~% (Splitting a set of ~x0 nodes.)" (len set))))
           ((mv node-to-value-alist unused-nodes)
            (node-to-value-alist-for-set-simple set test-case-stobj nil nil))
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
;;  (defthm true-listp-of-mv-nth-0-of-try-to-split-set-simple
;;    (implies (true-listp acc)
;;             (true-listp (mv-nth 0 (try-to-split-set-simple set test-case-stobj print acc))))
;;    :rule-classes :type-prescription
;;    :hints (("Goal" :in-theory (enable try-to-split-set-simple)))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-try-to-split-set-simple
   (implies (and (nat-listp set)
                 ;(consp set)
                 ;; print
                 (all-< set (node-val-array-length test-case-stobj))
                 (true-listp acc)
                 (nat-list-listp acc))
            (nat-list-listp (mv-nth 0 (try-to-split-set-simple set test-case-stobj print acc))))
   :hints (("Goal" :in-theory (enable try-to-split-set-simple)))))

;; (local
;;  (defthm all-consp-of-mv-nth-0-of-try-to-split-set-simple
;;    (implies (and (nat-listp set)
;; ;                 (consp set)
;;                  ;; print
;;                  (all-< set (node-val-array-length test-case-stobj))
;;                  (true-listp acc)
;;                  (nat-list-listp acc)
;;                  (all-consp acc))
;;             (all-consp (mv-nth 0 (try-to-split-set-simple set test-case-stobj print acc))))
;;    :hints (("Goal" :in-theory (enable try-to-split-set-simple)))))

(local
 (defthm all->=-len-of-mv-nth-0-of-try-to-split-set-simple
   (implies (and (<= 2 (len set))
                 (all->=-len acc 2))
            (all->=-len (mv-nth 0 (try-to-split-set-simple set test-case-stobj print acc)) 2))
   :hints (("Goal" :in-theory (enable try-to-split-set-simple)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-try-to-split-set-simple
   (implies (and (nat-listp set)
                 (all-< set bound)
                ;; print
                 (all-< set (node-val-array-length test-case-stobj))
                 (true-listp acc)
                 (nat-list-listp acc)
                 (all-all-< acc bound)
                 (<= (node-val-array-length test-case-stobj) bound)
                 )
            (all-all-< (mv-nth 0 (try-to-split-set-simple set test-case-stobj print acc))
                       bound))
   :hints (("Goal" :in-theory (enable try-to-split-set-simple)))))

(local
 (defthm natp-of-mv-nth-1-of-try-to-split-set-simple
   (natp (mv-nth 1 (try-to-split-set-simple set test-case-stobj print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (try-to-split-set-simple) ())))))

(local
 (defthm booleanp-of-mv-nth-2-of-try-to-split-set-simple
   (booleanp (mv-nth 2 (try-to-split-set-simple set test-case-stobj print acc)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable try-to-split-set-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to split the sets using test-case-array.
;; Returns (mv new-sets new-singleton-count changep),
;sets are moved from SETS to ACC.  as they are moved they are split if indicated by this test case.
;sets are lists of nodenums.  each set has length at least 2 (singleton sets are dropped).
(defund update-probably-equal-node-sets-simple (sets acc singleton-count-acc print test-case-stobj changep)
  (declare (xargs :guard (and (nat-list-listp sets)
                              (all->=-len sets 2)
                              (nat-list-listp acc)
                              (natp singleton-count-acc)
                              (print-levelp print)
                              (all-all-< sets (node-val-array-length test-case-stobj))
                              (equal(node-val-array-length test-case-stobj)
                                    (done-node-array-length test-case-stobj))
                              (booleanp changep))
                  :stobjs test-case-stobj
                  :guard-hints (("Goal" :in-theory (enable all-all-<)))))
  (if (endp sets)
      (mv acc singleton-count-acc changep)
    (let* ((set (first sets)))
      (mv-let (acc ;has the new sets appended onto it
                new-singleton-count change-flg-for-this-set)
        (try-to-split-set-simple set test-case-stobj print acc)
        (update-probably-equal-node-sets-simple (rest sets)
                                                acc
                                                (+ singleton-count-acc new-singleton-count)
                                                print
                                                test-case-stobj
                                                (or changep change-flg-for-this-set))))))

(local
 (defthm nat-list-listp-of-mv-nth-0-of-update-probably-equal-node-sets-simple
   (implies (and (nat-list-listp sets)
                 (nat-list-listp acc)
          ;                (all-consp acc)
;                 (all-consp sets)

                 (natp singleton-count-acc)
                 ;; print
                 (all-all-< sets (node-val-array-length test-case-stobj))
                 (booleanp changep))
            (nat-list-listp (mv-nth 0 (update-probably-equal-node-sets-simple sets  acc singleton-count-acc print test-case-stobj changep))))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets-simple all-all-<)))))

;;implied by the rule below
;; (local
;;  (defthm all-consp-of-mv-nth-0-of-update-probably-equal-node-sets-simple
;;    (implies (and (nat-list-listp sets)
;;                  (nat-list-listp acc)
;;                  (all-consp acc)
;;                  (all-consp sets)

;;                  (natp singleton-count-acc)
;;                  ;; print
;;                  (all-all-< sets (node-val-array-length test-case-stobj))
;;                  (booleanp changep))
;;             (all-consp (mv-nth 0 (update-probably-equal-node-sets-simple sets  acc singleton-count-acc print test-case-stobj changep))))
;;    :hints (("Goal" :in-theory (enable update-probably-equal-node-sets-simple all-all-<)))))

(local
 (defthm all->=-len-of-mv-nth-0-of-update-probably-equal-node-sets-simple
   (implies (and (all->=-len sets 2)
                 (all->=-len acc 2))
            (all->=-len (mv-nth 0 (update-probably-equal-node-sets-simple sets acc singleton-count-acc print test-case-stobj changep)) 2))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets-simple all-all-<)))))

(local
 (defthm all-all-<-of-mv-nth-0-of-update-probably-equal-node-sets-simple
   (implies (and (<= (node-val-array-length test-case-stobj) dag-len)
                 (nat-list-listp sets)
                 (nat-list-listp acc)
;                 (all-consp acc)
 ;                (all-consp sets)

                 (natp singleton-count-acc)
                 (ALL-ALL-< ACC DAG-LEN)
                 ;; print
                 (all-all-< sets (node-val-array-length test-case-stobj))
                 (booleanp changep))
            (all-all-< (mv-nth 0 (update-probably-equal-node-sets-simple sets  acc singleton-count-acc print test-case-stobj changep))
                       dag-len))
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets-simple all-all-<)))))

(local
 (defthm natp-of-mv-nth-1-of-update-probably-equal-node-sets-simple
   (implies (natp singleton-count-acc)
            (natp (mv-nth 1 (update-probably-equal-node-sets-simple sets  acc singleton-count-acc print test-case-stobj changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets-simple)))))

(local
 (defthm booleanp-of-mv-nth-2-of-update-probably-equal-node-sets-simple
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (update-probably-equal-node-sets-simple sets  acc singleton-count-acc print test-case-stobj changep))))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :in-theory (enable update-probably-equal-node-sets-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this function drops any pairs which are invalidated by the current test case
;this rebuilds the whole alist - hope that is okay...
;returns (mv probably-constant-node-alist changep)
;fixme might be faster to process more than 1 test case at a time
;every node in probably-constant-node-alist has been used on at least one test case
(defund update-probably-constant-alist-simple (probably-constant-node-alist ;;pairs nodenums with probable constants
                                               test-case-stobj
                                               acc ;pairs are moved from probably-constant-node-alist to this
                                               changep)
  (declare (xargs :guard (and (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (all-< (strip-cars probably-constant-node-alist)
                                     (node-val-array-length test-case-stobj))
                              (equal (node-val-array-length test-case-stobj)
                                     (done-node-array-length test-case-stobj))
                              ;; acc
                              (booleanp changep))
                  :stobjs test-case-stobj))
  (if (endp probably-constant-node-alist)
      (mv acc changep)
    (let* ((pair (first probably-constant-node-alist))
           (nodenum (car pair))
           (probable-value (cdr pair))
           (value-for-this-test-case (node-val-arrayi nodenum test-case-stobj))
           (done-for-this-test-case (done-node-arrayi nodenum test-case-stobj)))
      (if (or (not done-for-this-test-case)
              (equal probable-value value-for-this-test-case))
          ;; this test case doesn't invalidate the pair:
          (update-probably-constant-alist-simple (rest probably-constant-node-alist) test-case-stobj
                                                 (cons pair acc) changep)
        ;; the node is used and the value is different from the value in the alist, so drop the pair:
        (update-probably-constant-alist-simple (rest probably-constant-node-alist) test-case-stobj
                                               acc t)))))

(local
 (defthm alistp-of-mv-nth-0-of-update-probably-constant-alist-simple
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))

                 (all-< (strip-cars probably-constant-node-alist)
                        (node-val-array-length test-case-stobj))
                 (nat-listp (strip-cars acc))
                 (alistp acc)
                 (booleanp changep))
            (alistp (mv-nth 0 (update-probably-constant-alist-simple probably-constant-node-alist test-case-stobj acc changep))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist-simple)))))

(local
 (defthm booleanp-of-mv-nth-1-of-update-probably-constant-alist-simple
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))

                 (all-< (strip-cars probably-constant-node-alist)
                        (node-val-array-length test-case-stobj))
                 (nat-listp (strip-cars acc))
                 (alistp acc)
                 (booleanp changep))
            (booleanp (mv-nth 1 (update-probably-constant-alist-simple probably-constant-node-alist test-case-stobj acc changep))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist-simple)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-0-of-update-probably-constant-alist-simple
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))

                 (all-< (strip-cars probably-constant-node-alist)
                        (node-val-array-length test-case-stobj))
                 (nat-listp (strip-cars acc))
                 (booleanp changep))
            (nat-listp (strip-cars (mv-nth 0 (update-probably-constant-alist-simple probably-constant-node-alist test-case-stobj acc changep)))))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist-simple)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-0-of-update-probably-constant-alist-simple
   (implies (and (alistp probably-constant-node-alist)
                 (nat-listp (strip-cars probably-constant-node-alist))

                 (all-< (strip-cars probably-constant-node-alist)
                        (node-val-array-length test-case-stobj))
                 (nat-listp (strip-cars acc))
                 (ALL-< (STRIP-CARS ACC) BOUND)
                 (booleanp changep)
                 (<= (node-val-array-length test-case-stobj) bound)
                 )
            (all-< (strip-cars (mv-nth 0 (update-probably-constant-alist-simple probably-constant-node-alist test-case-stobj acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable update-probably-constant-alist-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Handles nodes that are used on this test case but have not been used on a previous test case.
;Such nodes are moved from the never-used-nodes list to the probably-constant-node-alist, where they are paired with their value on this test case.
;Returns (mv never-used-nodes probably-constant-node-alist changep) where changep remains true if it was initially true.
(defund handle-newly-used-nodes-simple (never-used-nodes ;these are moved to acc or get entries in the alist
                                        probably-constant-node-alist ;;pairs nodenums with probable constants
                                        test-case-stobj
                                        acc
                                        changep)
  (declare (xargs :guard (and (nat-listp never-used-nodes)
                              (alistp probably-constant-node-alist)
                              (all-< never-used-nodes (node-val-array-length test-case-stobj))
                              (equal (node-val-array-length test-case-stobj)
                                     (done-node-array-length test-case-stobj))
                              ;; acc
                              (booleanp changep))
                  :stobjs test-case-stobj))
  (if (endp never-used-nodes)
      (mv acc probably-constant-node-alist changep)
    (let* ((nodenum (first never-used-nodes))
           (value (node-val-arrayi nodenum test-case-stobj))
           (done (done-node-arrayi nodenum test-case-stobj)))
      (if (not done)
          ;; the node is still unused:
          (handle-newly-used-nodes-simple (rest never-used-nodes)
                                   probably-constant-node-alist
                                   test-case-stobj
                                   (cons nodenum acc)
                                   changep)
        ;;the node is used for the first time on this test case:
        (handle-newly-used-nodes-simple (rest never-used-nodes)
                                 (acons-fast nodenum value probably-constant-node-alist)
                                 test-case-stobj
                                 acc
                                 t)))))

(local
 (defthm nat-listp-of-mv-nth-0-of-handle-newly-used-nodes-simple
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp acc))
            (nat-listp (mv-nth 0 (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes-simple)))))

(local
 (defthm all-<-of-mv-nth-0-of-handle-newly-used-nodes-simple
   (implies (and (nat-listp never-used-nodes)
                 (alistp probably-constant-node-alist)
                 (all-< never-used-nodes dag-len)
                 (all-< acc dag-len)
                 (booleanp changep))
            (all-< (mv-nth 0 (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj acc changep))
                   dag-len))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes-simple)))))

(local
 (defthm alistp-of-mv-nth-1-of-handle-newly-used-nodes-simple
   (implies (alistp probably-constant-node-alist)
            (alistp (mv-nth 1 (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes-simple)))))

(local
 (defthm nat-listp-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes-simple
   (implies (and (nat-listp never-used-nodes)
                 (nat-listp (strip-cars probably-constant-node-alist)))
            (nat-listp (strip-cars (mv-nth 1 (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj acc changep)))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes-simple)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-1-of-handle-newly-used-nodes-simple
   (implies (and (all-< never-used-nodes bound)
                 (all-< (strip-cars probably-constant-node-alist) bound))
            (all-< (strip-cars (mv-nth 1 (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj acc changep)))
                   bound))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes-simple)))))

(local
 (defthm booleanp-of-mv-nth-2-of-handle-newly-used-nodes-simple
   (implies (booleanp changep)
            (booleanp (mv-nth 2 (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj acc changep))))
   :hints (("Goal" :in-theory (enable handle-newly-used-nodes-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; run test cases and use them to split probably-equal-node-sets and eliminate probable constants
;; returns (mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand), where -alist is valid iff keep-test-casesp is non-nil
;ffixme think about what to do with nodes that are unreachable (don't influence the top node, because of ifs) on a single test case, or on all test cases.  maybe i now handle that?
;now the tests come in randomized?
(defund update-probable-facts-with-test-cases-simple (steps-left ; ensures termination
                                                      test-case-count
                                                      test-case-type-alist
                                                      singleton-count
                                                      dag-array-name dag-array dag-len
                                                      probably-equal-node-sets
                                                      never-used-nodes
                                                      probably-constant-node-alist
                                                      interpreted-function-alist print
                                                      test-case-number
                                                      ;; debug-nodes
                                                      num-of-last-interesting-test-case
                                                      test-case-stobj rand
                                                      )
  (declare (xargs :guard (and (natp steps-left)
                              (or (natp test-case-count)
                                  (eq :auto test-case-count))
                              (test-case-type-alistp test-case-type-alist)
                              (natp singleton-count)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (nat-list-listp probably-equal-node-sets)
                              (all->=-len probably-equal-node-sets 2)
                              (all-all-< probably-equal-node-sets dag-len)
                              (nat-listp never-used-nodes)
                              (all-< never-used-nodes dag-len)
                              (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (all-< (strip-cars probably-constant-node-alist) dag-len)
                              (interpreted-function-alistp interpreted-function-alist)
                              (print-levelp print)
                              (natp test-case-number)
                              (or (null num-of-last-interesting-test-case)
                                  (natp num-of-last-interesting-test-case)))
                  :guard-hints (("Goal" :in-theory (disable natp strip-cars)))
                  :stobjs (test-case-stobj rand)))
  (b* (;; Check for normal termination:
       ((when (zp steps-left))
        (mv :limit-reached nil probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand))
       ;; Check for abnormal termination:
       ((when (or (and (not (eq :auto test-case-count))
                       (zp test-case-count))
                  ;;stop if we've done at least 100 test cases and nothing has happened in the last 90% of them:
                  ;;fixme could allow the user to change the 10 and the 100 here:
                  (if (and t ;abandon-testing-when-boringp ;(or t abandon-testing-when-boringp)
                           num-of-last-interesting-test-case
                           (<= 100 test-case-number)
                           (<= (* 10 num-of-last-interesting-test-case) test-case-number))
                      (prog2$ (cw "(Abandoning testing because nothing interesting is happening.)")
                              t)
                    nil)))
        (mv (erp-nil)
            t ; all tests passed
            probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand))
       ;; Keep going:
       (- ;;TODO: Only print when things change?:
         (cw "(Test ~x0 (~x1 total sets, ~x2 singletons, ~x3 constants)"
             test-case-number
             (+ singleton-count (len probably-equal-node-sets)) ;slow? could keep a count?
             singleton-count
             (len probably-constant-node-alist) ;slow?
             ))
       ((mv erp test-case rand) (make-test-case test-case-type-alist nil rand))
       ((when erp) (mv erp nil probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand))
       ;; Evaluate the test case and ensure the top node is true:
       ((mv erp test-case-stobj) (evaluate-test-case-simple dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))
       ((when erp) (mv erp nil probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand))
       ((when (not (equal t (node-val-arrayi (+ -1 dag-len) test-case-stobj))))
        (cw "WARNING: Test case failed: ~X01.~%" test-case nil)
        (mv :test-case-failed nil probably-equal-node-sets never-used-nodes probably-constant-node-alist  test-case-stobj rand))
       (changep nil) ; track whether this test case was interesting
       ;; Update the probably-equal-node-sets:
       ((mv new-sets new-singleton-count changep)
        (update-probably-equal-node-sets-simple probably-equal-node-sets nil 0 print test-case-stobj changep))
       ;; Maybe invalidate some probable constants (done before handle-newly-used-nodes-simple, which may add new probable constants):
       ((mv probably-constant-node-alist changep)
        (update-probably-constant-alist-simple probably-constant-node-alist test-case-stobj nil changep))
       ;; Handle nodes that are used for the first time on this test case (they become probable constants):
       ((mv never-used-nodes probably-constant-node-alist changep)
        (handle-newly-used-nodes-simple never-used-nodes probably-constant-node-alist test-case-stobj nil changep))
       (- (if (and (or (eq print :verbose)
                       (eq print :verbose!))
                   changep) ; todo: use this value to decide whether to keep the test case? maybe keep the first few boring ones so we have enough..
              (cw "~%interesting test case ~x0.)~%" test-case)
            (cw ")~%"))))
    (update-probable-facts-with-test-cases-simple (+ -1 steps-left)
                                                  (if (eq :auto test-case-count) :auto (+ -1 test-case-count))
                                                  test-case-type-alist
                                                  (+ singleton-count new-singleton-count)
                                                  dag-array-name dag-array dag-len
                                                  new-sets
                                                  never-used-nodes
                                                  probably-constant-node-alist
                                                  interpreted-function-alist print
                                                  (+ 1 test-case-number)
                                                  (if changep
                                                      test-case-number
                                                    num-of-last-interesting-test-case)
                                                  test-case-stobj rand)))

(local
  (defthm booleanp-of-mv-nth-1-of-update-probable-facts-with-test-cases-simple
    (booleanp (mv-nth 1 (update-probable-facts-with-test-cases-simple steps-left
                                                                      test-case-count
                                                                      test-case-type-alist
                                                                      singleton-count
                                                                      dag-array-name dag-array dag-len
                                                                      probably-equal-node-sets
                                                                      never-used-nodes
                                                                      probably-constant-node-alist
                                                                      interpreted-function-alist print
                                                                      test-case-number
                                                                      num-of-last-interesting-test-case
                                                                      test-case-stobj rand)))
    :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases-simple)))))

(local
  (defthm nat-list-listp-of-mv-nth-2-of-update-probable-facts-with-test-cases-simple
    (implies (and (natp steps-left)
                  (or (natp test-case-count)
                      (eq :auto test-case-count))
                  (test-case-type-alistp test-case-type-alist)
                  (natp singleton-count)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< 0 dag-len)
                  (nat-list-listp probably-equal-node-sets)
;                (all-consp probably-equal-node-sets)
                  (all-all-< probably-equal-node-sets dag-len)
                  (nat-listp never-used-nodes)
                  (all-< never-used-nodes dag-len)
                  (alistp probably-constant-node-alist)
                  (nat-listp (strip-cars probably-constant-node-alist))
                  (all-< (strip-cars probably-constant-node-alist) dag-len)
                  (interpreted-function-alistp interpreted-function-alist)
                  ;; print
                  (natp test-case-number)
                  (or (null num-of-last-interesting-test-case)
                      (natp num-of-last-interesting-test-case)))
             (nat-list-listp (mv-nth 2 (update-probable-facts-with-test-cases-simple steps-left
                                                                                     test-case-count
                                                                                     test-case-type-alist
                                                                                     singleton-count
                                                                                     dag-array-name dag-array dag-len
                                                                                     probably-equal-node-sets
                                                                                     never-used-nodes
                                                                                     probably-constant-node-alist
                                                                                     interpreted-function-alist print
                                                                                     test-case-number
                                                                                     num-of-last-interesting-test-case
                                                                                     test-case-stobj rand))))
    :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases-simple)))))

(local
  (defthm all->=-len-of-mv-nth-2-of-update-probable-facts-with-test-cases-simple
    (implies (and (natp steps-left)
                  (or (natp test-case-count)
                      (eq :auto test-case-count))
                  (test-case-type-alistp test-case-type-alist)
                  (natp singleton-count)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< 0 dag-len)
                  (nat-list-listp probably-equal-node-sets)
                  (all->=-len probably-equal-node-sets 2)
                  (all-all-< probably-equal-node-sets dag-len)
                  (nat-listp never-used-nodes)
                  (all-< never-used-nodes dag-len)
                  (alistp probably-constant-node-alist)
                  (nat-listp (strip-cars probably-constant-node-alist))
                  (all-< (strip-cars probably-constant-node-alist) dag-len)
                  (interpreted-function-alistp interpreted-function-alist)
                  ;; print
                  (natp test-case-number)
                  (or (null num-of-last-interesting-test-case)
                      (natp num-of-last-interesting-test-case)))
             (all->=-len (mv-nth 2 (update-probable-facts-with-test-cases-simple steps-left
                                                                                 test-case-count
                                                                                 test-case-type-alist
                                                                                 singleton-count
                                                                                 dag-array-name dag-array dag-len
                                                                                 probably-equal-node-sets
                                                                                 never-used-nodes
                                                                                 probably-constant-node-alist
                                                                                 interpreted-function-alist print
                                                                                 test-case-number
                                                                                 num-of-last-interesting-test-case
                                                                                 test-case-stobj rand))
                         2))
    :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases-simple)))))

(local
  (defthm nat-listp-of-mv-nth-3-of-update-probable-facts-with-test-cases-simple
    (implies (nat-listp never-used-nodes)
             (nat-listp (mv-nth 3 (update-probable-facts-with-test-cases-simple steps-left
                                                                                test-case-count
                                                                                test-case-type-alist
                                                                                singleton-count
                                                                                dag-array-name dag-array dag-len
                                                                                probably-equal-node-sets
                                                                                never-used-nodes
                                                                                probably-constant-node-alist
                                                                                interpreted-function-alist print
                                                                                test-case-number
                                                                                num-of-last-interesting-test-case
                                                                                test-case-stobj rand))))
    :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases-simple)))))

(local
  (defthm alistp-of-mv-nth-4-of-update-probable-facts-with-test-cases-simple
    (implies (and (natp steps-left)
                  (or (natp test-case-count)
                      (eq :auto test-case-count))
                  (test-case-type-alistp test-case-type-alist)
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
                  (natp test-case-number)
                  (or (null num-of-last-interesting-test-case)
                      (natp num-of-last-interesting-test-case)))
             (alistp (mv-nth 4 (update-probable-facts-with-test-cases-simple steps-left
                                                                             test-case-count
                                                                             test-case-type-alist
                                                                             singleton-count
                                                                             dag-array-name dag-array dag-len
                                                                             probably-equal-node-sets
                                                                             never-used-nodes
                                                                             probably-constant-node-alist
                                                                             interpreted-function-alist print
                                                                             test-case-number
                                                                             num-of-last-interesting-test-case
                                                                             test-case-stobj rand))))
    :hints (("Goal" :in-theory (enable update-probable-facts-with-test-cases-simple)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Repeatedly evaluates a test case and then use it to split possibly-equal node sets and eliminate possibly-constant nodes.
;; Returns (mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand),
;; where probably-equal-node-sets includes nodes believed to be constant and probably-constant-node-alist pairs nodes with the constants they seem to be equal to
(defund find-probable-facts-simple (dag-array-name
                                    dag-array
                                    dag-len
                                    ;; miter-depth
                                    test-case-count
                                    test-case-type-alist
                                    interpreted-function-alist
                                    print
                                    ;; keep-test-casesp
                                    ;; debug-nodes
                                    test-case-stobj
                                    rand)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              ;; (natp miter-depth)
                              (or (natp test-case-count)
                                  (eq :auto test-case-count))
                              (test-case-type-alistp test-case-type-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (print-levelp print)
                              ;; (booleanp keep-test-casesp)
                              ;; (nat-listp debug-nodes)
                              ;; (all-< debug-nodes dag-len)
                              )
                  :guard-hints (("Goal" :in-theory (disable natp)))
                  :stobjs (test-case-stobj rand)))
  (b* ((- (cw "(Evaluating test cases:~%"))
       ;; use the first test case to make initial-probably-equal-node-sets (I think this is faster than starting with one huge set and then splitting it):
       (- (cw "(Test 0 (initial)"))
       ((mv erp test-case rand) (make-test-case test-case-type-alist nil rand))
       ((when erp) (mv erp nil nil nil nil test-case-stobj rand))
       ;; Give values to all nodes:
       ((mv erp test-case-stobj) (evaluate-test-case-simple dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))
       ((when erp) (mv erp nil nil nil nil test-case-stobj rand))
       ((when (not (equal t (node-val-arrayi (+ -1 dag-len) test-case-stobj))))
        (cw "WARNING: First test case failed: ~X01.~%" test-case nil)
        (mv :test-case-failed nil nil nil nil test-case-stobj rand))
       ((mv initial-probably-equal-node-sets
            initial-singleton-count
            initial-probably-constant-node-alist ;pairs nodenums used on the first test case with their values
            initial-never-used-nodes)
        (initial-probable-facts-simple dag-len test-case-stobj))
       (- (cw ")~%"))
       ;;use additional test cases to split the sets and update the probable constant facts:
       ((mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand)
        (update-probable-facts-with-test-cases-simple 1000000
                                                      (if (eq :auto test-case-count)
                                                          :auto
                                                        (nfix (+ -1 test-case-count)))
                                                      test-case-type-alist
                                                      initial-singleton-count
                                                      dag-array-name
                                                      dag-array
                                                      dag-len
                                                      initial-probably-equal-node-sets
                                                      initial-never-used-nodes
                                                      initial-probably-constant-node-alist
                                                      interpreted-function-alist
                                                      print
                                                      ;; keep-test-casesp ;just check whether test-case-array-alist is nil?
                                                      ;; test-case-array-alist
                                                      1 ;test case number
                                                      ;; debug-nodes
                                                      nil ;;number of last interesting test case
                                                      test-case-stobj
                                                      rand))
       ((when erp) (mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand))
       (probably-equal-node-sets (remove-set-of-unused-nodes probably-equal-node-sets never-used-nodes nil)) ;TODO: could try to prove that these are really unused (could give interesting counterexamples)
       (- (cw ")~%")))
    (mv (erp-nil)
        all-passedp
        probably-equal-node-sets
        never-used-nodes
        probably-constant-node-alist
        test-case-stobj rand)))

(defthm find-probable-facts-simple-return-type
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< 0 dag-len)
                ;; (natp miter-depth)
                (or (natp test-case-count)
                    (eq :auto test-case-count))
                (test-case-type-alistp test-case-type-alist)
                (interpreted-function-alistp interpreted-function-alist)
                ;; print
                ;; (booleanp keep-test-casesp)
                ;; (nat-listp debug-nodes)
                ;; (all-< debug-nodes dag-len)
                )
           (and (booleanp (mv-nth 1 (find-probable-facts-simple dag-array-name dag-array dag-len test-case-count test-case-type-alist interpreted-function-alist print test-case-stobj rand)))
                (nat-list-listp (mv-nth 2 (find-probable-facts-simple dag-array-name dag-array dag-len test-case-count test-case-type-alist interpreted-function-alist print test-case-stobj rand)))
                (all->=-len (mv-nth 2 (find-probable-facts-simple dag-array-name dag-array dag-len test-case-count test-case-type-alist interpreted-function-alist print test-case-stobj rand)) 2)
                (nat-listp (mv-nth 3 (find-probable-facts-simple dag-array-name dag-array dag-len test-case-count test-case-type-alist interpreted-function-alist print test-case-stobj rand)))
                (alistp (mv-nth 4 (find-probable-facts-simple dag-array-name dag-array dag-len test-case-count test-case-type-alist interpreted-function-alist print test-case-stobj rand)))))
  :hints (("Goal" :in-theory (enable find-probable-facts-simple))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist).
(defund find-probable-facts-for-dag-simple (dag
                                            test-case-count
                                            test-case-type-alist ; types for the vars in the dag
                                            interpreted-function-alist
                                            print
                                            ;; keep-test-casesp
                                            ;; debug-nodes
                                            )
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) *max-1d-array-length*)
                              (or (natp test-case-count)
                                  (eq :auto test-case-count))
                              (test-case-type-alistp test-case-type-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              ;; (booleanp keep-test-casesp)
                              (print-levelp print))))
  (let* ((dag-array-name 'probable-facts-array)
         (dag-array (make-into-array dag-array-name dag))
         (dag-len (len dag)))
    (with-local-stobjs
      (test-case-stobj rand)
      (mv-let (erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist test-case-stobj rand)
        (find-probable-facts-simple dag-array-name
                                    dag-array
                                    dag-len
                                    ;; 0 ; miter-depth
                                    test-case-count
                                    test-case-type-alist
                                    interpreted-function-alist
                                    print
                                    ;; keep-test-casesp
                                    ;; nil ; debug-nodes
                                    test-case-stobj
                                    rand)
        (mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist)))))

(defthm find-probable-facts-for-dag-simple-return-type
  (implies (and (pseudo-dagp dag)
                (<= (len dag) *max-1d-array-length*)
                (or (natp test-case-count)
                    (eq :auto test-case-count))
                (test-case-type-alistp test-case-type-alist)
                (interpreted-function-alistp interpreted-function-alist)
                ;; (booleanp keep-test-casesp)
                )
           (and (booleanp (mv-nth 1 (find-probable-facts-for-dag-simple dag test-case-count test-case-type-alist interpreted-function-alist print)))
                (nat-list-listp (mv-nth 2 (find-probable-facts-for-dag-simple dag test-case-count test-case-type-alist interpreted-function-alist print)))
                (all->=-len (mv-nth 2 (find-probable-facts-for-dag-simple dag test-case-count test-case-type-alist interpreted-function-alist print)) 2)
                (nat-listp (mv-nth 3 (find-probable-facts-for-dag-simple dag test-case-count test-case-type-alist interpreted-function-alist print)))
                (alistp (mv-nth 4 (find-probable-facts-for-dag-simple dag test-case-count test-case-type-alist interpreted-function-alist print)))))
  :hints (("Goal" :in-theory (enable find-probable-facts-for-dag-simple))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns nil but prints the facts.
(defund print-probable-facts-for-dag-simple (dag test-case-count test-case-type-alist interpreted-function-alist print)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) *max-1d-array-length*)
                              (or (natp test-case-count)
                                  (eq :auto test-case-count))
                              (test-case-type-alistp test-case-type-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (print-levelp print))))
  (b* (; (interpreted-function-alist (make-interpreted-function-alist interpreted-fns wrld))
       ((mv erp all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist)
        (find-probable-facts-for-dag-simple dag test-case-count test-case-type-alist interpreted-function-alist print))
       ((when erp)
        (er hard? 'print-probable-facts-for-dag-simple "Error (~x0) getting probable facts." erp))
       (- (print-probable-info all-passedp probably-equal-node-sets never-used-nodes probably-constant-node-alist)))
    nil))
