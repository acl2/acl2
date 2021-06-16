; dag-array-builders that involve memoization
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains functions to build dag-arrays.  See also
;; dag-array-builders.lisp and dag-array-builders2.lisp. The functions in this
;; book deal with the memoization (and one of them also passes through the
;; info, and one takes print arguments).

(include-book "wf-dagp")
;(include-book "numeric-lists")
;(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "dag-parent-array")
(include-book "make-dag-constant-alist")
(include-book "make-dag-variable-alist")
(include-book "memoization")
(include-book "kestrel/utilities/erp" :dir :system)

(defund print-intervalp (print-interval)
  (declare (xargs :guard t))
  (or (not print-interval)
      (posp print-interval)))

(defthm print-intervalp-forward
  (implies (and (print-intervalp print-interval)
                print-interval)
           (posp print-interval))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable print-intervalp))))

(local (in-theory (disable alistp)))

;; TODO: Consider using hashing?

;; Either extends the dag to include a node for VAR or returns an existing node
;; that represents VAR.  Also updates the memoization to record the fact that all of the
;; TREES-EQUAL-TO-TREE are equal to the node returned for VAR.  Returns (mv erp
;; nodenum dag-array dag-len dag-parent-array dag-constant-alist
;; dag-variable-alist memoization info).
(defund add-variable-to-dag-array-with-memo (var dag-array dag-len
                                                 dag-parent-array ;;just passed through
                                                 dag-constant-alist ;;just passed through
                                                 dag-variable-alist
                                                 trees-equal-to-tree
                                                 memoization
                                                 info ;;just passed through
                                                 )
  (declare (type symbol var)
           (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (true-listp trees-equal-to-tree)
                              (trees-to-memoizep trees-equal-to-tree)
                              (maybe-memoizationp memoization)
                              (symbolp var))
                  :split-types t))
  (let* ((nodenum-if-present (lookup-eq var dag-variable-alist))
         (memoization (if (and memoization
                               trees-equal-to-tree)
                          (add-pairs-to-memoization
                           trees-equal-to-tree ;;don't include var itself??, since its a variable - or can we memoize vars?
                           (if nodenum-if-present nodenum-if-present dag-len) ;the nodenum they are all equal to
                           memoization)
                        memoization)))
    (if nodenum-if-present
        (mv (erp-nil)
            nodenum-if-present
            dag-array
            dag-len
            dag-parent-array
            dag-constant-alist
            dag-variable-alist
            memoization
            info)
      (if (= dag-len 2147483646) ;error case
          (mv :dag-too-large     ;error
              dag-len            ;; meaningless but might help with proofs
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization info)
        (mv (erp-nil)
            dag-len
            (aset1-expandable 'dag-array dag-array dag-len var)
            (+ 1 dag-len)
            (maybe-expand-array 'dag-parent-array dag-parent-array dag-len) ;fixme rethink this - must keep the arrays in sync
            dag-constant-alist
            ;;pairs var with its new nodenum in the DAG:
            (acons-fast var dag-len dag-variable-alist)
            memoization
            info)))))

(defthm natp-of-mv-nth-1-of-add-variable-to-dag-array-with-memo
  (implies (and (dag-variable-alistp dag-variable-alist)
                (natp dag-len)
;                (symbolp var)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (natp (mv-nth 1 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm array1p-of-mv-nth-2-of-add-variable-to-dag-array-with-memo
  (implies (and (array1p 'dag-array dag-array)
                (<= dag-len 2147483646)
                (natp dag-len))
           (array1p 'dag-array (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-variable-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (<= dag-len 2147483646)
                (natp dag-len)
                (symbolp var))
           (pseudo-dag-arrayp 'dag-array (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                              (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-with-memo)
                                  (index-in-bounds-after-maybe-expand-array))
           :use (:instance index-in-bounds-after-maybe-expand-array
                           (name 'dag-array)
                           (l dag-array)
                           (index dag-len)))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-with-memo-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-with-memo-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-with-memo-3-gen
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound
               (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :use (:instance bound-on-mv-nth-3-of-add-variable-to-dag-array-with-memo-3)
           :in-theory (disable bound-on-mv-nth-3-of-add-variable-to-dag-array-with-memo-3))))

(defthm <=-of-mv-nth-3-of-add-variable-to-dag-array-with-memo
  (implies (and (<= dag-len 2147483646)
                (integerp dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
           (<= (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
               2147483646))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm natp-of-mv-nth-3-of-add-variable-to-dag-array-with-memo
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-variable-to-dag-array-with-memo
  (implies (and (natp dag-len)
                ;(all-< (strip-cdrs dag-constant-alist) dag-len)
                ;(DAG-PARENT-ARRAYP 'DAG-PARENT-ARRAY DAG-PARENT-ARRAY)
                ;(bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                ;; (ARRAY1P 'DAG-ARRAY DAG-ARRAY)
                ;; (ALL-DARGP-LESS-THAN (DARGS EXPR)
                ;;                                 (alen1 'DAG-ARRAY DAG-ARRAY))
                ;; (EQUAL (alen1 'DAG-ARRAY DAG-ARRAY)
                ;;        (alen1 'DAG-PARENT-ARRAY
                ;;                         DAG-PARENT-ARRAY))
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                )
           (< (mv-nth 1 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
              (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm dag-parent-arrayp-of-mv-nth-4-of-add-variable-to-dag-array-with-memo
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (natp dag-len)
                (<= dag-len 2147483646))
           (dag-parent-arrayp 'dag-parent-array (mv-nth 4 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm alen1-of-mv-nth-4-of-add-variable-to-dag-array-with-memo
  (implies (and (array1p 'dag-array dag-array)
                (<= dag-len 2147483646)
                (natp dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (equal (alen1 'dag-parent-array (mv-nth 4 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                  (alen1 'dag-array (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo maybe-expand-array))))

(defthm mv-nth-5-of-add-variable-to-dag-array-with-memo
  (equal (mv-nth 5 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
         dag-constant-alist)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm dag-variable-listp-of-mv-nth-6-of-add-variable-to-dag-array-with-memo
  (implies (and (dag-variable-alistp dag-variable-alist)
                (symbolp var)
                (natp dag-len))
           (dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm all-<-of-strip-cdrs-of-mv-nth-6-of-add-variable-to-dag-array-with-memo
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (all-< (strip-cdrs (mv-nth 6 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                  (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo bounded-dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-of-mv-nth-6-of-add-variable-to-dag-array-with-memo
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (bounded-dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                                        (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-memo
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array dag-array))
                                             'dag-parent-array
                                             dag-parent-array
                                             dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (array1p 'dag-array dag-array)
                (natp dag-len)
                (<= dag-len 2147483646)
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
                                        'dag-parent-array
                                        (mv-nth 4 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                                        (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :expand (BOUNDED-DAG-PARENT-ENTRIESP
                           (+ -1
                              (alen1 'DAG-ARRAY
                                               (MAYBE-EXPAND-ARRAY 'DAG-ARRAY
                                                             DAG-ARRAY DAG-LEN)))
                           'DAG-PARENT-ARRAY
                           DAG-PARENT-ARRAY (+ 1 DAG-LEN))
           :use (:instance BOUNDED-DAG-PARENT-ENTRIESP-SUFF
                           (LIMIT (+ 1
                                     (alen1 'DAG-ARRAY DAG-ARRAY)))
                           (DAG-PARENT-ARRAY DAG-PARENT-ARRAY)
                           (DAG-PARENT-ARRAY-NAME 'DAG-PARENT-ARRAY)
                           (N
                            (+
                             -1
                             (alen1
                               'DAG-ARRAY
                               (MAYBE-EXPAND-ARRAY
                                'DAG-ARRAY
                                DAG-ARRAY
                                (alen1 'DAG-ARRAY DAG-ARRAY))))))
           :cases ((= DAG-LEN (alen1 'DAG-ARRAY DAG-ARRAY)))
           :in-theory (enable add-variable-to-dag-array-with-memo DAG-PARENT-ARRAYP))))

(defthm bounded-dag-parent-arrayp-after-add-variable-to-dag-array-with-memo
  (implies (and (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                ;(not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                (<= dag-len 2147483646))
           (bounded-dag-parent-arrayp 'dag-parent-array
                               (mv-nth 4 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                               (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-memo)
           :in-theory (e/d (bounded-dag-parent-arrayp alen1-of-maybe-expand-array)
                           (bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-memo)))))

(defthmd dag-variable-alist-correct-after-add-variable-to-dag-array-with-memo
  (implies (and ;(not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 6 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                  (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                   (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthmd dag-constant-alist-correct-after-add-variable-to-dag-array-with-memo
  (implies (and ;(not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 5 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                  (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                   (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthmd dag-constant-alist-after-add-variable-to-dag-array-with-memo
  (implies (and ;(not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                   (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                  (make-dag-constant-alist 'dag-array dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

(defthm wf-dagp-after-add-variable-to-dag-array-with-memo
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                ;(not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info)))
                (symbolp var))
           (wf-dagp 'dag-array
                    (mv-nth 2 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                    (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                    'dag-parent-array
                    (mv-nth 4 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                    dag-constant-alist ;; unchanged
                    (mv-nth 6 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     dag-variable-alist-correct-after-add-variable-to-dag-array-with-memo
                                     dag-constant-alist-after-add-variable-to-dag-array-with-memo))))

(defthm bounded-memoizationp-of-nth-7-of-add-variable-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (bounded-memoizationp memoization dag-len)
                (trees-to-memoizep trees-equal-to-tree)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
           (bounded-memoizationp (mv-nth 7 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                                 (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-with-memo dargp-less-than-when-natp)
                                  (dargp-less-than natp)))))

(defthm maybe-bounded-memoizationp-of-nth-7-of-add-variable-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (maybe-bounded-memoizationp memoization dag-len)
                (trees-to-memoizep trees-equal-to-tree)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
           (maybe-bounded-memoizationp (mv-nth 7 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
                                       (mv-nth 3 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-with-memo dargp-less-than-when-natp MAYBE-BOUNDED-MEMOIZATIONP)
                                  (dargp-less-than natp)))))

;gen?
(defthm memoizationp-of-nth-7-of-add-variable-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (memoizationp memoization)
                (trees-to-memoizep trees-equal-to-tree)
                (dag-variable-alistp dag-variable-alist)
                ;(all-< (strip-cdrs dag-variable-alist) dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
           (memoizationp (mv-nth 7 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-with-memo dargp-less-than-when-natp)
                                  (dargp-less-than natp)))))

(defthm mv-nth-8-of-add-variable-to-dag-array-with-memo
  (equal (mv-nth 8 (add-variable-to-dag-array-with-memo var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist trees-equal-to-tree memoization info))
         info)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-memo))))

;; Either extends the dag to include a node for FN applied to ARGS or returns
;; an existing node that represents that expr.  Also updates the memoization to
;; record the fact that all of the TREES-EQUAL-TO-TREE are equal to the node
;; returned for that expr.  Returns (mv erp nodenum dag-array dag-len
;; dag-parent-array dag-constant-alist dag-variable-alist memoization).
;; TODO: if we are not calling this as a tail call, we could separate out the memo stuff and just call add-function-call-expr-to-dag-array.
(defund add-function-call-expr-to-dag-array-with-memo (fn args dag-array dag-len
                                                          dag-parent-array
                                                          dag-constant-alist
                                                          dag-variable-alist
                                                          print-interval print ;can we avoid passing in both?
                                                          trees-equal-to-tree
                                                          memoization)
  (declare (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbolp fn)
                              (not (equal 'quote fn))
                              (true-listp args)
                              (all-dargp-less-than args dag-len)
                              (true-listp trees-equal-to-tree)
                              (trees-to-memoizep trees-equal-to-tree)
                              (maybe-memoizationp memoization)
                              (print-intervalp print-interval))
                  :split-types t))
  (if (all-consp args) ;; "constant" case  ;;todo: we could keep these separate from the other constant alist
      (let* ((expr (cons fn args))
             (possible-index (lookup-equal expr dag-constant-alist))) ;BOZO use hashing?
        (if possible-index
            ;; if it's already present... ;update the memoization?!
            (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization)
          ;; otherwise, we add it...
          (if (= dag-len 2147483646) ;error case
              (mv :dag-too-large     ;error
                  dag-len            ;; meaningless but might help with proofs
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization)
            (mv (erp-nil)
                dag-len ;new nodenum
                (aset1-expandable 'dag-array dag-array dag-len expr)
                (+ 1 dag-len)
                (maybe-expand-array 'dag-parent-array dag-parent-array dag-len)
                (acons-fast expr dag-len dag-constant-alist)
                dag-variable-alist
                (if memoization
                    (add-pairs-to-memoization trees-equal-to-tree
                                              dag-len ;the nodenum they are all equal to
                                              memoization)
                  memoization)))))
    ;; It has at least one child that's a nodenum, so we can use the "parent trick".
    ;; that is, to check if the expression is already in the DAG, look for it among the parents of one of its children
    (let ((possible-index (find-expr-using-parents fn args dag-array dag-parent-array dag-len))) ;BOZO use hashing?
      (if possible-index ;is already present
          (mv (erp-nil)
              possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
              (if memoization
                  (add-pairs-to-memoization trees-equal-to-tree
                                            possible-index ;the nodenum they are all equal to
                                            memoization)
                memoization))
        ;; Since the node isn't already present, add it at the top
        (if (= dag-len 2147483646) ;error case
            (mv :dag-too-large     ;error
                dag-len            ;; meaningless but might help with proofs
                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist memoization)
          (prog2$ (if (and print
                           print-interval
                           (eql 0 (mod dag-len print-interval)))
                      (print-array2 'dag-array dag-array dag-len) ;
                    ;; (cw "Adding node ~x0 to dag: ~x1.~%" dag-len (array-to-alist 'dag-array dag-array dag-len))
                    ;;ffixme also print for adding other kinds of nodes (else, there may be missing multiples of 1000?)
                    (and print ;new
                         (eql 0 (mod dag-len 1000))
                         (progn$ (cw " Adding node ~x0.~%" dag-len)
                                 ;;(and memoization (print-memo-stats memoization)) ;; uncomment to see some statistics about the memoization
                                 )))
                  (mv (erp-nil)
                      dag-len ;the new nodenum
                      (aset1-expandable 'dag-array dag-array dag-len (cons fn args))
                      (+ 1 dag-len)
                      (add-to-parents-of-atoms args dag-len (maybe-expand-array 'dag-parent-array dag-parent-array dag-len))
                      dag-constant-alist
                      dag-variable-alist
                      (if memoization
                          (add-pairs-to-memoization trees-equal-to-tree
                                                    dag-len ;the nodenum they are all equal to
                                                    memoization)
                        memoization))))))))

(defthm natp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (natp (mv-nth 1 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

;;this one assume wf-dagp
(defthm natp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-memo-alt
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                (true-listp args))
           (natp (mv-nth 1 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm not-consp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (not (consp (mv-nth 1 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

; need array1p-of-set1-expandable
(defthm array1p-of-mv-nth-2-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (array1p 'dag-array dag-array)
                (natp dag-len)
                (<= dag-len 2147483646))
           (array1p 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-dargp-less-than args dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args)
                (integerp dag-len)
                (<= dag-len 2147483646)
;                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                )
           (pseudo-dag-arrayp 'dag-array
                              (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                              (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :cases ((< dag-len 2147483646))
           :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (natp dag-len)
                (<= dag-len 2147483646))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
               2147483646))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm <=-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (<= dag-len 2147483646)
                (integerp dag-len)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
               2147483646))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (BOUNDED-DAG-PARENT-ARRAYP 'DAG-PARENT-ARRAY DAG-PARENT-ARRAY dag-len)
                (ARRAY1P 'DAG-ARRAY DAG-ARRAY)
                (ALL-DARGP-LESS-THAN args (alen1 'DAG-ARRAY DAG-ARRAY))
                (EQUAL (alen1 'DAG-ARRAY DAG-ARRAY)
                       (alen1 'DAG-PARENT-ARRAY
                                        DAG-PARENT-ARRAY))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                )
           (< (mv-nth 1 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
              (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (natp dag-len)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (array1p 'dag-array dag-array)
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp fn)
                (not (equal 'quote fn)) ;drop?
                (true-listp args)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                                       (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo-3-gen
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound
               (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :use (:instance bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo-3)
           :in-theory (disable bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-memo-3))))

(defthm alen1-of-mv-nth-4-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (array1p 'dag-array dag-array)
                (<= dag-len 2147483646)
                (natp dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                (all-dargp args))
           (equal (alen1 'dag-parent-array (mv-nth 4 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                  (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo maybe-expand-array))))

;todo: but we need to know that the other slots in the parent array contain nils, since we leave them unchanged!
(defthm dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (all-dargp-less-than args (alen1 'dag-parent-array dag-parent-array))
                (all-dargp-less-than args dag-len)
                (natp dag-len)
                (<= dag-len 2147483646))
           (dag-parent-arrayp 'dag-parent-array
                              (mv-nth 4 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :expand (all-dag-parent-entriesp dag-len 'dag-parent-array
                                  (maybe-expand-array 'dag-parent-array
                                                dag-parent-array dag-len))
           :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array-with-memo
  (implies (natp dag-len)
           (equal (dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                  (dag-constant-alistp dag-constant-alist)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm all-<-of-strip-cdrs-of-mv-nth-5-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (all-< (strip-cdrs (mv-nth 5 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                  (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo bounded-dag-constant-alistp))))

(defthm bounded-dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (bounded-dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                                       (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm dag-variable-alistp-of-mv-nth-6-of-add-function-call-expr-to-dag-array-with-memo
  (equal (dag-variable-alistp (mv-nth 6 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
         (dag-variable-alistp dag-variable-alist))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm mv-nth-6-of-add-function-call-expr-to-dag-array-with-memo
  (equal (mv-nth 6 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
         dag-variable-alist)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array-with-memo
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array dag-array))
                                             'dag-parent-array
                                             dag-parent-array
                                             dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (array1p 'dag-array dag-array)
                (natp dag-len)
                (<= dag-len 2147483646)
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
                                        'dag-parent-array
                                        (mv-nth 4 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :expand (BOUNDED-DAG-PARENT-ENTRIESP
                           (+ -1
                              (alen1 'DAG-ARRAY
                                               (MAYBE-EXPAND-ARRAY 'DAG-ARRAY
                                                             DAG-ARRAY DAG-LEN)))
                           'DAG-PARENT-ARRAY
                           DAG-PARENT-ARRAY (+ 1 DAG-LEN))
           :use (:instance BOUNDED-DAG-PARENT-ENTRIESP-SUFF
                           (LIMIT (+ 1
                                     (alen1 'DAG-ARRAY DAG-ARRAY)))
                           (DAG-PARENT-ARRAY DAG-PARENT-ARRAY)
                           (DAG-PARENT-ARRAY-NAME 'DAG-PARENT-ARRAY)
                           (N
                            (+
                             -1
                             (alen1
                               'DAG-ARRAY
                               (MAYBE-EXPAND-ARRAY
                                'DAG-ARRAY
                                DAG-ARRAY
                                (alen1 'DAG-ARRAY DAG-ARRAY))))))
           :cases ((= DAG-LEN (alen1 'DAG-ARRAY DAG-ARRAY)))
           :in-theory (enable alen1-of-maybe-expand-array
                              add-function-call-expr-to-dag-array-with-memo DAG-PARENT-ARRAYP))))

(defthm bounded-dag-parent-arrayp-after-add-function-call-expr-to-dag-array-with-memo
  (implies (and (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                (all-dargp-less-than args dag-len)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (<= dag-len 2147483646))
           (bounded-dag-parent-arrayp 'dag-parent-array
                               (mv-nth 4 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                               (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array-with-memo)
           :in-theory (e/d (bounded-dag-parent-arrayp alen1-of-maybe-expand-array)
                           (bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array-with-memo)))))

;drop?
(defthmd dag-variable-alist-correct-after-add-function-call-expr-to-dag-array-with-memo
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len))
           (equal (mv-nth 6 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                  (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                   (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm dag-variable-alist-after-add-function-call-expr-to-dag-array-with-memo
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len))
           (equal (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                   (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                  (make-dag-variable-alist 'dag-array dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthmd dag-constant-alist-correct-after-add-function-call-expr-to-dag-array-with-memo
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (equal 'quote fn)))
           (equal (mv-nth 5 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                  (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                   (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-memo))))

(defthm wf-dagp-after-add-function-call-expr-to-dag-array-with-memo
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args)
                (all-dargp-less-than args dag-len))
           (wf-dagp 'dag-array
                    (mv-nth 2 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                    (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                    'dag-parent-array
                    (mv-nth 4 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                    (mv-nth 5 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                    dag-variable-alist ; unchanged
                    ))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     dag-constant-alist-correct-after-add-function-call-expr-to-dag-array-with-memo))))

(defthm bounded-memoizationp-of-nth-7-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp-less-than args dag-len)
                (true-listp args)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (bounded-memoizationp memoization dag-len)
;                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (trees-to-memoizep trees-equal-to-tree))
           (bounded-memoizationp (mv-nth 7 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                                 (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (e/d (add-function-call-expr-to-dag-array-with-memo dargp-less-than-when-natp)
                                  (dargp-less-than ;natp
                                   )))))

(defthm maybe-bounded-memoizationp-of-nth-7-of-add-function-call-expr-to-dag-array-with-memo
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp-less-than args dag-len)
                (true-listp args)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (maybe-bounded-memoizationp memoization dag-len)
;                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization)))
                (trees-to-memoizep trees-equal-to-tree))
           (maybe-bounded-memoizationp (mv-nth 7 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))
                                       (mv-nth 3 (add-function-call-expr-to-dag-array-with-memo fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print-interval print trees-equal-to-tree memoization))))
  :hints (("Goal" :in-theory (e/d (add-function-call-expr-to-dag-array-with-memo dargp-less-than-when-natp maybe-bounded-memoizationp)
                                  (dargp-less-than ;natp
                                   )))))
