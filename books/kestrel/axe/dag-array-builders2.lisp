; More general functions to create and extend dag-arrays
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

;; This book contains functions to build dag-arrays. Unlike the functions in
;; dag-array-builders-maybe.lisp, the functions in this book do not assume that
;; the dag-array and dag-parent-array have particular names.

(include-book "wf-dagp")
(include-book "numeric-lists")
(include-book "make-dag-constant-alist")
(include-book "make-dag-variable-alist")
(include-book "dag-parent-array-with-name")
(include-book "kestrel/utilities/erp" :dir :system)

(in-theory (disable alistp))

;;;
;;; add-variable-to-dag-array-with-name
;;;

;returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
(defund add-variable-to-dag-array-with-name (var dag-array dag-len
                                                       dag-parent-array
                                                       dag-constant-alist ;;just passed through
                                                       dag-variable-alist
                                                       dag-array-name dag-parent-array-name)
  (declare (type symbol var)
           (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbolp var))
                  :split-types t))
  (let* ((nodenum-if-present (lookup-eq var dag-variable-alist)))
    (if nodenum-if-present
        (mv (erp-nil)
            nodenum-if-present
            dag-array
            dag-len
            dag-parent-array
            dag-constant-alist
            dag-variable-alist)
      (if (= dag-len 2147483646) ;error case
          (mv :dag-too-large     ;error
              dag-len            ;; meaningless but might help with proofs
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (mv (erp-nil)
            dag-len ;new nodenum
            (aset1-expandable dag-array-name dag-array dag-len var)
            (+ 1 dag-len)
            (maybe-expand-array dag-parent-array-name dag-parent-array dag-len) ;; must keep the arrays in sync (parents of the new node are nil, the default)
            dag-constant-alist
            ;;pair var with its new nodenum in the DAG :
            (acons-fast var dag-len dag-variable-alist))))))

(DEFTHM NATP-OF-MV-NTH-3-OF-ADD-VARIABLE-TO-DAG-ARRAY-WITH-NAME
  (IMPLIES (NATP DAG-LEN)
           (NATP (MV-NTH 3
                         (ADD-VARIABLE-TO-DAG-ARRAY-WITH-NAME
                          VAR DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                          DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                          DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME))))
  :RULE-CLASSES (:REWRITE :TYPE-PRESCRIPTION)
  :HINTS (("Goal" :IN-THEORY (ENABLE ADD-VARIABLE-TO-DAG-ARRAY-WITH-NAME))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-with-name-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3
                       (add-variable-to-dag-array-with-name
                        var dag-array dag-len dag-parent-array
                        dag-constant-alist dag-variable-alist
                        dag-array-name dag-parent-array-name))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-variable-to-dag-array-with-name
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (<= dag-len 2147483646)
                (natp dag-len)
                (symbolp var))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 2
                                      (add-variable-to-dag-array-with-name
                                       var dag-array dag-len dag-parent-array
                                       dag-constant-alist dag-variable-alist
                                       dag-array-name dag-parent-array-name))
                              (mv-nth 3
                                      (add-variable-to-dag-array-with-name
                                       var dag-array dag-len dag-parent-array
                                       dag-constant-alist dag-variable-alist
                                       dag-array-name dag-parent-array-name))))
  :hints
  (("Goal"
    :in-theory (e/d (add-variable-to-dag-array-with-name)
                    (index-in-bounds-after-maybe-expand-array))
    :CASES ((< (alen1 dag-array-name dag-array)
               '2147483646))
    :use (:instance index-in-bounds-after-maybe-expand-array
                    (name dag-array-name)
                    (l dag-array)
                    (index dag-len)))))

(defthm natp-of-mv-nth-1-of-add-variable-to-dag-array-with-name
  (implies (and (dag-variable-alistp dag-variable-alist)
                (natp dag-len))
           (natp (mv-nth 1 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm array1p-of-mv-nth-2-of-add-variable-to-dag-array-with-name
  (implies (and (array1p dag-array-name dag-array)
                (<= dag-len 2147483646)
                (natp dag-len))
           (array1p dag-array-name (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-with-name-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-with-name-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm <=-of-mv-nth-3-of-add-variable-to-dag-array-with-name
  (implies (and (<= dag-len 2147483646)
                (integerp dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (<= (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
               2147483646))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-variable-to-dag-array-with-name
  (implies (and (natp dag-len)
                ;(all-< (strip-cdrs dag-constant-alist) dag-len)
                ;(DAG-PARENT-ARRAYP DAG-PARENT-ARRAY-NAME DAG-PARENT-ARRAY)
                ;(bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                ;; (ARRAY1P DAG-ARRAY-NAME DAG-ARRAY)
                ;; (ALL-DARGP-LESS-THAN (DARGS EXPR)
                ;;                                 (alen1 DAG-ARRAY-NAME DAG-ARRAY))
                ;; (EQUAL (alen1 DAG-ARRAY-NAME DAG-ARRAY)
                ;;        (alen1 DAG-PARENT-ARRAY-NAME
                ;;                         DAG-PARENT-ARRAY))
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (< (mv-nth 1 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
              (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm dag-parent-arrayp-of-mv-nth-4-of-add-variable-to-dag-array-with-name
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (natp dag-len)
                (<= dag-len 2147483646))
           (dag-parent-arrayp dag-parent-array-name (mv-nth 4 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm alen1-of-mv-nth-4-of-add-variable-to-dag-array-with-name
  (implies (and (<= dag-len 2147483646)
                (natp dag-len)
                (equal (alen1 dag-parent-array-name dag-parent-array)
                       (alen1 dag-array-name dag-array)))
           (equal (alen1 dag-parent-array-name (mv-nth 4 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                  (alen1 dag-array-name (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name maybe-expand-array))))

(defthm mv-nth-5-of-add-variable-to-dag-array-with-name
  (equal (mv-nth 5 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
         dag-constant-alist)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm dag-variable-listp-of-mv-nth-6-of-add-variable-to-dag-array-with-name
  (implies (and (dag-variable-alistp dag-variable-alist)
                (symbolp var)
                (natp dag-len))
           (dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm dag-variable-alistp-of-mv-nth-6-of-add-variable-to-dag-array-with-name
  (implies (and (dag-variable-alistp dag-variable-alist)
                (natp dag-len)
                (symbolp var))
           (dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name dag-variable-alistp))))

(defthm all-<-of-strip-cdrs-of-mv-nth-6-of-add-variable-to-dag-array-with-name
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (all-< (strip-cdrs (mv-nth 6 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                  (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name bounded-dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-of-add-variable-to-dag-array-with-name
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (bounded-dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                        (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name bounded-dag-variable-alistp))))

(defthm bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-name
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 dag-array-name dag-array))
                                             dag-parent-array-name
                                             dag-parent-array
                                             dag-len)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (natp dag-len)
                (<= dag-len 2147483646)
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array))
                (equal (alen1 dag-parent-array-name dag-parent-array)
                       (alen1 dag-array-name dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 dag-array-name (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
                                        dag-parent-array-name
                                        (mv-nth 4 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                        (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :expand (BOUNDED-DAG-PARENT-ENTRIESP
                           (+ -1
                              (alen1 DAG-ARRAY-NAME
                                               (MAYBE-EXPAND-ARRAY DAG-ARRAY-NAME
                                                             DAG-ARRAY DAG-LEN)))
                           DAG-PARENT-ARRAY-NAME
                           DAG-PARENT-ARRAY (+ 1 DAG-LEN))
           :use (:instance BOUNDED-DAG-PARENT-ENTRIESP-SUFF
                           (LIMIT (+ 1
                                     (alen1 DAG-ARRAY-NAME DAG-ARRAY)))
                           (DAG-PARENT-ARRAY DAG-PARENT-ARRAY)
                           (DAG-PARENT-ARRAY-NAME DAG-PARENT-ARRAY-NAME)
                           (N
                            (+
                             -1
                             (alen1
                               DAG-ARRAY-NAME
                               (MAYBE-EXPAND-ARRAY
                                DAG-ARRAY-NAME
                                DAG-ARRAY
                                (alen1 DAG-ARRAY-NAME DAG-ARRAY))))))
           :cases ((= DAG-LEN (alen1 DAG-ARRAY-NAME DAG-ARRAY)))
           :in-theory (enable add-variable-to-dag-array-with-name DAG-PARENT-ARRAYP))))

(defthm bounded-dag-parent-arrayp-after-add-variable-to-dag-array-with-name
  (implies (and (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (equal (alen1 dag-parent-array-name dag-parent-array)
                       (alen1 dag-array-name dag-array)))
           (bounded-dag-parent-arrayp dag-parent-array-name
                               (mv-nth 4 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                               (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-name)
           :in-theory (e/d (bounded-dag-parent-arrayp) (bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-name)))))

(defthmd dag-variable-alist-correct-after-add-variable-to-dag-array-with-name
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (equal dag-variable-alist (make-dag-variable-alist dag-array-name dag-array dag-len))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 6 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                  (make-dag-variable-alist
                   dag-array-name
                   (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthmd dag-constant-alist-correct-after-add-variable-to-dag-array-with-name
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (equal dag-constant-alist (make-dag-constant-alist dag-array-name dag-array dag-len))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 5 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                  (make-dag-constant-alist
                   dag-array-name
                   (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthmd dag-constant-alist-after-add-variable-to-dag-array-with-name
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (equal dag-constant-alist (make-dag-constant-alist dag-array-name dag-array dag-len))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (make-dag-constant-alist
                   dag-array-name
                   (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                  (make-dag-constant-alist dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array-with-name))))

(defthm wf-dagp-after-add-variable-to-dag-array-with-name
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (symbolp var))
           (wf-dagp dag-array-name
                    (mv-nth 2 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    (mv-nth 3 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    dag-parent-array-name
                    (mv-nth 4 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    dag-constant-alist ; unchanged
                    (mv-nth 6 (add-variable-to-dag-array-with-name var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     dag-variable-alist-correct-after-add-variable-to-dag-array-with-name
                                     dag-constant-alist-after-add-variable-to-dag-array-with-name))))

;;;
;;; add-function-call-expr-to-dag-array-with-name
;;;

;returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;expands the array if needed
;; TODO: Split out the constant case from the no-constant case, because often we know which case we are in
(defund add-function-call-expr-to-dag-array-with-name (fn args dag-array dag-len dag-parent-array dag-constant-alist
                                                                dag-variable-alist ;fixme just passed through
                                                                dag-array-name dag-parent-array-name)
  (declare (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (symbolp fn)
                              (not (equal 'quote fn))
                              (true-listp args)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (all-dargp-less-than args dag-len))
                  :split-types t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable <-of-+-of-minus1-arith-hack)))))
  (if (no-atoms args) ;; "constant" case
      (let* ((expr (cons fn args))
             (possible-index (lookup-equal expr dag-constant-alist))) ;BOZO use hashing?
        (if possible-index
            ;; if it's already present...
            (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          ;; otherwise, we try to add it...
          (if (= dag-len 2147483646) ;error case
              (mv :dag-too-large     ;error
                  dag-len            ;; meaningless but might help with proofs
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (mv (erp-nil)
                dag-len ;new nodenum
                (aset1-expandable dag-array-name dag-array dag-len expr)
                (+ 1 dag-len)
                (maybe-expand-array dag-parent-array-name dag-parent-array dag-len) ;; must keep the arrays in sync (parents of the new node are nil, the default)
                (acons-fast expr dag-len dag-constant-alist)
                dag-variable-alist))))
    ;; It has at least one child that's a nodenum, so we can use the "parent trick".
    ;; that is, to check the node's presence, compare it to the parents of one of its children
    (let ((possible-index (find-expr-using-parents-with-name fn args dag-array dag-parent-array dag-array-name dag-parent-array-name dag-len))) ;BOZO use hashing?
      (if possible-index ;is already present
          (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        ;; otherwisem try to add it at the top
        (if (= dag-len 2147483646)     ;error case
            (mv :dag-too-large         ;error
                dag-len ;; meaningless but might help with proofs
                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (mv (erp-nil)
              dag-len ;new nodenum
              (aset1-expandable dag-array-name dag-array dag-len (cons fn args))
              (+ 1 dag-len)
              (add-to-parents-of-atoms-with-name args dag-len dag-parent-array-name (maybe-expand-array dag-parent-array-name dag-parent-array dag-len))
              dag-constant-alist
              dag-variable-alist))))))

(defthm natp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;;(true-listp args)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array))
           (natp (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm <-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name-and-0
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array))
           (not (< (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   0)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm integerp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array))
           (integerp (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm dargp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array))
           (dargp (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm not-consp-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array))
           (not (consp (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm array1p-of-mv-nth-2-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (array1p dag-array-name dag-array)
                (natp dag-len)
                (<= dag-len 2147483646))
           (array1p dag-array-name (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-dargp-less-than args dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args)
                (integerp dag-len)
                (<= dag-len 2147483646))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                              (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :cases ((< dag-len 2147483646))
           :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;; The dag length after adding the expr actually can't be zero.
(defthm posp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (natp dag-len)
                (all-dargp-less-than args dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist))
           (< 0 (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name wf-dagp))))

(defthm <-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-and-0
  (implies (natp dag-len)
           (not (< (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   0)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm integerp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name
  (implies (integerp dag-len)
           (integerp (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;; We add at most one node.
(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;; The resulting dag-len is not too big.
(defthm <=-of-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (<= dag-len 2147483646)
                (integerp dag-len))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
               2147483646))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;; The nodenum returned is less than the length returned
(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (all-dargp-less-than args (alen1 dag-array-name dag-array))
                (equal (alen1 dag-array-name dag-array)
                       (alen1 dag-parent-array-name
                                        dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (< (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
              (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;; The dag-len does not decrease.
(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-3-gen
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-3
           :in-theory (disable bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-3))))

(defthm alen1-of-mv-nth-4-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (<= dag-len 2147483646)
                (natp dag-len)
                (equal (alen1 dag-parent-array-name dag-parent-array)
                       (alen1 dag-array-name dag-array))
                (all-dargp args))
           (equal (alen1 dag-parent-array-name (mv-nth 4 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                  (alen1 dag-array-name (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name maybe-expand-array))))

;todo: but we need to know that the other slots in the parent array contain nils, since we leave them unchanged!
;drop?
(defthm dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (all-dargp-less-than args (alen1 dag-parent-array-name dag-parent-array))
                (all-dargp-less-than args dag-len)
                (natp dag-len)
                (<= dag-len 2147483646))
           (dag-parent-arrayp dag-parent-array-name
                              (mv-nth 4 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :expand (all-dag-parent-entriesp dag-len dag-parent-array-name
                                  (maybe-expand-array dag-parent-array-name
                                                dag-parent-array dag-len))
           :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array-with-name
  (implies (natp dag-len)
           (equal (dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                  (dag-constant-alistp dag-constant-alist)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm all-<-of-strip-cdrs-of-mv-nth-5-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (natp dag-len))
           (all-< (strip-cdrs (mv-nth 5 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-namew)))
                  (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name bounded-dag-constant-alistp))))

(defthm bounded-dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                )
           (bounded-dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

(defthm mv-nth-6-of-add-function-call-expr-to-dag-array-with-name
  (equal (mv-nth 6 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
         dag-variable-alist)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array-with-name
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 dag-array-name dag-array))
                                             dag-parent-array-name
                                             dag-parent-array
                                             dag-len)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (natp dag-len)
                (<= dag-len 2147483646)
                (<= dag-len (alen1 dag-parent-array-name dag-parent-array))
                (all-dargp-less-than args (alen1 dag-array-name dag-array))
                (equal (alen1 dag-parent-array-name dag-parent-array)
                       (alen1 dag-array-name dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 dag-array-name (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
                                        dag-parent-array-name
                                        (mv-nth 4 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :expand (BOUNDED-DAG-PARENT-ENTRIESP
                           (+ -1
                              (alen1 DAG-ARRAY-NAME
                                               (MAYBE-EXPAND-ARRAY DAG-ARRAY-NAME
                                                             DAG-ARRAY DAG-LEN)))
                           DAG-PARENT-ARRAY-NAME
                           DAG-PARENT-ARRAY (+ 1 DAG-LEN))
           :use (:instance BOUNDED-DAG-PARENT-ENTRIESP-SUFF
                           (LIMIT (+ 1
                                     (alen1 DAG-ARRAY-NAME DAG-ARRAY)))
                           (DAG-PARENT-ARRAY DAG-PARENT-ARRAY)
                           (DAG-PARENT-ARRAY-NAME DAG-PARENT-ARRAY-NAME)
                           (N
                            (+
                             -1
                             (alen1
                               DAG-ARRAY-NAME
                               (MAYBE-EXPAND-ARRAY
                                DAG-ARRAY-NAME
                                DAG-ARRAY
                                (alen1 DAG-ARRAY-NAME DAG-ARRAY))))))
           :cases ((= DAG-LEN (alen1 DAG-ARRAY-NAME DAG-ARRAY)))
           :in-theory (enable alen1-of-maybe-expand-array
                              add-function-call-expr-to-dag-array-with-name DAG-PARENT-ARRAYP))))

(defthm bounded-dag-parent-arrayp-after-add-function-call-expr-to-dag-array-with-name
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than args dag-len)
                (natp dag-len))
           (bounded-dag-parent-arrayp dag-parent-array-name
                               (mv-nth 4 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                               (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-name)
           :in-theory (e/d (bounded-dag-parent-arrayp wf-dagp)
                           (bounded-dag-parent-entriesp-after-add-variable-to-dag-array-with-name)))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-with-name-4
  (implies (and (natp dag-len)
                (<= (alen1 dag-array-name dag-array) 2147483646)
                (integerp (alen1 dag-array-name dag-array))
                (<= dag-len (alen1 dag-array-name dag-array)))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
               (alen1 dag-array-name
                      (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal"  :cases ((< (alen1 dag-array-name dag-array) '2147483646))
           :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;in fact, it's always a natp...
(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbolp fn)
                (not (equal 'quote fn))
                ;; (true-listp args)
                (all-dargp-less-than args (alen1 dag-array-name dag-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                       (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable dargp-less-than))))

(defthm not-<-of-alen1-of-mv-nth-2-of-add-function-call-expr-to-dag-array-with-name
  (implies (and (natp dag-len)
                (<= (alen1 dag-array-name dag-array) 2147483646))
           (not (< (alen1 dag-array-name (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                   (alen1 dag-array-name dag-array))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm not-<-of-alen1-of-mv-nth-2-of-add-function-call-expr-to-dag-array-with-name-2
  (implies (and (natp dag-len)
                (<= (alen1 dag-array-name dag-array) 2147483646)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (not (< 2147483646
                   (alen1 dag-array-name (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

;; drop?  it's just unchaged
(defthmd dag-variable-alist-correct-after-add-function-call-expr-to-dag-array-with-name
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (equal dag-variable-alist (make-dag-variable-alist dag-array-name dag-array dag-len))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 6 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                  (make-dag-variable-alist
                   dag-array-name
                   (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm dag-variable-alist-after-add-function-call-expr-to-dag-array-with-name
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (equal dag-variable-alist (make-dag-variable-alist dag-array-name dag-array dag-len))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (make-dag-variable-alist
                   dag-array-name
                   (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                  (make-dag-variable-alist dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthmd dag-constant-alist-correct-after-add-function-call-expr-to-dag-array-with-name
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (equal dag-constant-alist (make-dag-constant-alist dag-array-name dag-array dag-len))
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp dag-len)
                (not (equal 'quote fn)))
           (equal (mv-nth 5 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                  (make-dag-constant-alist
                   dag-array-name
                   (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                   (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array-with-name))))

(defthm wf-dagp-after-add-function-call-expr-to-dag-array-with-name
  (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args)
                (all-dargp-less-than args dag-len))
           (wf-dagp dag-array-name
                    (mv-nth 2 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    (mv-nth 3 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    dag-parent-array-name
                    (mv-nth 4 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    (mv-nth 5 (add-function-call-expr-to-dag-array-with-name fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    dag-variable-alist ; unchanged
                    ))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     dag-constant-alist-correct-after-add-function-call-expr-to-dag-array-with-name))))
