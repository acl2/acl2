; Functions to create and extend dag-arrays
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

;; This book contains functions to build dag-arrays by adding nodes for
;; function calls and variables.  These functions assume the dag-array name is
;; 'dag-array and the dag-parent-array name is 'dag-parent-array, but see
;; dag-array-builders2.lisp for more general functions.

;; These functions can return errors if adding to the DAG would make it too
;; large (to fit into an array).  This lets us avoid putting guards on these
;; functions that guarantee that the DAG doesn't get too big (such guards can
;; be hard to establish in the caller).

;; todo: perhaps use macros instead of the lookup-xxx functions?

(include-book "wf-dagp")
(include-book "numeric-lists")
(include-book "make-dag-constant-alist")
(include-book "make-dag-variable-alist")
(include-book "dag-parent-array")
(include-book "kestrel/utilities/erp" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(in-theory (disable alistp))

;;;
;;; add-variable-to-dag-array
;;;

;Add the symbol VAR to the dag-array.
;returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;TODO: make a version that doesn't thread through the dag-constant-alist?
;TODO: Combine the erp return value with nodenum (use nil for error)?
(defund add-variable-to-dag-array (var dag-array dag-len
                                             dag-parent-array
                                             dag-constant-alist ;;just passed through
                                             dag-variable-alist)
  (declare (type symbol var)
           (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              (equal (alen1 'dag-array dag-array)
                                     (alen1 'dag-parent-array dag-parent-array))
                              (bounded-dag-variable-alistp dag-variable-alist dag-len)
                              (symbolp var))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (enable rational-listp-when-all-natp dag-variable-alistp)))))
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
          (mv :dag-too-large ;error
              dag-len ;; meaningless but might help with proofs
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (mv (erp-nil)
            dag-len     ;new nodenum
            (aset1-expandable 'dag-array dag-array dag-len var)
            (+ 1 dag-len)
            (maybe-expand-array 'dag-parent-array dag-parent-array dag-len) ;; must keep the arrays in sync (parents of the new node are nil, the default)
            dag-constant-alist
            ;;pair var with its new nodenum in the DAG :
            (acons-fast var dag-len dag-variable-alist))))))

(defthm natp-of-mv-nth-1-of-add-variable-to-dag-array
  (implies (and (dag-variable-alistp dag-variable-alist)
                (natp dag-len))
           (natp (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm array1p-of-mv-nth-2-of-add-variable-to-dag-array
  (implies (and (array1p 'dag-array dag-array)
                (<= dag-len 2147483646)
                (natp dag-len))
           (array1p 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-variable-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (symbolp var))
           (pseudo-dag-arrayp 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                              (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array)
                                  (index-in-bounds-after-maybe-expand-array))
           :use (:instance INDEX-IN-BOUNDS-AFTER-MAYBE-EXPAND-ARRAY
                           (name 'dag-array)
                           (l DAG-ARRAY)
                           (index dag-len)))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm natp-of-mv-nth-3-of-add-variable-to-dag-array
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm integerp-of-mv-nth-3-of-add-variable-to-dag-array
  (implies (natp dag-len)
           (integerp (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

;; If no error is signaled, the new size is acceptable
(defthm <=-of-mv-nth-3-of-add-variable-to-dag-array-and-2147483646
  (implies (and (<= dag-len 2147483646)
                (integerp dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (<= (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               2147483646))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-variable-to-dag-array
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
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (< (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
              (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm dag-parent-arrayp-of-mv-nth-4-of-add-variable-to-dag-array
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (natp dag-len)
                (<= dag-len 2147483646))
           (dag-parent-arrayp 'dag-parent-array (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm alen1-of-mv-nth-4-of-add-variable-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (equal (alen1 'dag-parent-array (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array maybe-expand-array))))

(defthm mv-nth-5-of-add-variable-to-dag-array
  (equal (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         dag-constant-alist)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm dag-variable-listp-of-mv-nth-6-of-add-variable-to-dag-array
  (implies (and (dag-variable-alistp dag-variable-alist)
                (symbolp var)
                (natp dag-len))
           (dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm all-<-of-strip-cdrs-of-mv-nth-6-of-add-variable-to-dag-array
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (all-< (strip-cdrs (mv-nth 6 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array bounded-dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-of-mv-nth-6-of-add-variable-to-dag-array
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (bounded-dag-variable-alistp (mv-nth 6 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                        (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm bounded-dag-parent-entriesp-after-add-variable-to-dag-array
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array dag-array))
                                             'dag-parent-array
                                             dag-parent-array
                                             dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (natp dag-len)
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
                                        'dag-parent-array
                                        (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                        (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
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
           :in-theory (enable add-variable-to-dag-array DAG-PARENT-ARRAYP))))

(defthm bounded-dag-parent-arrayp-after-add-variable-to-dag-array
  (implies (and (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (bounded-dag-parent-arrayp 'dag-parent-array
                               (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                               (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-variable-to-dag-array)
           :in-theory (e/d (bounded-dag-parent-arrayp) (bounded-dag-parent-entriesp-after-add-variable-to-dag-array)))))

(defthmd dag-variable-alist-correct-after-add-variable-to-dag-array
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 6 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                  (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                   (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthmd dag-constant-alist-correct-after-add-variable-to-dag-array
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                  (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                   (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthmd dag-constant-alist-after-add-variable-to-dag-array
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (consp var)))
           (equal (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                   (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (make-dag-constant-alist 'dag-array dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm wf-dagp-after-add-variable-to-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (symbolp var))
           (wf-dagp 'dag-array
                    (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    'dag-parent-array
                    (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    dag-constant-alist ; unchanged
                    (mv-nth 6 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     dag-constant-alist-after-add-variable-to-dag-array
                                     dag-variable-alist-correct-after-add-variable-to-dag-array))))

(defthm dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array
  (implies (and (natp dag-len)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (dargp-less-than add-variable-to-dag-array) (natp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array-gen
  (implies (and (<= (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)) bound)
                (natp dag-len)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            bound))
  :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array))))

;;;
;;; add-function-call-expr-to-dag-array
;;;

;returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;expands the array if needed
(defund add-function-call-expr-to-dag-array (fn args dag-array dag-len dag-parent-array dag-constant-alist
                                                dag-variable-alist ;fixme just passed through?
                                                )
  (declare (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (true-listp args)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-dargp-less-than args dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (dag-constant-alistp dag-constant-alist)
                              (equal (alen1 'dag-array dag-array)
                                     (alen1 'dag-parent-array dag-parent-array)))
                  :split-types t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable <-of-+-of-minus1-arith-hack)))))
  (if (no-atoms args) ;; A function call all of whose children are quoteps is the "constant" case.  includes calls of 0-ary functions
      (let* ((expr (cons fn args)) ;todo: avoid this cons?
             (possible-index (lookup-equal expr dag-constant-alist))) ;fixme use hashing or something?
        (if possible-index
            ;; if it's already present...
            (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          ;; otherwise, we try to add it...
          (if (= dag-len 2147483646) ;error case
              (mv :dag-too-large     ;error
                  dag-len            ;; meaningless but might help with proofs
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (mv (erp-nil)
                dag-len ;the new nodenum
                (aset1-expandable 'dag-array dag-array dag-len expr)
                (+ 1 dag-len)
                ;; the new node has no parents:
                ;; todo: this redoes the same computation to decide whether to expand the array:
                (maybe-expand-array 'dag-parent-array dag-parent-array dag-len) ;; must keep the arrays in sync (parents of the new node are nil, the default)
                (acons-fast expr dag-len dag-constant-alist)
                dag-variable-alist))))
    ;; EXPR has at least one child that's a nodenum, so we can use the "parent trick".
    ;; That is, to check the node's presence, compare it to the parents of one of its children.
    (let ((possible-index (find-expr-using-parents fn args dag-array dag-parent-array dag-len))) ;BOZO use hashing?
      (if possible-index ;is already present
          (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        ;; otherwise, try to add it at the top
        (if (= dag-len 2147483646) ;error case
            (mv :dag-too-large     ;error
                dag-len            ;; meaningless but might help with proofs
                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (mv (erp-nil)
              dag-len ;the new nodenum
              (aset1-expandable 'dag-array dag-array dag-len (cons fn args))
              (+ 1 dag-len)
              (add-to-parents-of-atoms args
                                       dag-len ;the new nodenum
                                       (maybe-expand-array 'dag-parent-array dag-parent-array dag-len))
              dag-constant-alist
              dag-variable-alist))))))

(defthm natp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (natp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm integerp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (integerp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm not-consp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (not (consp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm dargp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (all-dargp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (dargp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm array1p-of-mv-nth-2-of-add-function-call-expr-to-dag-array
  (implies (and (array1p 'dag-array dag-array)
                (natp dag-len)
                (<= dag-len 2147483646))
           (array1p 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-dargp-less-than args dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args))
           (pseudo-dag-arrayp 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                              (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :cases ((< dag-len 2147483646))
           :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-gen
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (<= n (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (natp n)
                (all-dargp-less-than args dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args))
           (pseudo-dag-arrayp 'dag-array
                              (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                              n))
  :hints (("Goal" :use (:instance pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array)
           :in-theory (disable pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array))))

(defthm natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm integerp-of-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (natp dag-len)
           (integerp (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (and (natp dag-len)
                (<= dag-len 2147483646))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               2147483646))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

;; TODO: Add a variant of this for the other dag-array-builder operations and files
(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-4
  (implies (and (natp dag-len)
                (<= dag-len 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array PSEUDO-DAG-ARRAYP))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (< (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
              (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-alt
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (< (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
              (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm <=-of-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (and (<= dag-len 2147483646)
                (integerp dag-len)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               2147483646))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

;; shows that the new dag is good up through the returne node, at least
(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-other
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (all-dargp-less-than args dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args))
           (pseudo-dag-arrayp 'dag-array
                              (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                              (+ 1 (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :use ((:instance pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array)
                        bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-alt
                        (:instance PSEUDO-DAG-ARRAYP-MONOTONE
                                   (DAG-ARRAY-NAME 'dag-array)
                                   (dag-array (MV-NTH 2
                                                      (ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY
                                                       FN
                                                       ARGS DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                                                       DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST)))
                                   (m (+
                                       1
                                       (MV-NTH
                                        1
                                        (ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY FN ARGS DAG-ARRAY DAG-LEN
                                                                             DAG-PARENT-ARRAY DAG-CONSTANT-ALIST
                                                                             DAG-VARIABLE-ALIST))))
                                   (n (MV-NTH 3
                                              (ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY
                                               FN
                                               ARGS DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                                               DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST)))))
           :cases ((natp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           :in-theory (disable pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array
                               PSEUDO-DAG-ARRAYP-OF-MV-NTH-2-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY-GEN
                               bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-alt
                               BOUND-ON-MV-NTH-3-AND-MV-NTH-1-OF-ADD-FUNCTION-CALL-EXPR-TO-DAG-ARRAY
                               PSEUDO-DAG-ARRAYP-MONOTONE
                               natp))))

(defthm alen1-of-mv-nth-4-of-add-function-call-expr-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                (all-dargp args))
           (equal (alen1 'dag-parent-array (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array maybe-expand-array))))

;todo: but we need to know that the other slots in the parent array contain nils, since we leave them unchanged!
(defthm dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (all-dargp-less-than args (alen1 'dag-parent-array dag-parent-array))
                (all-dargp-less-than args dag-len)
                (natp dag-len)
                (<= dag-len 2147483646))
           (dag-parent-arrayp 'dag-parent-array
                              (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :expand (all-dag-parent-entriesp dag-len 'dag-parent-array
                                                   (maybe-expand-array 'dag-parent-array
                                                                       dag-parent-array dag-len))
           :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm array1p-of-mv-nth-4-of-add-function-call-expr-to-dag-array
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (all-dargp-less-than args (alen1 'dag-parent-array dag-parent-array))
                (all-dargp-less-than args dag-len)
                (natp dag-len)
                (<= dag-len 2147483646))
           (array1p 'dag-parent-array
                    (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :use (:instance dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array)
           :in-theory (disable dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array))))

(defthm dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array
  (implies (natp dag-len)
           (equal (dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (dag-constant-alistp dag-constant-alist)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm all-<-of-strip-cdrs-of-mv-nth-5-of-add-function-call-expr-to-dag-array
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (natp dag-len))
           (all-< (strip-cdrs (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp))))

(defthm bounded-dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (natp dag-len))
           (bounded-dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

(defthm mv-nth-6-of-add-function-call-expr-to-dag-array
  (equal (mv-nth 6 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         dag-variable-alist)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array dag-array))
                                             'dag-parent-array
                                             dag-parent-array
                                             dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
                                        'dag-parent-array
                                        (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
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
                              add-function-call-expr-to-dag-array DAG-PARENT-ARRAYP))))

(defthm bounded-dag-parent-arrayp-after-add-function-call-expr-to-dag-array
  (implies (and (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                (all-dargp-less-than args dag-len)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (bounded-dag-parent-arrayp 'dag-parent-array
                               (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                               (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array)
           :in-theory (e/d (bounded-dag-parent-arrayp) (bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array)))))

;in fact, it's always a natp...
(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                ;; (true-listp args)
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array-gen
  (implies (and (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)) bound)
                (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                ;; (true-listp args)
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            bound))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

;; this one uses wf-dagp
(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array-gen-alt
  (implies (and (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)) bound)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (symbolp fn)
                (not (equal 'quote fn))
                ;; (true-listp args)
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            bound))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

;; drop?  the dag-variable-alist is simply unchanged
(defthmd dag-variable-alist-correct-after-add-function-call-expr-to-dag-array
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (equal 'quote fn)))
           (equal (mv-nth 6 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                  (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                   (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm dag-variable-alist-after-add-function-call-expr-to-dag-array
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                ;(not (equal 'quote fn))
                )
           (equal (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                   (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                  (make-dag-variable-alist 'dag-array dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthmd dag-constant-alist-correct-after-add-function-call-expr-to-dag-array
  (implies (and (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (equal 'quote fn)))
           (equal (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                  (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                   (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm wf-dagp-after-add-function-call-expr-to-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                (symbolp fn)
                (not (equal 'quote fn))
                (true-listp args)
                (all-dargp-less-than args dag-len))
           (wf-dagp 'dag-array
                    (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    'dag-parent-array
                    (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                    dag-variable-alist ; unchanged
                    ))
  :hints (("Goal" :in-theory (enable wf-dagp dag-variable-alist-correct-after-add-function-call-expr-to-dag-array
                                     dag-constant-alist-correct-after-add-function-call-expr-to-dag-array))))
