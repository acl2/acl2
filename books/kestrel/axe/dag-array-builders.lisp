; Functions to create and extend dag-arrays
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

;; This book contains functions to build dag-arrays by adding nodes for
;; function calls and variables.  These functions assume the dag-array name is
;; 'dag-array and the dag-parent-array name is 'dag-parent-array, but see
;; dag-array-builders2.lisp for more general functions.

;; These functions can return errors if adding to the DAG would make it too
;; large (to fit into an array).  This lets us avoid putting guards on these
;; functions that guarantee that the DAG doesn't get too big (such guards can
;; be hard to establish in the caller).

;; todo: consider putting back some printing like that done by add-function-call-expr-to-dag-array-with-memo

(include-book "wf-dagp")
(local (include-book "numeric-lists"))
;(include-book "make-dag-constant-alist")
;(include-book "make-dag-variable-alist")
;(include-book "dag-parent-array")
;(include-book "kestrel/utilities/erp" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable alistp)))

;;;
;;; add-variable-to-dag-array
;;;

;Add the symbol VAR to the dag-array.
;returns (mv erp nodenum dag-array dag-len dag-parent-array dag-variable-alist)
;TODO: Combine the erp return value with nodenum (use nil for error)?
(defund add-variable-to-dag-array (var dag-array dag-len
                                             dag-parent-array
                                             ;; dag-constant-alist ;;just passed through
                                             dag-variable-alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              (equal (alen1 'dag-array dag-array)
                                     (alen1 'dag-parent-array dag-parent-array))
                              (bounded-dag-variable-alistp dag-variable-alist dag-len)
                              (symbolp var))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (enable rational-listp-when-all-natp dag-variable-alistp))))
           (type symbol var)
           (type (integer 0 1152921504606846974) dag-len))
  (let* ((nodenum-if-present (lookup-in-dag-variable-alist var dag-variable-alist)))
    (if nodenum-if-present
        (mv (erp-nil)
            nodenum-if-present
            dag-array
            dag-len
            dag-parent-array
            dag-variable-alist)
      (if (= dag-len *max-1d-array-length*) ;error case
          (mv :dag-too-large ;error
              dag-len ;; meaningless but might help with proofs
              dag-array dag-len dag-parent-array dag-variable-alist)
        (mv (erp-nil)
            dag-len ; new nodenum
            (aset1-expandable 'dag-array dag-array dag-len var)
            (+ 1 dag-len) ; new dag-len
            (maybe-expand-array 'dag-parent-array dag-parent-array dag-len) ;; must keep the array lengths in sync (parents of the new node are nil, the default)
            ;; pairs var with its new nodenum in the DAG:
            (add-to-dag-variable-alist var dag-len dag-variable-alist))))))

(defthm natp-of-mv-nth-1-of-add-variable-to-dag-array
  (implies (and (dag-variable-alistp dag-variable-alist)
                (natp dag-len))
           (natp (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm array1p-of-mv-nth-2-of-add-variable-to-dag-array
  (implies (and (array1p 'dag-array dag-array)
                (<= dag-len *max-1d-array-length*)
                (natp dag-len))
           (array1p 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-variable-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (symbolp var))
           (pseudo-dag-arrayp 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                              (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array)
                                  (index-in-bounds-after-maybe-expand-array))
           :use (:instance INDEX-IN-BOUNDS-AFTER-MAYBE-EXPAND-ARRAY
                           (name 'dag-array)
                           (l DAG-ARRAY)
                           (index dag-len)))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm bound-on-mv-nth-3-of-add-variable-to-dag-array-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm natp-of-mv-nth-3-of-add-variable-to-dag-array
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm integerp-of-mv-nth-3-of-add-variable-to-dag-array
  (implies (natp dag-len)
           (integerp (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

;; If no error is signaled, the new size is acceptable
(defthm <=-of-mv-nth-3-of-add-variable-to-dag-array-and-max-1d-array-length
  (implies (and (<= dag-len *max-1d-array-length*)
                (integerp dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
           (<= (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
               *max-1d-array-length*))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-variable-to-dag-array
  (implies (and (natp dag-len)
                ;(DAG-PARENT-ARRAYP 'DAG-PARENT-ARRAY DAG-PARENT-ARRAY)
                ;(bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                ;; (ARRAY1P 'DAG-ARRAY DAG-ARRAY)
                ;; (BOUNDED-DARG-LISTP (DARGS EXPR)
                ;;                                 (alen1 'DAG-ARRAY DAG-ARRAY))
                ;; (EQUAL (alen1 'DAG-ARRAY DAG-ARRAY)
                ;;        (alen1 'DAG-PARENT-ARRAY
                ;;                         DAG-PARENT-ARRAY))
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
           (< (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
              (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

(defthm dag-parent-arrayp-of-mv-nth-4-of-add-variable-to-dag-array
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (natp dag-len)
                (<= dag-len *max-1d-array-length*))
           (dag-parent-arrayp 'dag-parent-array (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

;; We use the length of the dag-array, not the dag-parent-array, as the normal form.
(defthm alen1-of-mv-nth-4-of-add-variable-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (equal (alen1 'dag-parent-array (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
                  (alen1 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array maybe-expand-array))))

(defthm dag-variable-alistp-of-mv-nth-5-of-add-variable-to-dag-array
  (implies (and (dag-variable-alistp dag-variable-alist)
                (symbolp var)
                (natp dag-len))
           (dag-variable-alistp (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-variable-to-dag-array))))

;; (defthm all-<-of-strip-cdrs-of-mv-nth-5-of-add-variable-to-dag-array
;;   (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
;;                 (symbolp var)
;;                 (natp dag-len))
;;            (all-< (strip-cdrs (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
;;                   (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
;;   :hints (("Goal" :in-theory (enable add-variable-to-dag-array bounded-dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-of-mv-nth-5-of-add-variable-to-dag-array
  (implies (and (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (natp dag-len))
           (bounded-dag-variable-alistp (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                                        (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
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
           (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
                                        'dag-parent-array
                                        (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                                        (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
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
                ;;(not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
                )
           (bounded-dag-parent-arrayp 'dag-parent-array
                                      (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                                      (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-variable-to-dag-array)
           :in-theory (e/d (bounded-dag-parent-arrayp) (bounded-dag-parent-entriesp-after-add-variable-to-dag-array)))))

;; If the dag-variable-alist was correct, it is still correct.
(local
  (defthmd dag-variable-alist-after-add-variable-to-dag-array
    (implies (and ;(not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
               (equal dag-variable-alist (make-dag-variable-alist 'dag-array dag-array dag-len))
               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
               (natp dag-len)
               (not (consp var)))
             (equal (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                    (make-dag-variable-alist
                      'dag-array
                      (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                      (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))))
    :hints (("Goal" :in-theory (enable add-variable-to-dag-array)))))

;; The dag-constant-alist is not affected by adding a variable.
(local
  (defthmd dag-constant-alist-after-add-variable-to-dag-array
    (implies (and ;(not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
               ;; (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
               (natp dag-len)
               (not (consp var)))
             (equal (make-dag-constant-alist
                      'dag-array
                      (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                      (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
                    (make-dag-constant-alist 'dag-array dag-array dag-len)))
    :hints (("Goal" :in-theory (enable add-variable-to-dag-array)))))

(defthm wf-dagp-after-add-variable-to-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                ;(not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)))
                (symbolp var))
           (wf-dagp 'dag-array
                    (mv-nth 2 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                    (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                    'dag-parent-array
                    (mv-nth 4 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                    dag-constant-alist ; unchanged
                    (mv-nth 5 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     dag-constant-alist-after-add-variable-to-dag-array
                                     dag-variable-alist-after-add-variable-to-dag-array))))

(defthm dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array
  (implies (and (natp dag-len)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                            (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (dargp-less-than add-variable-to-dag-array) (natp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array-gen
  (implies (and (<= (mv-nth 3 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist)) bound)
                (natp dag-len)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (symbolp var)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-variable-to-dag-array var dag-array dag-len dag-parent-array dag-variable-alist))
                            bound))
  :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-add-variable-to-dag-array))))

;;;
;;; add-function-call-expr-to-dag-array
;;;

;; This variant doesn't pass through the dag-variable-alist.
;; Returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist).
; Expands the array if needed.
(defund add-function-call-expr-to-dag-array (fn args dag-array dag-len dag-parent-array dag-constant-alist)
  (declare (type (integer 0 1152921504606846974) dag-len)
           (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-darg-listp args dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (dag-constant-alistp dag-constant-alist)
                              (equal (alen1 'dag-array dag-array)
                                     (alen1 'dag-parent-array dag-parent-array)))
                  :split-types t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable <-of-+-of-minus1-arith-hack dargp-when-natp)))))
  (if (all-consp args) ;; A function call all of whose children are quoteps is the "constant" case.  includes calls of 0-ary functions
      (let* ((expr (cons fn args)) ;todo: avoid this cons?
             (possible-index (lookup-equal expr dag-constant-alist))) ; todo: consider using a fast alist (but this case is rare)
        (if possible-index
            ;; it's already present...
            (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist)
          ;; otherwise, we try to add it...
          (if (= dag-len *max-1d-array-length*) ;error case
              (mv :dag-too-large     ;error
                  dag-len            ;; meaningless but might help with proofs
                  dag-array dag-len dag-parent-array dag-constant-alist)
            (mv (erp-nil)
                dag-len ;the new nodenum
                (aset1-expandable 'dag-array dag-array dag-len expr)
                (+ 1 dag-len)
                ;; the new node has no parents:
                ;; todo: this redoes the same computation to decide whether to expand the array:
                (maybe-expand-array 'dag-parent-array dag-parent-array dag-len) ;; must keep the array lengths in sync (parents of the new node are nil, the default)
                (acons-fast expr dag-len dag-constant-alist)))))
    ;; EXPR has at least one child that's a nodenum, so we can use the "parent trick".
    ;; That is, to check the node's presence in the DAG, look for it the parent list of one of its children.
    (let ((possible-index (find-expr-using-parents fn args dag-array dag-parent-array dag-len))) ; TODO: use hashing / a fast-alist for this?
      (if possible-index ;is already present
          (mv (erp-nil) possible-index dag-array dag-len dag-parent-array dag-constant-alist)
        ;; otherwise, try to add it at the top
        (if (= dag-len *max-1d-array-length*) ;error case
            (mv :dag-too-large     ;error
                dag-len            ;; meaningless but might help with proofs
                dag-array dag-len dag-parent-array dag-constant-alist)
          (mv (erp-nil)
              dag-len ;the new nodenum
              (aset1-expandable 'dag-array dag-array dag-len (cons fn args))
              (+ 1 dag-len)
              (add-to-parents-of-atoms args
                                       dag-len ;the new nodenum
                                       ;; must keep the array lengths in sync:
                                       (maybe-expand-array 'dag-parent-array dag-parent-array dag-len))
              dag-constant-alist))))))

(defthm natp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                ;(symbolp fn)
                ;(not (equal 'quote fn))
                (darg-listp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (natp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm integerp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                ;(symbolp fn)
                ;(not (equal 'quote fn))
                (darg-listp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (integerp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm not-consp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (darg-listp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (not (consp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm dargp-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (dag-constant-alistp dag-constant-alist)
                (natp dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (darg-listp args)
                ;; (true-listp args)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (dargp (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array dargp-when-natp))))

(defthm array1p-of-mv-nth-2-of-add-function-call-expr-to-dag-array
  (implies (and (array1p 'dag-array dag-array)
                (natp dag-len)
                (<= dag-len *max-1d-array-length*))
           (array1p 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (bounded-darg-listp args dag-len)
                (symbolp fn)
                (not (equal 'quote fn)))
           (pseudo-dag-arrayp 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                              (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :cases ((< dag-len *max-1d-array-length*))
           :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-gen
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (<= n (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                (natp n)
                (bounded-darg-listp args dag-len)
                (symbolp fn)
                (not (equal 'quote fn)))
           (pseudo-dag-arrayp 'dag-array
                              (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                              n))
  :hints (("Goal" :use (:instance pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array)
           :in-theory (disable pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array))))

(defthm natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-type
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm integerp-of-mv-nth-3-of-add-function-call-expr-to-dag-array-type
  (implies (integerp dag-len)
           (integerp (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm natp-of-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (natp dag-len)
           (natp (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))

(defthm integerp-of-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (natp dag-len) ; todo: or say integerp here?
           (integerp (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))

(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array
  (implies (and (natp dag-len)
                (<= dag-len *max-1d-array-length*))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
               *max-1d-array-length*))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

;; ;; todo: combine with the above?
;; (defthmd <=-of-mv-nth-3-of-add-function-call-expr-to-dag-array
;;   (implies (and (<= dag-len *max-1d-array-length*)
;;                 (integerp dag-len)
;;                 ;(not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
;;                 )
;;            (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
;;                *max-1d-array-length*))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm <=-of-mv-nth-3-of-add-function-call-expr-to-dag-array-linear
  (implies (and (<= dag-len *max-1d-array-length*)
                (integerp dag-len)
                ;(not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                )
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
               *max-1d-array-length*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

;; The DAG doesn't get shorter.
(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-3
  (implies (natp dag-len)
           (<= dag-len
               (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

;; At most one node gets added.
(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-2
  (implies (natp dag-len)
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
               (+ 1 dag-len)))
  :rule-classes ((:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

;; TODO: Add a variant of this for the other dag-array-builder operations and files
(defthm bound-on-mv-nth-3-of-add-function-call-expr-to-dag-array-4
  (implies (and (natp dag-len)
                (<= dag-len *max-1d-array-length*)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len))
           (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
               (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array PSEUDO-DAG-ARRAYP))))

;; still needed?
(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
           (< (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
              (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-alt
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
           (< (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
              (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp))))

(defthm bound-on-mv-nth-3-and-mv-nth-1-of-add-function-call-expr-to-dag-array-alt-strong
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
           (<= (+ 1 (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
               (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :rule-classes ( ;:rewrite
                 (:linear :trigger-terms ((mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp))))

;; shows that the new dag is good up through the returne node, at least
;; move up, but this depends on some rules about (mv-nth 3 ..).
(defthm pseudo-dag-arrayp-of-mv-nth-2-of-add-function-call-expr-to-dag-array-other
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                (bounded-darg-listp args dag-len)
                (symbolp fn)
                (not (equal 'quote fn)))
           (pseudo-dag-arrayp 'dag-array
                              (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                              (+ 1 (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))))

;; We use the length of the dag-array, not the dag-parent-array, as the normal form.
(defthm alen1-of-mv-nth-4-of-add-function-call-expr-to-dag-array
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array))
                (darg-listp args))
           (equal (alen1 'dag-parent-array (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                  (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array maybe-expand-array))))

;todo: but we need to know that the other slots in the parent array contain nils, since we leave them unchanged!
(defthm dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (bounded-darg-listp args (alen1 'dag-parent-array dag-parent-array))
                (bounded-darg-listp args dag-len)
                (natp dag-len)
                (<= dag-len *max-1d-array-length*))
           (dag-parent-arrayp 'dag-parent-array
                              (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :expand (all-dag-parent-entriesp dag-len 'dag-parent-array
                                                   (maybe-expand-array 'dag-parent-array
                                                                       dag-parent-array dag-len))
           :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm array1p-of-mv-nth-4-of-add-function-call-expr-to-dag-array
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (bounded-darg-listp args (alen1 'dag-parent-array dag-parent-array))
                (bounded-darg-listp args dag-len)
                (natp dag-len)
                (<= dag-len *max-1d-array-length*))
           (array1p 'dag-parent-array
                    (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :use (:instance dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array)
           :in-theory (disable dag-parent-arrayp-of-mv-nth-4-of-add-function-call-expr-to-dag-array))))

(defthm dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array
  (implies (natp dag-len)
           (equal (dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                  (dag-constant-alistp dag-constant-alist)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(local
  (defthm all-<-of-strip-cdrs-of-mv-nth-5-of-add-function-call-expr-to-dag-array
    (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                  (natp dag-len))
             (all-< (strip-cdrs (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                    (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
    :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array bounded-dag-constant-alistp)))))

(defthm bounded-dag-constant-alistp-of-mv-nth-5-of-add-function-call-expr-to-dag-array
  (implies (and (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (natp dag-len))
           (bounded-dag-constant-alistp (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

(defthm bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array
  (implies (and (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array dag-array))
                                             'dag-parent-array
                                             dag-parent-array
                                             dag-len)
                (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (<= dag-len (alen1 'dag-parent-array dag-parent-array))
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (equal (alen1 'dag-parent-array dag-parent-array)
                       (alen1 'dag-array dag-array)))
           (bounded-dag-parent-entriesp (+ -1 (alen1 'dag-array (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
                                        'dag-parent-array
                                        (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                                        (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
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
                (bounded-darg-listp args dag-len)
                ;;(not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                )
           (bounded-dag-parent-arrayp 'dag-parent-array
                               (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                               (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :use (:instance bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array)
           :in-theory (e/d (bounded-dag-parent-arrayp) (bounded-dag-parent-entriesp-after-add-function-call-expr-to-dag-array)))))

;in fact, it's always a natp...
(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array
  (implies (and (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                            (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array-gen
  (implies (and (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)) bound)
                (natp dag-len)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (symbolp fn)
                (not (equal 'quote fn))
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array
                              dag-parent-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                            bound))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

;; this one uses wf-dagp
(defthm dargp-less-than-of-mv-nth-1-of-add-function-call-expr-to-dag-array-gen-alt
  (implies (and (<= (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)) bound)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (symbolp fn)
                (not (equal 'quote fn))
                (bounded-darg-listp args (alen1 'dag-array dag-array))
                (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))))
           (dargp-less-than (mv-nth 1 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                            bound))
  :hints (("Goal" :in-theory (e/d (dargp-less-than) (natp)))))

(defthm dag-variable-alist-after-add-function-call-expr-to-dag-array
  (implies (and ;;(not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                ;(not (equal 'quote fn))
                )
           (equal (make-dag-variable-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                   (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                  (make-dag-variable-alist 'dag-array dag-array dag-len)))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthmd dag-constant-alist-correct-after-add-function-call-expr-to-dag-array
  (implies (and ;;(not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                (equal dag-constant-alist (make-dag-constant-alist 'dag-array dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp dag-len)
                (not (equal 'quote fn)))
           (equal (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                  (make-dag-constant-alist
                   'dag-array
                   (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                   (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))))
  :hints (("Goal" :in-theory (enable add-function-call-expr-to-dag-array))))

(defthm wf-dagp-after-add-function-call-expr-to-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                ;; (not (mv-nth 0 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist)))
                (symbolp fn)
                (not (equal 'quote fn))
                (bounded-darg-listp args dag-len))
           (wf-dagp 'dag-array
                    (mv-nth 2 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                    (mv-nth 3 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                    'dag-parent-array
                    (mv-nth 4 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                    (mv-nth 5 (add-function-call-expr-to-dag-array fn args dag-array dag-len dag-parent-array dag-constant-alist))
                    dag-variable-alist ; unchanged
                    ))
  :hints (("Goal" :in-theory (enable wf-dagp
                                     ;dag-variable-alist-correct-after-add-function-call-expr-to-dag-array
                                     dag-constant-alist-correct-after-add-function-call-expr-to-dag-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; The dag-len returned is always 0.
;; TODO: Use this more?
(defund empty-dag-array (slack-amount)
  (declare (xargs :guard (and (posp slack-amount)
                              (<= slack-amount *max-1d-array-length*))))
  (mv (make-empty-array 'dag-array slack-amount)
      0
      (make-empty-array 'dag-parent-array slack-amount)
      nil ; empty-dag-constant-alist ; todo: name that notion
      (empty-dag-variable-alist)))

(defthm wf-dagp-after-empty-dag-array
  (implies (and (posp slack-amount)
                (<= slack-amount *max-1d-array-length*))
           (mv-let (dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (empty-dag-array slack-amount)
             (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :in-theory (enable wf-dagp empty-dag-array))))
