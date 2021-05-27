; Functions to update a node-replacement-array
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

(include-book "node-replacement-array")
(include-book "dag-arrays")
(local (include-book "kestrel/lists-light/nth" :dir :system))

;;;
;;; assume-nodenum-true-in-node-replacement-array
;;;

;; Keep this in sync with unassume-nodenum-true-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes).
;; Updates NODE-REPLACEMENT-ARRAY, if possible, to reflect the fact that
;; NODENUM is non-nil.
(defund assume-nodenum-true-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0))))
           (ignore dag-len) ;avoid passing in?
           )
  (let ((expr (aref1 'dag-array dag-array nodenum)))
    (if (and (consp expr)
             (eq 'not (ffn-symb expr)) ; todo: can there be more than one nested not?
             (= 1 (len (dargs expr)))  ;optimize?
             (not (consp (darg1 expr))) ;avoid (not <constant>) but that should not happen
             )
        ;; To assume (not <noden>), we assume <noden> is nil:
        (add-node-replacement-entry-and-maybe-expand (darg1 expr) *nil* 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)
      ;; Assume nodenum is t, but only if it's a call of a known boolean:
      (if (and (consp expr) ;always true?
               (member-eq (ffn-symb expr) known-booleans))
          (add-node-replacement-entry-and-maybe-expand nodenum *t* 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)
        ;; TODO: Do something better in this case, perhaps by tracking nodenums known to be non-nil:
        ;; Or assume that (not <nodenum>) is nil, but that might require adding a node to the dag.
        (mv node-replacement-array node-replacement-array-num-valid-nodes)))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-array-num-valid-nodes)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                )
           (natp (mv-nth 1 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The array doesn't get shorter.
(defthm bound-on-alen1-of-mv-nth-0-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bound-on-mv-nth-1-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The num-valid-nodes does not decrease.
(defthm bound2-on-mv-nth-1-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-array-num-valid-nodes
               (mv-nth 1 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;;;
;;; assume-nodenum-false-in-node-replacement-array
;;;

;; Keep this in sync with unassume-nodenum-false-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes).
;; Updates NODE-REPLACEMENT-ARRAY to reflect the fact that NODENUM is nil.
(defund assume-nodenum-false-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0))))
           (ignore dag-len))
  (let ((expr (aref1 'dag-array dag-array nodenum)))
    (if (and (consp expr)
             (eq 'not (ffn-symb expr)) ; todo: can there be more than one nested not?
             (= 1 (len (dargs expr)))  ;optimize?
             (not (consp (darg1 expr))) ;avoid (not <constant>) but that should not happen
             )
        ;; To assume (not <noden>) is false, we assume <noden> is t, if it's a call of a known boolean.  Otherwise, we assume the whole not is nil (less strong).
        (let* ((noden (darg1 expr)) ;also done above
               (noden-expr (aref1 'dag-array dag-array noden)))
          (if (and (consp noden-expr)
                   (member-eq (ffn-symb noden-expr) known-booleans))
              ;; We are assuming that (not <noden>) is false where <noden> is boolean
              (add-node-replacement-entry-and-maybe-expand noden *t* 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)
            ;; TODO: Do something better in this case, perhaps by tracking nodenums known to be non-nil:
            (add-node-replacement-entry-and-maybe-expand nodenum *nil* 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)))
      ;; Assume nodenum is nil:
      (add-node-replacement-entry-and-maybe-expand nodenum *nil* 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-array-num-valid-nodes)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len))
           (natp (mv-nth 1 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The array doesn't get shorter.
(defthm bound-on-alen1-of-mv-nth-0-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bound-on-mv-nth-1-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The num-valid-nodes does not decrease.
(defthm bound2-on-mv-nth-1-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-array-num-valid-nodes
               (mv-nth 1 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;;;
;;; unassume-nodenum-true-in-node-replacement-array
;;;

;; Keep this in sync with assume-nodenum-true-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes).
;; Removes any assumptions made to reflect the fact that NODENUM is non-nil.
;; TODO: Think about whether unassuming can in rare cases destroy information.  We could save the previous entries for the node (and the argument of not) and restore them last.
;; TODO: add-node-replacement-entry-and-maybe-expand is overkill here, because we should never need to expand.
(defund unassume-nodenum-true-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0))))
           (ignore dag-len) ;avoid passing in?
           )
  (let ((expr (aref1 'dag-array dag-array nodenum)))
    (if (and (consp expr)
             (eq 'not (ffn-symb expr)) ; todo: can there be more than one nested not?
             (= 1 (len (dargs expr)))  ;optimize?
             (not (consp (darg1 expr))) ;avoid (not <constant>) but that should not happen
             )
        ;; To unassume (not <noden>), we clear the entry for <noden>:
        (add-node-replacement-entry-and-maybe-expand (darg1 expr) nil 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)
      (if (and (consp expr) ;always true?
               (member-eq (ffn-symb expr) known-booleans))
          ;; Clear the entry for nodenum itself:
          (add-node-replacement-entry-and-maybe-expand nodenum nil 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)
        ;; TODO: Do something better in this case, perhaps by tracking nodenums known to be non-nil:
        ;; Or assume that (not <nodenum>) is nil, but that might require adding a node to the dag.
        (mv node-replacement-array node-replacement-array-num-valid-nodes)))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-array-num-valid-nodes)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                )
           (natp (mv-nth 1 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The array doesn't get shorter.
(defthm bound-on-alen1-of-mv-nth-0-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bound-on-mv-nth-1-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The num-valid-nodes does not decrease.
(defthm bound2-on-mv-nth-1-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-array-num-valid-nodes
               (mv-nth 1 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;;;
;;; unassume-nodenum-false-in-node-replacement-array
;;;

;; Keep this in sync with assume-nodenum-false-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes).
;; Removes any assumptions made to reflect the fact that NODENUM is nil.
;; TODO: add-node-replacement-entry-and-maybe-expand is overkill here, because we should never need to expand.
(defund unassume-nodenum-false-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0))))
           (ignore dag-len))
  (let ((expr (aref1 'dag-array dag-array nodenum)))
    (if (and (consp expr)
             (eq 'not (ffn-symb expr)) ; todo: can there be more than one nested not?
             (= 1 (len (dargs expr)))  ;optimize?
             (not (consp (darg1 expr))) ;avoid (not <constant>) but that should not happen
             )
        ;; To unassume (not <noden>) is false, we assumed <noden> is t, if it's a call of a known boolean.  Otherwise, we assumed the whole not is nil (less strong).
        (let* ((noden (darg1 expr)) ;also done above
               (noden-expr (aref1 'dag-array dag-array noden)))
          (if (and (consp noden-expr)
                   (member-eq (ffn-symb noden-expr) known-booleans))
              (add-node-replacement-entry-and-maybe-expand noden nil 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)
            ;; TODO: Do something better in this case, perhaps by tracking nodenums known to be non-nil:
            (add-node-replacement-entry-and-maybe-expand nodenum nil 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes)))
      ;; Clear the entry for nodenum:
      (add-node-replacement-entry-and-maybe-expand nodenum nil 'node-replacement-array node-replacement-array node-replacement-array-num-valid-nodes))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-array-num-valid-nodes)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len))
           (natp (mv-nth 1 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The array doesn't get shorter.
(defthm bound-on-alen1-of-mv-nth-0-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bound-on-mv-nth-1-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The num-valid-nodes does not decrease.
(defthm bound2-on-mv-nth-1-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-array-num-valid-nodes
               (mv-nth 1 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-array-num-valid-nodes known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))
