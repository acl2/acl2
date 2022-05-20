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

;; NOTE: See new version in node-replacement-array3.lisp.

;; TODO: Speed up the known boolean checking (e.g., by using a property list world).

;;;
;;; assume-nodenum-true-in-node-replacement-array
;;;

;; Keep this in sync with unassume-nodenum-true-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-count).
;; Updates NODE-REPLACEMENT-ARRAY, if possible, to reflect the fact that
;; NODENUM is non-nil.
;; TODO: Can we do better if the node is an equality (taking care to avoid loops)?
(defund assume-nodenum-true-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-count)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
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
        ;; To assume (not <noden>) is true, we assume <noden> is nil:
        (add-node-replacement-entry-and-maybe-expand (darg1 expr) *nil* node-replacement-array node-replacement-count)
      ;; Assume nodenum is T, but only if it's a call of a known boolean:
      (if (and (consp expr) ;always true?
               (member-eq (ffn-symb expr) known-booleans))
          (add-node-replacement-entry-and-maybe-expand nodenum *t* node-replacement-array node-replacement-count)
        ;; TODO: Do something better in this case, perhaps by tracking nodenums known to be non-nil:
        ;; Or assume that (not <nodenum>) is nil, but that might require adding the NOT node to the dag.
        (mv node-replacement-array node-replacement-count)))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-count)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len))
           (natp (mv-nth 1 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
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
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
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
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))
           (<= (mv-nth 1 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The node-replacement-count does not decrease.
(defthm bound2-on-mv-nth-1-of-assume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-count
               (mv-nth 1 (assume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;;;
;;; assume-nodenum-false-in-node-replacement-array
;;;

;; Keep this in sync with unassume-nodenum-false-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-count).
;; Updates NODE-REPLACEMENT-ARRAY to reflect the fact that NODENUM is nil.
(defund assume-nodenum-false-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-count)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
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
              (add-node-replacement-entry-and-maybe-expand noden *t* node-replacement-array node-replacement-count)
            ;; TODO: Do something better in this case, perhaps by tracking nodenums known to be non-nil:
            (add-node-replacement-entry-and-maybe-expand nodenum *nil* node-replacement-array node-replacement-count)))
      ;; Assume nodenum is nil:
      (add-node-replacement-entry-and-maybe-expand nodenum *nil* node-replacement-array node-replacement-count))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-count)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len))
           (natp (mv-nth 1 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
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
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
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
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The node-replacement-count does not decrease.
(defthm bound2-on-mv-nth-1-of-assume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-count
               (mv-nth 1 (assume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (assume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;;;
;;; unassume-nodenum-true-in-node-replacement-array
;;;

;; Keep this in sync with assume-nodenum-true-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-count).
;; Removes any assumptions made to reflect the fact that NODENUM is non-nil.
;; TODO: Think about whether unassuming can in rare cases destroy information.  We could save the previous entries for the node (and the argument of not) and restore them last.
;; TODO: add-node-replacement-entry-and-maybe-expand is overkill here, because we should never need to expand.
(defund unassume-nodenum-true-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-count)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
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
        (add-node-replacement-entry-and-maybe-expand (darg1 expr) nil node-replacement-array node-replacement-count)
      (if (and (consp expr) ;always true?
               (member-eq (ffn-symb expr) known-booleans))
          ;; Clear the entry for nodenum itself:
          (add-node-replacement-entry-and-maybe-expand nodenum nil node-replacement-array node-replacement-count)
        (mv node-replacement-array node-replacement-count)))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-count)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                )
           (natp (mv-nth 1 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
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
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
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
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The node-replacement-count does not decrease.
(defthm bound2-on-mv-nth-1-of-unassume-nodenum-true-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-count
               (mv-nth 1 (unassume-nodenum-true-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-true-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;;;
;;; unassume-nodenum-false-in-node-replacement-array
;;;

;; Keep this in sync with assume-nodenum-false-in-node-replacement-array.
;; Returns (mv node-replacement-array node-replacement-count).
;; Removes any assumptions made to reflect the fact that NODENUM is nil.
;; TODO: add-node-replacement-entry-and-maybe-expand is overkill here, because we should never need to expand.
(defund unassume-nodenum-false-in-node-replacement-array (nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)
  (declare (xargs :guard (and (natp nodenum) ;; should be the nodenum of a function call
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-count)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (enable CAR-BECOMES-NTH-OF-0))))
           (ignore dag-len))
  (let ((expr (aref1 'dag-array dag-array nodenum)))
    (if (and (consp expr)
             (eq 'not (ffn-symb expr)) ; todo: can there be more than one nested not?
             (= 1 (len (dargs expr)))  ;optimize?
             (not (consp (darg1 expr))) ;avoid (not <constant>) but that should not happen
             )
        ;; When we unassumed (not <noden>) is false, we assumed <noden> is t, if it's a call of a known boolean.  Otherwise, we assumed the whole not is nil (less strong).
        ;; Now we undo whatever was done.
        (let* ((noden (darg1 expr)) ;also done above
               (noden-expr (aref1 'dag-array dag-array noden)))
          (if (and (consp noden-expr)
                   (member-eq (ffn-symb noden-expr) known-booleans))
              ;; Clear the entry for the argument of NODENUM:
              (add-node-replacement-entry-and-maybe-expand noden nil node-replacement-array node-replacement-count)
            ;; Clear the entry for NODENUM itself:
            (add-node-replacement-entry-and-maybe-expand nodenum nil node-replacement-array node-replacement-count)))
      ;; Clear the entry for NODENUM itself:
      (add-node-replacement-entry-and-maybe-expand nodenum nil node-replacement-array node-replacement-count))))

(defthm node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
                                            bound))
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)))))

(defthm natp-of-mv-nth-1-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (natp node-replacement-count)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len))
           (natp (mv-nth 1 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
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
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
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
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                )
           (<= (mv-nth 1 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))
               (alen1 'node-replacement-array (mv-nth 0 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))

;; The node-replacement-count does not decrease.
(defthm bound2-on-mv-nth-1-of-unassume-nodenum-false-in-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (<= node-replacement-count
               (mv-nth 1 (unassume-nodenum-false-in-node-replacement-array nodenum dag-array dag-len node-replacement-array node-replacement-count known-booleans))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (unassume-nodenum-false-in-node-replacement-array
                                   car-becomes-nth-of-0)
                                  (natp)))))
