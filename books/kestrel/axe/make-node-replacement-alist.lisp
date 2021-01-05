; Making equalities involving nodenums
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

(include-book "node-replacement-alist")
(include-book "equality-pairs")
(include-book "merge-term-into-dag-array-basic")
;(include-book "kestrel/utilities/erp" :dir :system)
(local (include-book "kestrel/alists-light/alistp" :dir :system))

;dup
(defthmd bounded-natp-alistp-redef
  (implies (true-listp l)
           (equal (bounded-natp-alistp l n)
                  (and (alistp l)
                       (all-natp (strip-cars l))
                       (all-< (strip-cars l) n))))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(local
 (defthm pseudo-termp-of-cdar-when-equality-pairsp
   (implies (and (equality-pairsp pairs)
                 ;(consp pairs)
                 )
            (pseudo-termp (cdr (car pairs))))
   :hints (("Goal" :in-theory (enable equality-pairsp)))))

(local
 (defthm cons-of-car-when-equality-pairsp
   (implies (and (equality-pairsp pairs)
                 (consp pairs)
                 )
            (consp (car pairs)))
   :hints (("Goal" :in-theory (enable equality-pairsp)))))

(local
 (defthm pseudo-termp-of-caar-when-equality-pairsp
   (implies (and (equality-pairsp pairs)
                 ;(consp pairs)
                 )
            (pseudo-termp (car (car pairs))))
   :hints (("Goal" :in-theory (enable equality-pairsp)))))

(local
 (defthm equality-pairsp-of-cdr
   (implies (equality-pairsp pairs)
            (equality-pairsp (cdr pairs)))
   :hints (("Goal" :in-theory (enable equality-pairsp)))))

(local
 (defthm equality-pairsp-forward-to-true-listp
   (implies (equality-pairsp pairs)
            (true-listp pairs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable equality-pairsp)))))

;; Returns (mv erp node-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund make-node-replacement-alist-and-add-to-dag-array-aux (pairs
                                                              dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                              acc)
  (declare (xargs :guard (and (equality-pairsp pairs)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (alistp acc))))
  (if (endp pairs)
      (mv (erp-nil)
          acc ;could reverse..
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((pair (first pairs))
           (lhs (car pair))
           (rhs (cdr pair)))
      (b* (((mv erp lhs-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (merge-term-into-dag-array-basic lhs
                                             nil ;var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             nil ;interpreted-function-alist
                                             ))
           ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
           ((when (consp lhs-nodenum-or-quotep)) ; check for quotep -- todo: prove this can't happen
            (er hard? 'make-node-replacement-alist-and-add-to-dag-array-aux "Assumption with a quotep LHS: ~x0." `(equal ,lhs ,rhs))
            (mv :unexpectd-quote nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
           ((mv erp rhs-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (merge-term-into-dag-array-basic rhs
                                             nil ;var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             nil ;interpreted-function-alist
                                             ))
           ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
           )
        (make-node-replacement-alist-and-add-to-dag-array-aux (rest pairs)
                                                              dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                              (acons-fast lhs-nodenum-or-quotep ;will be a nodenum (checked above)
                                                                          rhs-nodenum-or-quotep
                                                                          acc))))))

(defthm make-node-replacement-alist-and-add-to-dag-array-aux-return-type
  (implies (and (equality-pairsp pairs)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (node-replacement-alistp acc dag-len))
           (mv-let (erp node-replacement-alist dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-node-replacement-alist-and-add-to-dag-array-aux pairs
                                                                   dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                                   acc)
             (implies (not erp)
                      (and (node-replacement-alistp node-replacement-alist new-dag-len)
                           (<= dag-len new-dag-len)
                           (natp new-dag-len)
                           (wf-dagp dag-array-name dag-array new-dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :in-theory (e/d (make-node-replacement-alist-and-add-to-dag-array-aux) (wf-dagp
                                      wf-dagp-expander)))))

;; Returns (mv erp node-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund make-node-replacement-alist-and-add-to-dag-array (assumptions
                                                          dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                          ;;known-boolean-fns
                                                          wrld)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              ;; (symbol-listp known-boolean-fns)
                              (plist-worldp wrld))))
  (make-node-replacement-alist-and-add-to-dag-array-aux (make-equality-pairs assumptions wrld) ;todo: optimize by not-reifying.  also, this may be computed elsewhere.
                                                        dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                        nil))

(defthm make-node-replacement-alist-and-add-to-dag-array-return-type
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                )
           (mv-let (erp node-replacement-alist dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-node-replacement-alist-and-add-to-dag-array assumptions
                                                               dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                               wrld)
             (implies (not erp)
                      (and (node-replacement-alistp node-replacement-alist new-dag-len)
                           (natp new-dag-len)
                           (integerp new-dag-len)
                           ;; (not (consp new-dag-len)) ; a bit odd. drop?
                           (<= dag-len new-dag-len)
                           (wf-dagp dag-array-name dag-array new-dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :use (:instance make-node-replacement-alist-and-add-to-dag-array-aux-return-type
                                  (pairs (make-equality-pairs assumptions wrld))
                                  (acc nil))
           :in-theory (e/d (MAKE-NODE-REPLACEMENT-ALIST-AND-ADD-TO-DAG-ARRAY) (make-node-replacement-alist-and-add-to-dag-array-aux-return-type)))))

(defthmd NATP-ALISTP-redef
  (implies (alistp alist)
           (equal (NATP-ALISTP alist)
                  (all-natp (strip-cars alist))))
  :hints (("Goal" :in-theory (enable natp-alistp))))

(defthm make-node-replacement-alist-and-add-to-dag-array-return-type-corollary
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                )
           (mv-let (erp node-replacement-alist dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-node-replacement-alist-and-add-to-dag-array assumptions
                                                               dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                               wrld)
             (declare (ignore dag-array dag-parent-array dag-constant-alist dag-variable-alist))
             (implies (not erp)
                      (and (NOT (< '2147483646 new-dag-len))
                           (all-natp (strip-cars node-replacement-alist))
                           (natp-alistp node-replacement-alist)
                           (true-listp node-replacement-alist)
                           (BOUNDED-NATP-ALISTP node-replacement-alist 2147483646)))))
  :hints (("Goal" :use (:instance make-node-replacement-alist-and-add-to-dag-array-return-type)
           :in-theory (e/d (NODE-REPLACEMENT-ALISTP
                            BOUNDED-NATP-ALISTP-REDEF
                            NATP-ALISTP-redef)
                           (make-node-replacement-alist-and-add-to-dag-array-return-type)))))

;free var makes this not work well
;; (defthm natp-of-max-key-when-node-replacement-alistp
;;   (implies (node-replacement-alistp pairs dag-len)
;;            (natp (max-key pairs 0))))
