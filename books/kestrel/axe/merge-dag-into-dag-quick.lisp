; Merging a DAG into another
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

(include-book "kestrel/utilities/erp" :dir :system)
(include-book "dags")
(include-book "make-dag-indices")
(include-book "merge-nodes-into-dag-array")
(include-book "consecutivep2")
(local (include-book "kestrel/alists-light/strip-cars2" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (enable symbolp-of-car-when-dag-exprp0
                          car-of-car-when-pseudo-dagp-cheap)))

;; Merges dag1 into dag2. Takes two dag-lst-or-quoteps and returns a
;; dag-lst-or-quotep. Returns (mv erp nodenum-or-quotep-for-dag1
;; extended-dag2). any valid nodenums in dag2 remain the same.  fixme make an
;; aux function that returns the 5 dag components and use in make-equality-dag
;; ?
(defund merge-dag-into-dag-quick (dag1 dag2)
  (declare (xargs :guard (and (or (myquotep dag1)
                                  (pseudo-dagp dag1))
                              (or (myquotep dag2)
                                  (pseudo-dagp dag2)))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d ( ;car-of-nth-of-len-minus1-when-pseudo-dagp
                                                  BOUNDED-DAG-PARENT-ARRAYP
                                                  wf-dagp
                                                  )
                                                 ( ;REVERSE-REMOVAL
                                                  PSEUDO-DAG-arrayP))))))
  (if (quotep dag1)
      (mv (erp-nil) dag1 dag2)
    (if (quotep dag2) ;this case is a bit odd
        (mv (erp-nil) (top-nodenum dag1) dag1)
      ;;neither is a quotep:
      (b* ((dag1-len (len dag1))
           (dag2-len (len dag2))
           ((when (or (< 2147483646 dag1-len)
                      (< 2147483646 dag2-len)))
            (mv :dag-too-big nil nil))
           (max-nodes-needed (+ dag1-len dag2-len)) ;fixme allow some slack space?
           (new-size (min 2147483646 max-nodes-needed))
           ;; make dag2 into an array:
           (dag-array (make-into-array-with-len 'dag-array dag2 new-size))
           ;; make aux structures for dag2:
           ((mv dag-parent-array dag-constant-alist dag-variable-alist)
            (make-dag-indices 'dag-array dag-array 'dag-parent-array dag2-len))
           ;;now merge in the nodes from dag1:
           (rev-dag1 (reverse dag1))
           (renaming-array (make-empty-array 'renaming-array dag1-len)) ;will rename nodes in dag1 to nodes in the merged dag
           ((mv erp renaming-array dag-array dag-len & & & ;dag-parent-array dag-constant-alist dag-variable-alist ;todo: return these things?
                )
              ;todo: the checks here on whether the array needs to be expanded will always fail:
            (merge-nodes-into-dag-array rev-dag1
                                        dag-array dag2-len dag-parent-array dag-constant-alist dag-variable-alist
                                        renaming-array))
           ((when erp) (mv erp nil nil)))
        ;;fixme return more? ;do the array-to-alist in a wrapper function?
        (mv (erp-nil)
            (aref1 'renaming-array renaming-array (top-nodenum dag1))
            (array-to-alist dag-len 'dag-array dag-array))))))

(defthm true-listp-of-mv-nth-2-of-merge-dag-into-dag-quick
  (implies (and (true-listp dag1)
                (true-listp dag2))
           (true-listp (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2))))
  :hints (("Goal" :in-theory (enable merge-dag-into-dag-quick))))

(defthm dargp-less-than-of-mv-nth-1-of-merge-dag-into-dag-quick
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2))))
           (dargp-less-than (mv-nth 1 (merge-dag-into-dag-quick dag1 dag2))
                            (len (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2)))))
  :hints (("Goal" :in-theory (enable merge-dag-into-dag-quick PSEUDO-DAGP
                                     wf-dagp ;todo
                                     ))))

(defthm natp-of-mv-nth-1-of-merge-dag-into-dag-quick
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2)))
                (not (consp (mv-nth 1 (merge-dag-into-dag-quick dag1 dag2)))))
           (natp (mv-nth 1 (merge-dag-into-dag-quick dag1 dag2))))
  :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-merge-dag-into-dag-quick
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-merge-dag-into-dag-quick))))

(defthm myquotep-of-mv-nth-1-of-merge-dag-into-dag-quick
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2))))
           (equal (myquotep (mv-nth 1 (merge-dag-into-dag-quick dag1 dag2)))
                  (consp (mv-nth 1 (merge-dag-into-dag-quick dag1 dag2)))))
  :hints (("Goal" :use dargp-less-than-of-mv-nth-1-of-merge-dag-into-dag-quick
           :in-theory (disable dargp-less-than-of-mv-nth-1-of-merge-dag-into-dag-quick))))

(defthm not-quotep-of-mv-nth-2-of-merge-dag-into-dag-quick
  (implies (pseudo-dagp dag2)
           (not (quotep (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2)))))
  :hints (("Goal" :in-theory (enable merge-dag-into-dag-quick))))

;; ;may not be true if there are duplicate nodes?
;; (defthm <=-of-len-of-mv-nth-2-of-merge-dag-into-dag-quick
;;   (implies (and (pseudo-dagp dag1)
;;                 (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2))))
;;            (<= (len dag1) (len (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2)))))
;;   :hints (("Goal" :in-theory (enable merge-dag-into-dag-quick))))

(defthm <=-of-len-of-mv-nth-2-of-merge-dag-into-dag-quick-linear
  (implies (and (pseudo-dagp dag2)
                (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2))))
           (<= (len dag2) (len (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable merge-dag-into-dag-quick))))

(defthm pseudo-dagp-aux-of-mv-nth-2-of-merge-dag-into-dag-quick
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                (not (quotep (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2))))
                (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2))))
           (pseudo-dagp-aux (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2))
                            (+ -1 (len (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2))))))
  :hints (("Goal" :in-theory (e/d (merge-dag-into-dag-quick PSEUDO-DAGP wf-dagp
                                                            ARRAY-TO-ALIST ;todo
                                                            )
                                  (myquotep len PSEUDO-DAGP)))))

(local
 (defthm integerp-when-natp
   (implies (natp x) (integerp x))))

(local
 (defthm acl2-numberp-when-natp
   (implies (natp x) (acl2-numberp x))))

(defthm not-quote-of-ARRAY-TO-ALIST-AUX
  (implies (not (equal 'quote (car acc)))
           (not (quotep (ARRAY-TO-ALIST-AUX N LEN ARRAY-NAME ARRAY ACC))))
  :hints (("Goal" :in-theory (enable ARRAY-TO-ALIST-AUX))))

(local
 (defthm natp-of-+-of--1
   (implies (integerp x)
            (equal (NATP (+ -1 x))
                   (< 0 x)))))

(defthm pseudo-dagp-of-mv-nth-2-of-merge-dag-into-dag-quick
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                (not (quotep (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2))))
                (not (mv-nth 0 (merge-dag-into-dag-quick dag1 dag2))))
           (pseudo-dagp (mv-nth 2 (merge-dag-into-dag-quick dag1 dag2))))
  :hints (("Goal" :use pseudo-dagp-aux-of-mv-nth-2-of-merge-dag-into-dag-quick
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (pseudo-dagp merge-dag-into-dag-quick)
                           ( ;myquotep
                            quotep len natp BOUNDED-DAG-EXPRP
                            pseudo-dagp-aux-of-mv-nth-2-of-merge-dag-into-dag-quick)))))

;; ;dag1 and dag2 are dag-lsts
;; ;assumes each dag by itself has no duplicate nodes (at least, we don't check for them)
;; ;returns (mv dag-array dag-len top-nodea top-nodeb) ;note that this now returns an array!
;; ;return the auxilary data structures?
;; ;fixme handle dags that are just constants (the "allows-constants" here means this supports inlined constants in dag exprs)
;; ;fixme make this call merge-dag-into-dag-quick to do most of the work
;; (defun merge-dags-allows-constants-better (dag1 dag2)
;;   (let* ((dag1-len (len dag1))
;;          (dag2-len (len dag2))
;;          (max-nodes-needed (+ dag1-len dag2-len)) ;allow some slack space?
;;          (smaller-dag (if (< dag1-len dag2-len) dag1 dag2))
;;          (larger-dag (if (< dag1-len dag2-len) dag2 dag1))
;;          (larger-dag-len (max dag1-len dag2-len)) ;just do len of larger-dag?
;;          (smaller-dag-len (min dag1-len dag2-len)) ;just do len of smaller-dag?
;;          (dag-array (make-empty-array 'dag-array max-nodes-needed))
;;          (dag-parent-array (make-empty-array 'dag-parent-array max-nodes-needed))
;;          (dag-constant-alist (empty-alist))
;;          (dag-variable-alist (empty-alist)))
;;     (mv-let (dag-array dag-parent-array dag-constant-alist dag-variable-alist) ;we know what the dag-len will be
;;             ;;first, populate the array with the nodes from the larger dag (ffixme should we just copy in the vals and then make the auxiliary data structures)?
;;             (add-nodes-to-dag-array larger-dag
;;                                     dag-array
;;                                     dag-parent-array
;;                                     dag-constant-alist
;;                                     dag-variable-alist)
;;             (let* (;;then merge in the smaller dag:
;;                    (rev-smaller-dag (reverse smaller-dag))
;;                    (renaming-array (make-empty-array 'renaming-array smaller-dag-len)) ;will rename nodes in the smaller dag to nodes in the merged dag
;;                    )
;;               (mv-let (renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                       (merge-nodes-into-dag-array rev-smaller-dag
;;                                                   dag-array larger-dag-len
;;                                                   dag-parent-array dag-constant-alist dag-variable-alist
;;                                                   renaming-array)
;;                       (declare (ignore dag-parent-array dag-constant-alist dag-variable-alist))
;;                       (mv dag-array
;;                           dag-len
;;                           (+ -1 larger-dag-len) ;top node "a" (may be for dag1 or dag2)
;;                           (aref1 'renaming-array renaming-array (top-nodenum smaller-dag))
;;                           ))))))

;; (skip- proofs (verify-guards merge-dags-allows-constants-better))
