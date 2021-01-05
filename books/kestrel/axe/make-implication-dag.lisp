; Making an implication of two DAGs
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

(include-book "dags")
(include-book "merge-dag-into-dag-quick")
(local (include-book "kestrel/lists-light/cons" :dir :system))

;dag1 is a quotep or dag-lst
;dag2 is a quotep or dag-lst
;; Returns (mv erp res) where res is a quotep or dag-lst.
;todo: consider returning the auxilary data structures.
;todo: consider letting this return a list of disjuncts
(defund make-implication-dag (dag1 dag2)
  (declare (xargs :guard (and (or (myquotep dag1)
                                  (and (pseudo-dagp dag1)
                                       (<= (len dag1) 2147483646)))
                              (or (myquotep dag2)
                                  (and (pseudo-dagp dag2)
                                       (<= (len dag2) 2147483646))))
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))))
  (if (quotep dag1)
      (if (quotep dag2)
          ;;if they are both constants, just compute the result:
          (mv (erp-nil) (enquote (implies (unquote dag1) (unquote dag2))))
        ;;only dag1 is a quotep:
        (let ((top-nodenum (top-nodenum dag2)))
          (mv (erp-nil)
              ;;fixme call a blessed dag builder function here?
              (acons-fast (+ 1 top-nodenum) `(implies ,dag1 ,top-nodenum) dag2))))
    (if (quotep dag2)
        ;;only dag2 is a quotep:
        (let ((top-nodenum (top-nodenum dag1)))
          (mv (erp-nil)
              ;;fixme call a blessed dag builder function here?
              (acons-fast (+ 1 top-nodenum) `(implies ,top-nodenum ,dag2) dag1)))
      ;;both are dag-lsts (we'll merge the smaller one into the larger one):
      (let* ((dag1-len (len dag1))
             (dag2-len (len dag2))
             (dag1-smallerp (< dag1-len dag2-len))
             (smaller-dag (if dag1-smallerp dag1 dag2))
             (larger-dag (if dag1-smallerp dag2 dag1))
             (larger-dag-len (max dag1-len dag2-len)))
        (mv-let (erp nodenum-or-quotep-for-smaller-dag extended-larger-dag)
          (merge-dag-into-dag-quick smaller-dag larger-dag)
          (if erp
              (mv erp nil)
            (let* ((dag1-item (if dag1-smallerp nodenum-or-quotep-for-smaller-dag (+ -1 larger-dag-len)))
                   (dag2-item (if dag1-smallerp (+ -1 larger-dag-len) nodenum-or-quotep-for-smaller-dag)))
              ;;fixme call a blessed dag builder function here?
              (mv (erp-nil)
                  (acons-fast (len extended-larger-dag) ;the nodenum of the IMPLIES
                              `(implies ,dag1-item ,dag2-item) ;fixme could the implies expression ever be present in the dag? ;ffixme what if the top nodes are the same? just return t!
                              extended-larger-dag)))))))))

(defthm make-implication-dag-return-type
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                ;; no error:
                (not (mv-nth 0 (make-implication-dag dag1 dag2))))
           (or (myquotep (mv-nth 1 (make-implication-dag dag1 dag2)))
               (pseudo-dagp (mv-nth 1 (make-implication-dag dag1 dag2)))))
  :hints (("Goal" :in-theory (enable make-implication-dag
                                     pseudo-dagp-rewrite
                                     bounded-dag-exprp))))

(defthm true-listp-of-car-of-mv-nth-1-of-make-implication-dag
  (implies (and (not (mv-nth 0 (make-implication-dag dag1 dag2)))
                (not (quotep (mv-nth 1 (make-implication-dag dag1 dag2))))
                )
           (true-listp (car (mv-nth 1 (make-implication-dag dag1 dag2)))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-implication-dag))))

;; it's always a cons since it's either a quotep or a pseudo-dagp
(defthm consp-of-mv-nth-1-of-make-implication-dag
  (implies (not (mv-nth 0 (make-implication-dag dag1 dag2))) ; no error
           (consp (mv-nth 1 (make-implication-dag dag1 dag2))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-implication-dag))))

(defthm pseudo-dagp-of-mv-nth-1-of-make-implication-dag
  (implies (and (or (myquotep dag1)
                    (pseudo-dagp dag1))
                (or (myquotep dag2)
                    (pseudo-dagp dag2))
                (not (mv-nth 0 (make-implication-dag dag1 dag2)))
                (not (quotep (mv-nth 1 (make-implication-dag dag1 dag2)))))
           (pseudo-dagp (mv-nth 1 (make-implication-dag dag1 dag2))))
  :hints (("Goal" :in-theory (e/d (make-implication-dag
                                   PSEUDO-DAGP-REWRITE)
                                  (myquotep
                                   )))))

(defthm true-listp-of-mv-nth-1-of-make-implication-dag
  (implies (and (or (quotep dag1)
                    (pseudo-dagp dag1))
                (or (quotep dag2)
                    (pseudo-dagp dag2))
;                (not (quotep (make-implication-dag dag1 dag2)))
                (not (mv-nth 0 (make-implication-dag dag1 dag2)))
                )
           (true-listp (mv-nth 1 (make-implication-dag dag1 dag2))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-implication-dag))))

;; (make-implication-dag *t* *nil*)
;; (make-implication-dag *t* *t*)
;; (make-implication-dag '((2 foo 1) (1 baz 0) (0 . x)) '((1 bar 0) (0 . x)))
;; (make-implication-dag '((1 bar 0) (0 . x)) '((2 foo 1) (1 baz 0) (0 . x)))

;; Returns the dag-or-quotep.  Does not return erp.
(defun make-implication-dag! (dag1 dag2)
  (declare (xargs :guard (and (or (myquotep dag1)
                                  (and (pseudo-dagp dag1)
                                       (<= (len dag1) 2147483646)))
                              (or (myquotep dag2)
                                  (and (pseudo-dagp dag2)
                                       (<= (len dag2) 2147483646))))))
  (mv-let (erp dag-or-quotep)
    (make-implication-dag dag1 dag2)
    (if erp
        (er hard? 'make-implication-dag! "Error making implication DAG.")
      dag-or-quotep)))
