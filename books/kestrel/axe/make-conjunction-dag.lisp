; Making a conjunction of two DAGs
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

;; DAG1 is a quotep or dag-lst.
;; DAG2 is a quotep or dag-lst
;; Returns (mv erp res) where res is a quotep or dag-lst.
;todo: consider returning the auxilary data structures.
(defund make-conjunction-dag (dag1 dag2)
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
          (mv (erp-nil) (enquote (and (unquote dag1) (unquote dag2))))
        ;;only dag1 is a quotep:
        (let ((top-nodenum (top-nodenum-of-dag dag2)))
          (mv (erp-nil)
              ;;fixme call a blessed dag builder function here?
              (acons-fast (+ 1 top-nodenum) `(if ,dag1 ,top-nodenum 'nil) dag2))))
    (if (quotep dag2)
        ;;only dag2 is a quotep:
        (let ((top-nodenum (top-nodenum-of-dag dag1)))
          (mv (erp-nil)
              ;;fixme call a blessed dag builder function here?
              (acons-fast (+ 1 top-nodenum) `(if ,top-nodenum ,dag2 'nil) dag1)))
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
                  (acons-fast (len extended-larger-dag) ;the nodenum of the IF
                              `(if ,dag1-item ,dag2-item 'nil) ;fixme could the IF expression ever be present in the dag?
                              extended-larger-dag)))))))))

(defthm true-listp-of-car-of-mv-nth-1-of-make-conjunction-dag
  (implies (and (not (mv-nth 0 (make-conjunction-dag dag1 dag2)))
                (not (quotep (mv-nth 1 (make-conjunction-dag dag1 dag2))))
                )
           (true-listp (car (mv-nth 1 (make-conjunction-dag dag1 dag2)))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-conjunction-dag))))

;; (defthm pseudo-dagp-of-make-conjunction-dag
;;   (implies (and (or (quotep dag1)
;;                     (pseudo-dagp dag1))
;;                 (or (quotep dag2)
;;                     (pseudo-dagp dag2))
;;                 (not (quotep (make-conjunction-dag dag1 dag2))))
;;            (pseudo-dagp (make-conjunction-dag dag1 dag2)))
;;   :rule-classes (:type-prescription :rewrite)
;;   :hints (("Goal" :in-theory (enable make-conjunction-dag))))

(defthm true-listp-of-mv-nth-1-of-make-conjunction-dag
  (implies (and (or (quotep dag1)
                    (pseudo-dagp dag1))
                (or (quotep dag2)
                    (pseudo-dagp dag2))
;                (not (quotep (make-conjunction-dag dag1 dag2)))
                (not (mv-nth 0 (make-conjunction-dag dag1 dag2)))
                )
           (true-listp (mv-nth 1 (make-conjunction-dag dag1 dag2))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-conjunction-dag))))

;; (make-conjunction-dag *t* *nil*)
;; (make-conjunction-dag *t* *t*)
;; (make-conjunction-dag *t* '((2 foo 1) (1 baz 0) (0 . x)))
;; (make-conjunction-dag '((2 foo 1) (1 baz 0) (0 . x)) *t*)
;; (make-conjunction-dag '((2 foo 1) (1 baz 0) (0 . x)) '((1 bar 0) (0 . x)))
;; (make-conjunction-dag '((1 bar 0) (0 . x)) '((2 foo 1) (1 baz 0) (0 . x)))

;; Returns the dag-or-quotep.  Does not return erp.
(defun make-conjunction-dag! (dag1 dag2)
  (declare (xargs :guard (and (or (myquotep dag1)
                                  (and (pseudo-dagp dag1)
                                       (<= (len dag1) 2147483646)))
                              (or (myquotep dag2)
                                  (and (pseudo-dagp dag2)
                                       (<= (len dag2) 2147483646))))))
  (mv-let (erp dag-or-quotep)
    (make-conjunction-dag dag1 dag2)
    (if erp
        (er hard? 'make-conjunction-dag! "Error making conjunction DAG.")
      dag-or-quotep)))
