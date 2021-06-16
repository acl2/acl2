; Making equality dags
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
(defund make-equality-dag (dag1 dag2)
  (declare (xargs :guard (and (or (quotep dag1)
                                  (and (pseudo-dagp dag1)
                                       (<= (len dag1) 2147483646)))
                              (or (quotep dag2)
                                  (and (pseudo-dagp dag2)
                                       (<= (len dag2) 2147483646))))
                  :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))))
  (if (quotep dag1)
      (if (quotep dag2)
          ;;if they are both constants, just compare the constants
          (if (equal dag1 dag2)
              (mv (erp-nil) *t*)
            (mv (erp-nil) *nil*))
        ;;only dag1 is a quotep:
        (let ((top-nodenum (top-nodenum dag2)))
          (mv (erp-nil)
              (acons-fast (+ 1 top-nodenum) `(equal ,dag1 ,top-nodenum) dag2))))
    (if (quotep dag2)
        ;;only dag2 is a quotep:
        (let ((top-nodenum (top-nodenum dag1)))
          (mv (erp-nil)
              (acons-fast (+ 1 top-nodenum) `(equal ,dag2 ,top-nodenum) dag1)))
      ;;both are dag-lsts (we'll merge the smaller one into the larger one):
      (let* ((dag-len1 (len dag1))
             (dag-len2 (len dag2))
             (smaller-dag (if (< dag-len1 dag-len2) dag1 dag2))
             (larger-dag (if (< dag-len1 dag-len2) dag2 dag1))
             (larger-dag-len (max dag-len1 dag-len2)))
        (mv-let (erp nodenum-or-quotep-for-smaller-dag extended-larger-dag)
          (merge-dag-into-dag-quick smaller-dag larger-dag)
          (if erp
              (mv erp nil)
            ;;fixme call a blessed dag builder function here?
            (mv (erp-nil)
                (acons-fast (len extended-larger-dag) ;the nodenum
                            `(equal ,nodenum-or-quotep-for-smaller-dag ,(+ -1 larger-dag-len)) ;fixme could the equality expression ever be present in the dag? ;ffixme what if the top nodes are the same? just return t!
                            extended-larger-dag))))))))

(defthm true-listp-of-car-of-mv-nth-1-of-make-equality-dag
  (implies (and (not (mv-nth 0 (make-equality-dag dag1 dag2)))
                (not (quotep (mv-nth 1 (make-equality-dag dag1 dag2))))
                )
           (true-listp (car (mv-nth 1 (make-equality-dag dag1 dag2)))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-equality-dag))))

;; (defthm pseudo-dagp-of-make-equality-dag
;;   (implies (and (or (quotep dag1)
;;                     (pseudo-dagp dag1))
;;                 (or (quotep dag2)
;;                     (pseudo-dagp dag2))
;;                 (not (quotep (make-equality-dag dag1 dag2))))
;;            (pseudo-dagp (make-equality-dag dag1 dag2)))
;;   :rule-classes (:type-prescription :rewrite)
;;   :hints (("Goal" :in-theory (enable make-equality-dag))))

(defthm true-listp-of-mv-nth-1-of-make-equality-dag
  (implies (and (or (quotep dag1)
                    (pseudo-dagp dag1))
                (or (quotep dag2)
                    (pseudo-dagp dag2))
;                (not (quotep (make-equality-dag dag1 dag2)))
                (not (mv-nth 0 (make-equality-dag dag1 dag2)))
                )
           (true-listp (mv-nth 1 (make-equality-dag dag1 dag2))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable make-equality-dag))))

;;todo: deprecate but used in many examples
(defund make-equality-dag! (dag1 dag2)
  (declare (xargs :guard (and (or (quotep dag1)
                                  (and (pseudo-dagp dag1)
                                       (<= (len dag1) 2147483646)))
                              (or (quotep dag2)
                                  (and (pseudo-dagp dag2)
                                       (<= (len dag2) 2147483646))))))
  (mv-let (erp dag)
    (make-equality-dag dag1 dag2)
    (if erp
        (prog2$ (er hard? 'make-equality-dag! "Error making equality dag")
                dag)
      dag)))

;; ;puts the smaller dag on the bottom (why?)
;; ;fixme use this more?!
;; (defun make-equality-dag2 (dag1 dag2)
;;   (declare (xargs :guard (and (or (quotep dag1)
;;                                   (alist-with-integer-keysp dag1))
;;                               (or (quotep dag2)
;;                                   (alist-with-integer-keysp dag2)))
;;                   :guard-hints (("Goal" :in-theory (enable alistp-guard-hack alist-with-integer-keysp)))))
;;   (if (quotep dag1)
;;       (if (quotep dag2)
;;           ;;if they are both constants, just compare the constants
;;           (if (equal dag1 dag2)
;;               *t*
;;             *nil*)
;;         ;;only dag1 is a quotep:
;;         (let ((top-nodenum (top-nodenum dag2)))
;;           (acons-fast (+ 1 top-nodenum) `(equal ,dag1 ,top-nodenum) dag2)))
;;     (if (quotep dag2)
;;         ;;only dag2 is a quotep:
;;         (let ((top-nodenum (top-nodenum dag1)))
;;           (acons-fast (+ 1 top-nodenum) `(equal ,dag2 ,top-nodenum) dag1))
;;       ;;both are dag-lsts (we'll merge the larger one into the smaller one):
;;       (let* ((dag-len1 (len dag1))
;;              (dag-len2 (len dag2))
;;              (smaller-dag (if (< dag-len1 dag-len2) dag1 dag2))
;;              (larger-dag (if (< dag-len1 dag-len2) dag2 dag1))
;;              (smaller-dag-len (min dag-len1 dag-len2)))
;;         (mv-let (nodenum-or-quotep-for-larger-dag extended-smaller-dag)
;;                 (merge-dag-into-dag-quick larger-dag smaller-dag)
;; ;fixme call a blessed dag builder function here?
;;                 (acons-fast (len extended-smaller-dag) ;the nodenum
;;                             `(equal ,nodenum-or-quotep-for-larger-dag ,(+ -1 smaller-dag-len)) ;fixme could the equality expression ever be present in the dag? ;ffixme what if the top nodes are the same?
;;                             extended-smaller-dag))))))

;;       (mv-let (dag-array dag-len top-nodea top-nodeb)
;;               (merge-dags-allows-constants-better dag1 dag2)
;;               (acons-fast dag-len
;;                           `(equal ,top-nodea ,top-nodeb) ;fixme could the equality expression ever be present in the dag? ;ffixme what if the top nodes are the same?
;;                           (array-to-alist 'dag-array dag-array dag-len) ;ffixme skip this conversion?
;;                           )))))
