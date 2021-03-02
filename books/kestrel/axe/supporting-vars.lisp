; Computing the vars that support DAG nodes
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
(include-book "dag-arrays")

;;;
;;; vars-that-support-dag-nodes-aux
;;;

;; Extends ACC with the vars that support (any of the) the nodes in the WORKLIST.
(defund vars-that-support-dag-nodes-aux (steps-left worklist dag-array-name dag-array dag-len done-array acc)
  (declare (xargs :guard (and (natp steps-left)
                              (nat-listp worklist)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< worklist dag-len)
                              (symbol-listp acc)
                              (array1p 'done-array done-array)
                              (all-< worklist (alen1 'done-array done-array)))))
  (if (zp steps-left)
      (er hard? 'vars-that-support-dag-nodes-aux "Reached step limit (should not happen).")
    (if (endp worklist)
        acc
      (let ((nodenum (first worklist)))
        (if (aref1 'done-array done-array nodenum)
            (vars-that-support-dag-nodes-aux (+ -1 steps-left) (rest worklist) dag-array-name dag-array dag-len done-array acc)
          (let ((expr (aref1 dag-array-name dag-array nodenum)))
            (if (variablep expr)
                (vars-that-support-dag-nodes-aux (+ -1 steps-left)
                                                 (rest worklist) dag-array-name dag-array dag-len
                                                 (aset1 'done-array done-array nodenum t)
                                                 (add-to-set-eq ;had cons here, but that led to lots of duplicates...
                                                  expr acc))
              (if (fquotep expr)
                  (vars-that-support-dag-nodes-aux (+ -1 steps-left) (rest worklist) dag-array-name dag-array dag-len (aset1 'done-array done-array nodenum t) acc)
                ;;function call:
                (vars-that-support-dag-nodes-aux (+ -1 steps-left) (append-atoms (dargs expr) (rest worklist)) dag-array-name dag-array dag-len (aset1 'done-array done-array nodenum t) acc)))))))))

(defthm true-listp-of-vars-that-support-dag-nodes-aux
  (implies (true-listp acc)
           (true-listp (vars-that-support-dag-nodes-aux steps-left worklist dag-array-name dag-array dag-len done-array acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable vars-that-support-dag-nodes-aux))))

(defthm symbol-listp-of-vars-that-support-dag-nodes-aux
  (implies (and (symbol-listp acc)
                (nat-listp worklist)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< worklist dag-len))
           (symbol-listp (vars-that-support-dag-nodes-aux steps-left worklist dag-array-name dag-array dag-len done-array acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable vars-that-support-dag-nodes-aux))))

;;;
;;; vars-that-support-dag-nodes
;;;

;; Returns the list of the vars that support (any of the) NODENUMS.
(defund vars-that-support-dag-nodes (nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< nodenums dag-len))))
  (if (endp nodenums)
      nil
    (let* ((max-nodenum (maxelem nodenums))
           (max-steps (* 10 (+ 1 max-nodenum))) ;todo
           )
      (vars-that-support-dag-nodes-aux max-steps nodenums dag-array-name dag-array dag-len (make-empty-array 'done-array (+ 1 max-nodenum)) nil))))

(defthm true-listp-of-vars-that-support-dag-nodes
  (true-listp (vars-that-support-dag-nodes nodenums dag-array-name dag-array dag-len))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable vars-that-support-dag-nodes))))

(defthm symbol-listp-of-vars-that-support-dag-nodes
  (implies (and (nat-listp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< nodenums dag-len))
           (symbol-listp (vars-that-support-dag-nodes nodenums dag-array-name dag-array dag-len)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable vars-that-support-dag-nodes))))

;;;
;;; vars-that-support-dag-node
;;;

;; Returns the list of the vars that support NODENUM.
(defun vars-that-support-dag-node (nodenum dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len))))
  (vars-that-support-dag-nodes (list nodenum) dag-array-name dag-array dag-len))
