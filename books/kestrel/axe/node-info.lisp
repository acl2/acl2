; Computing information about DAG nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-info")
(include-book "dag-arrays")
;(include-book "dags")

;; ;; todo: optimize by keeping lists sorted and merging
;; (defund add-nodenums-to-acc (dargs acc)
;;   (declare (xargs :guard (and (all-dargp dargs)
;;                               (true-listp dargs)
;;                               (all-natp acc)
;;                               (true-listp acc))))
;;   (if (endp dargs)
;;       acc
;;     (let ((darg (first dargs)))
;;       (if (consp darg) ;; test for quoted constant
;;           (add-nodenums-to-acc (rest dargs) acc)
;;         (add-nodenums-to-acc (rest dargs) (add-to-set-eql darg acc))))))

;; (defthm all-natp-of-add-nodenums-to-acc
;;   (implies (and (all-dargp dargs)
;;                 (true-listp dargs)
;;                 (all-natp acc)
;;                 (true-listp acc))
;;            (all-natp (add-nodenums-to-acc dargs acc)))
;;   :hints (("Goal" :in-theory (enable add-nodenums-to-acc))))

;; (defthm true-listp-of-add-nodenums-to-acc
;;   (implies (and (all-dargp dargs)
;;                 (true-listp dargs)
;;                 (all-natp acc)
;;                 (true-listp acc))
;;            (true-listp (add-nodenums-to-acc dargs acc)))
;;   :hints (("Goal" :in-theory (enable add-nodenums-to-acc))))

;; ;; Adds into ACC all the nodenums that support NODENUM
;; (defun add-supporters-of-node (nodenum dag-array-name dag-array dag-len acc)
;;   (declare (xargs :guard (and (natp nodenum)
;;                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                               (< nodenum dag-len)
;;                               (all-natp acc)
;;                               (true-listp acc)))
;;            (ignore dag-len))
;;   (let ((expr (aref1 dag-array-name dag-array nodenum)))
;;     (if (or (variablep expr)
;;             (fquotep expr))
;;         acc
;;       (add-nodenums-to-acc (dargs expr) acc))))

;; (defthm all-natp-of-add-supporters-of-node
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (< nodenum dag-len)
;;                 (all-natp acc)
;;                 (true-listp acc))
;;            (all-natp (add-supporters-of-node nodenum dag-array-name dag-array dag-len acc)))
;;   :hints (("Goal" :in-theory (enable add-supporters-of-node))))

;; (defthm true-listp-of-add-supporters-of-node
;;   (implies (and (natp nodenum)
;;                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (< nodenum dag-len)
;;                 (all-natp acc)
;;                 (true-listp acc))
;;            (true-listp (add-supporters-of-node nodenum dag-array-name dag-array dag-len acc)))
;;   :hints (("Goal" :in-theory (enable add-supporters-of-node))))

;; (defun immediate-supporters-of-nodes (nodenums dag-array-name dag-array dag-len acc)
;;   (declare (xargs :guard (and (all-natp nodenums)
;;                               (true-listp nodenums)
;;                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                               (all-< nodenums dag-len)
;;                               (all-natp acc)
;;                               (true-listp acc))))
;;   (if (endp nodenums)
;;       acc
;;     (immediate-supporters-of-nodes (rest nodenums)
;;                                    dag-array-name dag-array dag-len
;;                                    (add-supporters-of-node (first nodenums) dag-array-name dag-array dag-len acc))))

;; ;;          (add-immediate-supporters (list nodenum) dag-array-name dag-array dag-len supporters-acc)

(mutual-recursion
 (defun node-tree-limited (depth darg dag-array-name dag-array dag-len)
   (declare (xargs :guard (and (natp depth)
                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (dargp-less-than darg dag-len))
                   :measure (make-ord 1 (+ 1 (nfix depth)) 1)))
   (if (or (zp depth)   ; hit the depth limit
           (consp darg) ;test for quotep
           )
       darg
     (let ((expr (aref1 dag-array-name dag-array darg)))
       (if (or (variablep expr)
               (fquotep expr))
           expr
         `(,(ffn-symb expr) ,@(node-trees-limited (+ -1 depth) (dargs expr) dag-array-name dag-array dag-len))))))

 (defun node-trees-limited (depth dargs dag-array-name dag-array dag-len)
   (declare (xargs :guard (and (natp depth)
                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (bounded-darg-listp dargs dag-len))
                   :measure (make-ord 1 (+ 1 (nfix depth)) (+ 1 (len dargs)))))
   (if (endp dargs)
       nil
     (cons (node-tree-limited depth (first dargs) dag-array-name dag-array dag-len)
           (node-trees-limited depth (rest dargs) dag-array-name dag-array dag-len)))))

(defun print-node-tree-limited (nodenum dag depth)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dagp dag)
                              (<= nodenum (top-nodenum dag))
                              (< (top-nodenum dag) 2147483646)
                              (posp depth))
                  :guard-hints (("Goal" :in-theory (enable CAR-OF-CAR-WHEN-PSEUDO-DAGP)))))
  (let* ((dag-array-name 'dag-array-for-node-info)
         (dag-array (make-dag-into-array 'dag-array-for-node-info dag 0))
         (top-nodenum (top-nodenum dag))
         (dag-len (+ 1 top-nodenum)))
    (cw "~X01~%"
        (node-tree-limited depth nodenum dag-array-name dag-array dag-len)
        nil)))

(defun node-info-fn (nodenum dag depth)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dagp dag)
                              (<= nodenum (top-nodenum dag))
                              (< (top-nodenum dag) 2147483646)
                              (posp depth))))
  (print-node-tree-limited nodenum dag depth))

;; todo: record the dag when we first get info on it and make it optional here
;; todo: print more info
(defmacro node-info (nodenum dag &key (depth '6))
  `(node-info-fn ,nodenum ,dag ,depth))
