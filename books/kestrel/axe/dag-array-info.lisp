; Computing information and statistics about dag-arrays.
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

(include-book "dag-info")
;(local (include-book "kestrel/alists-light/alistp" :dir :system))
;(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))

(defund dag-array-vars-aux (dag-array-name
                            dag-array
                            dag-len
                            n
                            acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (integerp n)
                              (< n dag-len)
                              (symbol-listp acc))
                  :measure (nfix (+ 1 n))))
  (if (not (natp n)) ; optimize?
      acc
    (let ((expr (aref1 dag-array-name dag-array n)))
      (dag-array-vars-aux dag-array-name
                          dag-array
                          dag-len
                          (+ -1 n)
                          (if (symbolp expr)
                              (cons expr acc) ; should not already be there
                            acc)))))

(defthm symbol-listp-of-dag-array-vars-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (< n dag-len)
                (symbol-listp acc))
           (symbol-listp (dag-array-vars-aux dag-array-name dag-array dag-len n acc)))
  :hints (("Goal" :in-theory (enable pseudo-dag-arrayp dag-array-vars-aux))))

(defund dag-array-vars (dag-array-name
                        dag-array
                        dag-len)
  (declare (xargs :guard (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
  (dag-array-vars-aux dag-array-name
                      dag-array
                      dag-len
                      (+ -1 dag-len)
                      nil))

(defthm symbol-listp-of-dag-array-vars
  (implies (pseudo-dag-arrayp dag-array-name dag-array dag-len)
           (symbol-listp (dag-array-vars dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable dag-array-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;res is an alist mapping functions in the dag to their occurrence counts
(defun tabulate-dag-array-fns-aux (dag-array-name
                                   dag-array
                                   dag-len
                                   n
                                   alist)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (integerp n)
                              (< n dag-len)
                              (alistp alist)
                              (nat-listp (strip-cdrs alist)))
                  :measure (nfix (+ 1 n))))
  (if (not (natp n)) ; optimize?
      alist
    (let* ((expr (aref1 dag-array-name dag-array n))
           (alist (if (or (variablep expr)
                          (fquotep expr))
                      alist
                    (let* ((fn (ffn-symb expr))
                           (count (or (lookup-eq fn alist) 0))
                           (new-count (+ 1 count)))
                      (acons-unique fn new-count alist)))))
      (tabulate-dag-array-fns-aux dag-array-name dag-array dag-len (+ -1 n) alist))))

(defthm true-listp-of-tabulate-dag-array-fns-aux
  (implies (true-listp alist)
           (true-listp (tabulate-dag-array-fns-aux dag-array-name dag-array dag-len n alist))))

(defthm alistp-of-tabulate-dag-array-fns-aux
  (implies (alistp alist)
           (alistp (tabulate-dag-array-fns-aux dag-array-name dag-array dag-len n alist))))

(defthm all-pair-with-rational-cdrp-of-tabulate-dag-array-fns-aux
  (implies (all-pair-with-rational-cdrp alist)
           (all-pair-with-rational-cdrp (tabulate-dag-array-fns-aux dag-array-name dag-array dag-len n alist)))
  :hints (("Goal" :in-theory (enable tabulate-dag-array-fns-aux))))

(defun tabulate-dag-array-fns (dag-array-name dag-array dag-len)
  (declare (xargs :guard (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
  (tabulate-dag-array-fns-aux dag-array-name dag-array dag-len (+ -1 dag-len) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This assumes the dag-array has been already crunched to drop non-supporters.
(defun print-dag-array-info (dag-array-name dag-array dag-len
                             name
                             print-size)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (or (stringp name)
                                  (null name))
                              (booleanp print-size))))
  (b* ((- (if name
              (cw "(DAG info for ~s0:~%" name)
            (cw "(DAG info:~%")))
       (- (cw " Unique nodes: ~x0~%" dag-len))
       ;; Can be slow:
       (- (and print-size
               (cw " Total nodes: ~x0~%" (dag-array-size dag-array-name dag-array dag-len))))
       ;; These usually get inlined (we could count those):
       ;; (constants (dag-constants dag))
       ;; (- (cw "~x0 constants~%" (len constants)))
       (vars (merge-sort-symbol< (dag-array-vars dag-array-name dag-array dag-len)))
       (- (cw " ~x0 Variables:~%" (len vars)))
       (- (print-symbols-4-per-line vars))
       ;; Don't need to print these, as we print their counts below:
       ;; (fns (dag-array-fns dag))
       ;; (- (cw " ~x0 Functions:~%" (len fns)))
       ;; (- (print-symbols-4-per-line fns))
       (- (cw " Functions and counts:~%"))
       (fn-counts (merge-sort-cdr-< (tabulate-dag-array-fns dag-array-name dag-array dag-len)))
       (- (print-function-counts fn-counts))
       (- (cw ")~%")))
    nil))
