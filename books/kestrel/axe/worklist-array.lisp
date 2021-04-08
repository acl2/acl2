; Support for worklist algorithms on DAG nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The worklist-array maps nodenums to :examined or nil (meaning unexamined).

;; TODO: Consider just using t and nil as the elements in this array.

;; TODO: Rename this to the examined-array?

;; See size-array-for-nodes-aux in dag-size2.lisp for an example of how to use the worklist-array.

(include-book "merge-sort-less-than")
(include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system)
(include-book "dags") ;for all-dargp-less-than
(include-book "kestrel/typed-lists-light/all-rationalp" :dir :system)

;; For use in the measure
(defun num-examined-nodes (n array-name array)
  (declare (xargs :measure (nfix (+ 1 n))))
  (if (not (natp n))
      0
    (let ((res (aref1 array-name array n)))
      (if (eq res :examined)
          (+ 1 (num-examined-nodes (+ -1 n) array-name array))
        (num-examined-nodes (+ -1 n) array-name array)))))

(defthm num-examined-nodes-bound
  (implies (and (integerp n)
                (<= -1 n))
           (<= (num-examined-nodes n array-name array)
               (+ 1 n)))
  :rule-classes ((:linear :trigger-terms ((num-examined-nodes n array-name array))))
  :hints (("Goal" :expand ((num-examined-nodes 0 array-name array)))))

(defthm num-examined-nodes-of-aset1-irrel
  (implies (and (array1p array-name array)
                ;; (natp n)
                (< index (alen1 array-name array))
                (natp index)
                (< n index))
           (equal (num-examined-nodes n array-name (aset1 array-name array index :examined))
                  (num-examined-nodes n array-name array)))
  :hints (("Goal" :expand ((num-examined-nodes 0 array-name array)
                           (num-examined-nodes 0 array-name
                                               (aset1 array-name array index :examined))))))

(defthm num-examined-nodes-of-aset1
  (implies (and (array1p array-name array)
                (natp n)
                (< n (alen1 array-name array))
                (natp index)
                (<= index n))
           (equal (num-examined-nodes n array-name (aset1 array-name array index :examined))
                  (if (equal :examined (aref1 array-name array index))
                      (num-examined-nodes n array-name array)
                    (+ 1 (num-examined-nodes n array-name array)))))
  :hints (("Goal" :expand ((num-examined-nodes 0 array-name (aset1 array-name array 0 :examined))))))

;;;
;;; get-unexamined-nodenum-args
;;;

;; Filter the ARGS, keeping only the ones that are nodenums not mapped to
;; :examined in the WORKLIST-ARRAY.  The result comes in reverse order.
(defund get-unexamined-nodenum-args (args worklist-array acc)
  (declare (xargs :guard (and (array1p 'worklist-array worklist-array)
                              (true-listp args)
                              (all-dargp-less-than args (alen1 'worklist-array worklist-array)))))
  (if (endp args)
      acc
    (let* ((arg (first args)))
      (if (or (consp arg) ;it's a quotep, so skip it
              (eq :examined (aref1 'worklist-array worklist-array arg)) ;it's already examined, so skip it
              )
          (get-unexamined-nodenum-args (rest args) worklist-array acc)
        ;; add the arg:
        (get-unexamined-nodenum-args (rest args) worklist-array (cons arg acc))))))

(defthm all-<-of-get-unexamined-nodenum-args
  (implies (and (all-dargp-less-than args bound)
                (all-< acc bound))
           (all-< (get-unexamined-nodenum-args args worklist-array acc)
                  bound))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args))))

(defthm all-natp-of-get-unexamined-nodenum-args
  (implies (and (all-dargp args)
                (all-natp acc))
           (all-natp (get-unexamined-nodenum-args args worklist-array acc)))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args))))

(defthm natp-listp-of-get-unexamined-nodenum-args
  (implies (and (all-dargp args)
                (nat-listp acc))
           (nat-listp (get-unexamined-nodenum-args args worklist-array acc)))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args))))

(defthm all-rationalp-of-get-unexamined-nodenum-args
  (implies (and (all-dargp args)
                (all-rationalp acc))
           (all-rationalp (get-unexamined-nodenum-args args worklist-array acc)))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args))))

(defthm true-listp-of-get-unexamined-nodenum-args
  (equal (true-listp (get-unexamined-nodenum-args args worklist-array acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable get-unexamined-nodenum-args))))
