; Support for worklist algorithms on DAGs
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

;; a book about arrays used in worklist algorithms to track whether nodes are
;; handled (needed for termination).  SEE WORKLIST-ARRAYS.LISP FOR A MORE
;; MODERN APPROACH

(include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system)

;;;
;;; num-handled-nodes
;;;

;; for the measure
;; the number of handled nodes (indicated by non-nil array values in the range [0,n].
(defun num-handled-nodes-aux (n array-name array)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (integerp n)
                              (<= -1 n)
                              (array1p array-name array)
                              (< n (alen1 array-name array)))))
  (if (not (natp n))
      0
    (let ((flag (aref1 array-name array n)))
      (+ (if flag 1 0)
         (num-handled-nodes-aux (+ -1 n) array-name array)))))

;; for the measure
(defthm num-handled-nodes-aux-of-aset1-irrel
  (implies (and (< n n2)
                (array1p array-name array)
                ;(natp n)
                (natp n2)
                (< n (alen1 array-name array))
                (< n2 (alen1 array-name array)))
           (equal (num-handled-nodes-aux n array-name (aset1 array-name array n2 flag))
                  (num-handled-nodes-aux n array-name array)))
  :hints (("Goal" :expand ((num-handled-nodes-aux 0
                                                  array-name
                                                  (aset1 array-name
                                                         array n2 flag))
                           (num-handled-nodes-aux 0 array-name array)))))

(defthm num-handled-nodes-aux-of-aset1
  (implies (and (not (aref1 array-name array n2))
                (array1p array-name array)
                flag
                (natp n)
                (natp n2)
                (<= n2 n)
                (< n (alen1 array-name array)))
           (equal (num-handled-nodes-aux n array-name (aset1 array-name array n2 flag))
                  (+ 1 (num-handled-nodes-aux n array-name array))))
  :hints (("Goal" :expand ((num-handled-nodes-aux 0 array-name
                                                  (aset1 array-name
                                                         array 0 flag))
                           (num-handled-nodes-aux 0 array-name array)))))

;; for the measure
(defund num-handled-nodes (array-name array)
  (declare (xargs :guard (array1p array-name array)))
  (num-handled-nodes-aux (+ -1 (alen1 array-name array))
                         array-name array))

(defthm num-handled-nodes-of-aset1
  (implies (and (not (aref1 array-name array n))
                (array1p array-name array)
                flag
                (natp n)
                (< n (alen1 array-name array)))
           (equal (num-handled-nodes array-name (aset1 array-name array n flag))
                  (+ 1 (num-handled-nodes array-name array))))
  :hints (("Goal" :in-theory (enable num-handled-nodes))))

(defthm num-handled-nodes-aux-bound
  (implies (and (integerp n)
                (<= -1 n)
                ;; (<= n (alen1 array-name array))
                )
           (<= (num-handled-nodes-aux n array-name array)
               (+ 1 n)))
  :rule-classes ((:linear :trigger-terms ((num-handled-nodes-aux n array-name array))))
  :hints (("Goal" :expand ((num-handled-nodes-aux 0 array-name array))
           :in-theory (enable num-handled-nodes-aux))))

(defthm num-handled-nodes-bound
  (implies (natp (alen1 array-name array))
           (<= (num-handled-nodes array-name array)
               (alen1 array-name array)))
  :rule-classes ((:linear :trigger-terms ((num-handled-nodes array-name array))))
  :hints (("Goal" :in-theory (enable num-handled-nodes))))
