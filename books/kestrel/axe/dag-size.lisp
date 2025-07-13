; Computing the size of a DAG (if it was a term)
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

;; This book contains a utility to compute the size of a DAG (if it were
;; represented as a tree).  See also dag-size-sparse.lisp and dag-size-fast.lisp.

;; TODO: Consider making a version that doesn't use bignums and only approximates the size.

(include-book "dag-arrays")
(include-book "dag-size-array")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/if-rules" :dir :system))

(local (in-theory (enable not-<-of-car-when-all-<
                          <=-of-0-when-natp
                          acl2-numberp-when-natp
                          integerp-when-natp)))

(local (in-theory (disable natp)))

;;;
;;; make-size-array-for-dag-array-with-name-aux
;;;

;; This version of the array filler stores a size for every node in the array.
;; Returns the populated size-array.
(defund make-size-array-for-dag-array-with-name-aux (n dag-len dag-array-name dag-array size-array-name size-array)
  (declare (xargs :measure (+ 1 (nfix (- dag-len n)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp n)
                              (<= n dag-len)
                              (size-arrayp size-array-name size-array n) ;vals up to n-1 are correct
                              (<= dag-len (alen1 size-array-name size-array)))))
  (if (or (>= n dag-len)
          (not (mbt (natp n)))
          (not (mbt (natp dag-len))))
      size-array
    (make-size-array-for-dag-array-with-name-aux (+ 1 n)
                                       dag-len
                                       dag-array-name
                                       dag-array
                                       size-array-name
                                       (aset1 size-array-name
                                              size-array
                                              n
                                              (let ((expr (aref1 dag-array-name dag-array n)))
                                                (if (or (variablep expr)
                                                        (fquotep expr))
                                                    ;; variables and constants have size 1:
                                                    1
                                                  ;; the size of a function call node is 1 plus the sizes of its node args,
                                                  ;; plus 1 for each constant arg:
                                                  (add-darg-sizes-with-name (dargs expr) size-array-name size-array 1)))))))

(defthm array1p-of-make-size-array-for-dag-array-with-name-aux
  (implies (and (array1p size-array-name size-array)
                (natp n)
                (equal len (alen1 size-array-name size-array)))
           (array1p size-array-name (make-size-array-for-dag-array-with-name-aux n len dag-array-name dag-array size-array-name size-array)))
  :hints (("Goal"
           :induct (make-size-array-for-dag-array-with-name-aux n len dag-array-name dag-array size-array-name size-array)
           :in-theory (enable make-size-array-for-dag-array-with-name-aux))))

(defthm alen1-of-make-size-array-for-dag-array-with-name-aux
  (implies (and (array1p size-array-name size-array)
                (natp n)
                (equal len (alen1 size-array-name size-array)))
           (equal (alen1 size-array-name (make-size-array-for-dag-array-with-name-aux n len dag-array-name dag-array size-array-name size-array))
                  (alen1 size-array-name size-array)))
  :hints (("Goal"
           :induct (make-size-array-for-dag-array-with-name-aux n len dag-array-name dag-array size-array-name size-array)
           :in-theory (enable make-size-array-for-dag-array-with-name-aux))))

(defthm size-arrayp-of-make-size-array-for-dag-array-with-name-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp n)
                (<= n dag-len)
                (<= dag-len (alen1 size-array-name size-array))
                (size-arrayp size-array-name size-array n) ;vals up to n-1 are correct
                (<= bound dag-len)
                (natp bound))
           (size-arrayp size-array-name
                        (make-size-array-for-dag-array-with-name-aux n dag-len dag-array-name dag-array size-array-name size-array)
                        bound))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array-with-name-aux))))

;;;
;;; make-size-array-for-dag-array-with-name
;;;

;; Makes an array named SIZE-ARRAY-NAME and populates it with a size for every
;; node in the dag less than dag-len.  Returns the populated size-array.
(defund make-size-array-for-dag-array-with-name (dag-len dag-array-name dag-array size-array-name)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (symbolp size-array-name))))
  (make-size-array-for-dag-array-with-name-aux 0
                                               dag-len
                                               dag-array-name
                                               dag-array
                                               size-array-name
                                               (make-empty-array size-array-name dag-len)))

(defthm array1p-of-make-size-array-for-dag-array-with-name
  (implies (and (posp dag-len)
                (<= dag-len *max-1d-array-length*)
                (symbolp size-array-name))
           (array1p size-array-name (make-size-array-for-dag-array-with-name dag-len dag-array-name dag-array size-array-name)))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array-with-name))))

(defthm size-arrayp-of-make-size-array-for-dag-array-with-name
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (posp dag-len)
                (<= dag-len *max-1d-array-length*)
                (symbolp size-array-name)
                (<= bound dag-len)
                (natp bound))
           (size-arrayp size-array-name
                        (make-size-array-for-dag-array-with-name dag-len dag-array-name dag-array size-array-name)
                        bound))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array-with-name))))

(defthm alen1-of-make-size-array-for-dag-array-with-name
  (implies (and (posp dag-len)
                (<= dag-len *max-1d-array-length*)
                (symbolp size-array-name))
           (equal (alen1 size-array-name (make-size-array-for-dag-array-with-name dag-len dag-array-name dag-array size-array-name))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array-with-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a natp.
;; Smashes the array named 'size-array
(defund dag-array-size (dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len))))
  (let* ((size-array-name 'size-array)
         (size-array (make-size-array-for-dag-array-with-name dag-len
                                                              dag-array-name
                                                              dag-array
                                                              size-array-name)))
    ;; The size of the DAG is the size of its top node in the populated size-array:
    (aref1 size-array-name size-array (+ -1 dag-len))))

(defthm natp-of-dag-array-size
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (posp dag-len))
           (natp (dag-array-size dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable dag-array-size
                                     car-of-car-when-pseudo-dagp-cheap))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the size of the tree represented by the DAG (may be a very large number).
;; Smashes the arrays named 'size-array and 'dag-array-for-size-computation.
(defund dag-size (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) *max-1d-array-length*) ;weaken?
                              )
                  :guard-hints (("Goal" :in-theory (enable pseudo-dagp)))))
  (let* ((dag-array-name 'dag-array-for-size-computation)
         (dag-array (make-into-array dag-array-name dag)) ;todo: avoid making this array?
         )
    (dag-array-size dag-array-name dag-array (len dag))))

(defthm natp-of-dag-size
  (implies (and (pseudo-dagp dag)
                (<= (len dag) *max-1d-array-length*) ;weaken?
                )
           (natp (dag-size dag)))
  :hints (("Goal" :in-theory (enable dag-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the size of the tree represented by the DAG (may be a very large number).
;; This version avoids imposing invariant-risk on callers, because it has a guard of t.
;; Smashes the arrays named 'size-array and 'dag-array-for-size-computation.
(defund dag-size-unguarded (dag)
  (declare (xargs :guard t))
  (if (and (pseudo-dagp dag)
           (<= (len dag) *max-1d-array-length*) ;weaken?
           )
      (dag-size dag)
    (prog2$ (er hard? 'dag-size-unguarded "Bad DAG: ~x0." dag)
            0)))

(defthm natp-of-dag-size-unguarded
  (natp (dag-size-unguarded dag))
  :hints (("Goal" :in-theory (enable dag-size-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the size of the tree represented by X (may be a very large number).
;; A constant is reported as having size 1 (would use a single DAG node).
;; Smashes the arrays named 'size-array and 'dag-array-for-size-computation.
(defund dag-or-quotep-size (x)
  (declare (xargs :guard (or (and (pseudo-dagp x)
                                  (<= (len x) *max-1d-array-length*))
                             (myquotep x))))
  (if (quotep x)
      1 ; we say a quoted constant has size 1
    (dag-size x)))

(defthm natp-of-dag-or-quotep-size
  (implies (or (and (pseudo-dagp x)
                    (<= (len x) *max-1d-array-length*))
               (myquotep x))
           (natp (dag-or-quotep-size x)))
  :hints (("Goal" :in-theory (enable dag-or-quotep-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This one considers huge dags to not have size < n, without even looking at n!
;; This one does not require the DAG to be not too large.
(defund dag-or-quotep-size-less-than (d n)
  (declare (xargs :guard (and (or (pseudo-dagp d)
                                  (myquotep d))
                              (natp n))
                  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))))
  (if (or (myquotep d)
          (<= (len d) *max-1d-array-length*))
      (< (dag-or-quotep-size d) n)
    nil ; the dag is huge
    ))
