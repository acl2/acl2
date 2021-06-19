; Computing the size of a DAG (if it was a term)
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

;; This book contains a utility to compute the size of a DAG (if it were
;; represented as a tree).  See also dag-size2.lisp.

(include-book "dag-arrays")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

(in-theory (disable bounded-dag-exprp)) ;move?

(local (in-theory (enable not-<-of-car-when-all-<)))

(local
 (defthm <-of-0-and-len
   (equal (< 0 (len x))
          (consp x))
   :hints (("Goal" :in-theory (e/d (len) (len-of-cdr))))))

;; Defines size-arrayp
(def-typed-acl2-array size-arrayp (natp val) :default-satisfies-predp nil)

;todo: have def-typed-acl2-array generate this
(defthm type-of-aref1-when-size-arrayp-2
  (implies (and (size-arrayp array-name array (+ 1 index))
                (natp index))
           (let ((val (aref1 array-name array index)))
             (natp val)))
  :hints (("Goal"
           :use (:instance type-of-aref1-when-size-arrayp-aux
                           (top-index index))
           :in-theory (e/d (size-arrayp)
                           (type-of-aref1-when-size-arrayp-aux)))))

(local
 (defthm integer-when-natp
   (implies (natp x)
            (integerp x))))

(local
 (defthm acl2-numberp-when-natp
   (implies (natp x)
            (acl2-numberp x))))

(local
 (defthm <=-of-+-when-natp-and-natp
   (implies (and (natp x)
                 (natp y))
            (<= 0 (+ x y)))))

(local
 (defthm natp-of-+-when-natp-and-natp
   (implies (and (natp x)
                 (natp y))
            (natp (+ x y)))))
(local
 (defthm natp-of-if
   (equal (natp (if test tp ep))
          (if test (natp tp) (natp ep)))))

(local (in-theory (disable natp)))

;;;
;;; add-arg-sizes-with-name
;;;

;; Add to ACC the sizes of all of the DARGS that are nodenums
(defund add-arg-sizes-with-name (dargs size-array-name size-array acc)
  (declare (xargs :guard (and (true-listp dargs)
                              (all-dargp dargs)
                              (size-arrayp size-array-name size-array (+ 1 (largest-non-quotep dargs)))
                              (natp acc))))
  (if (endp dargs)
      acc
    (let ((darg (first dargs)))
      (add-arg-sizes-with-name (rest dargs)
                               size-array-name
                               size-array
                               (+ (if (consp darg) ;check for a quotep, which we say has size 1
                                      1
                                    ;; dargs is a nodenum, so look up its size:
                                    (aref1 size-array-name size-array darg))
                                  acc)))))

(defthm natp-of-add-arg-sizes-with-name
  (implies (and (all-dargp dargs)
                (size-arrayp size-array-name size-array (+ 1 (largest-non-quotep dargs)))
                (natp acc))
           (natp (add-arg-sizes-with-name dargs size-array-name size-array acc)))
  :hints (("Goal" :in-theory (enable add-arg-sizes-with-name))))

;;;
;;; make-size-array-for-dag-array-aux
;;;

;; This version of the array filler stores a size for every node in the array.
;; Returns the populated size-array.
(defund make-size-array-for-dag-array-aux (n dag-len dag-array-name dag-array size-array-name size-array)
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
    (make-size-array-for-dag-array-aux (+ 1 n)
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
                                                  (add-arg-sizes-with-name (dargs expr) size-array-name size-array 1)))))))

(defthm array1p-of-make-size-array-for-dag-array-aux
  (implies (and (array1p size-array-name size-array)
                (natp n)
                (equal len (alen1 size-array-name size-array)))
           (array1p size-array-name (make-size-array-for-dag-array-aux n len dag-array-name dag-array size-array-name size-array)))
  :hints (("Goal"
           :induct (make-size-array-for-dag-array-aux n len dag-array-name dag-array size-array-name size-array)
           :in-theory (enable make-size-array-for-dag-array-aux))))

(defthm alen1-of-make-size-array-for-dag-array-aux
  (implies (and (array1p size-array-name size-array)
                (natp n)
                (equal len (alen1 size-array-name size-array)))
           (equal (alen1 size-array-name (make-size-array-for-dag-array-aux n len dag-array-name dag-array size-array-name size-array))
                  (alen1 size-array-name size-array)))
  :hints (("Goal"
           :induct (make-size-array-for-dag-array-aux n len dag-array-name dag-array size-array-name size-array)
           :in-theory (enable make-size-array-for-dag-array-aux))))

(defthm size-arrayp-of-make-size-array-for-dag-array-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (natp n)
                (<= n dag-len)
                (<= dag-len (alen1 size-array-name size-array))
                (size-arrayp size-array-name size-array n) ;vals up to n-1 are correct
                (<= bound dag-len)
                (natp bound))
           (size-arrayp size-array-name
                        (make-size-array-for-dag-array-aux n dag-len dag-array-name dag-array size-array-name size-array)
                        bound))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array-aux))))

;;;
;;; make-size-array-for-dag-array
;;;

;; Makes an array named SIZE-ARRAY-NAME and populates it with a size for every
;; node in the dag less than dag-len.  Returns the populated size-array.
(defund make-size-array-for-dag-array (dag-len dag-array-name dag-array size-array-name)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (symbolp size-array-name))))
  (make-size-array-for-dag-array-aux 0
                                     dag-len
                                     dag-array-name
                                     dag-array
                                     size-array-name
                                     (make-empty-array size-array-name dag-len)))

(defthm array1p-of-make-size-array-for-dag-array
  (implies (and (posp dag-len)
                (<= dag-len 2147483646)
                (symbolp size-array-name))
           (array1p size-array-name (make-size-array-for-dag-array dag-len dag-array-name dag-array size-array-name)))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array))))

(defthm size-arrayp-of-make-size-array-for-dag-array
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (posp dag-len)
                (<= dag-len 2147483646)
                (symbolp size-array-name)
                (<= bound dag-len)
                (natp bound)
                )
           (size-arrayp size-array-name
                        (make-size-array-for-dag-array dag-len dag-array-name dag-array size-array-name)
                        bound))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array))))

(defthm alen1-of-make-size-array-for-dag-array
  (implies (and (posp dag-len)
                (<= dag-len 2147483646)
                (symbolp size-array-name))
           (equal (alen1 size-array-name (make-size-array-for-dag-array dag-len dag-array-name dag-array size-array-name))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag-array))))

;;;
;;; dag-size
;;;

;; Returns the size of the tree represented by the DAG (may be a very large number).
;; Smashes the array named 'size-array.
(defund dag-size (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (len dag) 2147483647) ;weaken?
                              )
                  :guard-hints (("Goal" :in-theory (enable pseudo-dagp)))))
  (let* ((size-array-name 'size-array)
         (dag-array-name 'dag-array-for-size-computation)
         (dag-array (make-into-array dag-array-name dag)) ;todo: avoid making this array?
         (size-array (make-size-array-for-dag-array (len dag)
                                                    dag-array-name
                                                    dag-array
                                                    size-array-name)))
    ;; The size of the DAG is the size of its top node in the populated size-array:
    (aref1 size-array-name size-array (top-nodenum-of-dag dag))))

(defthm natp-of-dag-size
  (implies (and (pseudo-dagp dag)
                (< (len dag) 2147483647) ;weaken?
                )
           (natp (dag-size dag)))
  :hints (("Goal" :in-theory (enable dag-size
                                     car-of-car-when-pseudo-dagp-cheap))))

;;;
;;; dag-or-quotep-size
;;;

(defund dag-or-quotep-size (x)
  (declare (xargs :guard (or (and (pseudo-dagp x)
                                  (< (len x) 2147483647))
                             (myquotep x))))
  (if (quotep x)
      1 ; we say a quoted constant has size 1
    (dag-size x)))

(defthm natp-of-dag-or-quotep-size
  (implies (or (and (pseudo-dagp x)
                    (< (len x) 2147483647))
               (myquotep x))
           (natp (dag-or-quotep-size x)))
  :hints (("Goal" :in-theory (enable dag-or-quotep-size))))
