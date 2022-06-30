; More tools to compute DAG sizes
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

;; This version of the dag-size utility operates without turning the dag into an array.

;; The time spent is dominated by the additions done in ADD-DARG-SIZES.

(include-book "consecutivep")
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "dags")
(include-book "dag-size-array")
(local (include-book "consecutivep2"))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (enable not-<-of-car-when-all-<
                          <=-of-0-when-0-natp
                          acl2-numberp-when-natp
                          integerp-when-natp)))

(local (in-theory (disable natp weak-dagp-aux top-nodenum)))

(defthmd <-of-car-of-car-when-all-<-of-strip-cars
  (implies (and (all-< (strip-cars x) bound)
                (consp x))
           (< (car (car x)) bound))
  :hints (("Goal" :in-theory (enable strip-cars all-<))))

;dup
(local
 (defthm all-<-of-strip-cars-of-cdr
  (implies (all-< (strip-cars alist) bound)
           (all-< (strip-cars (cdr alist)) bound))
  :hints (("Goal" :in-theory (enable strip-cars)))))

(defthm strip-cars-of-reverse-list
  (equal (strip-cars (reverse-list dag))
         (reverse-list (strip-cars dag)))
  :hints (("Goal" :in-theory (enable reverse-list strip-cars))))

;;;
;;; make-size-array-for-rev-dag-aux
;;;

;; This version of the array filler stores a size for every node in the array.
;; Returns the array, whose name is 'SIZE-ARRAY.
(defund make-size-array-for-rev-dag-aux (rev-dag size-array)
  (declare (xargs :guard (and (weak-dagp-aux rev-dag)
                              ;;vals up until the current node are filled in
                              (size-arrayp 'size-array size-array (if (consp rev-dag)
                                                                      (car (car rev-dag))
                                                                    0))
                              (all-< (strip-cars rev-dag) (alen1 'size-array size-array))
                              (consecutivep (strip-cars rev-dag)))
                  :guard-hints (("Goal" :in-theory (enable weak-dagp-aux)))))
  (if (endp rev-dag)
      size-array
    (make-size-array-for-rev-dag-aux (rest rev-dag)
                                     (let* ((entry (first rev-dag))
                                            (nodenum (car entry))
                                            (expr (cdr entry)))
                                       (aset1 'size-array
                                              size-array
                                              nodenum
                                              (if (or (variablep expr)
                                                      (fquotep expr))
                                                  ;; variables and constants have size 1:
                                                  1
                                                ;; the size of a function call node is 1 plus the sizes of its node args,
                                                ;; plus 1 for each constant arg:
                                                ;; todo: bake in the size array name to a version of this:
                                                (add-darg-sizes (dargs expr) size-array 1)))))))

(defthm size-arrayp-of-make-size-array-for-rev-dag-aux
  (implies (and (weak-dagp-aux rev-dag)
                (size-arrayp 'size-array size-array (if (consp rev-dag)
                                                            (car (car rev-dag))
                                                          0))
                (all-< (strip-cars rev-dag) (alen1 'size-array size-array))
                (consecutivep (strip-cars rev-dag))
                (<= bound (if (consp rev-dag)
                              (+ 1 (car (car (last rev-dag))))
                            0))
                (natp bound))
           (size-arrayp 'size-array
                        (make-size-array-for-rev-dag-aux rev-dag size-array)
                        bound))
  :hints (("Goal" :expand ((weak-dagp-aux rev-dag))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable make-size-array-for-rev-dag-aux
                              caar-of-cdr-when-consecutivep-of-strip-cars
                              <-of-car-of-car-when-all-<-of-strip-cars))))

(defthm alen1-of-make-size-array-for-rev-dag-aux
  (implies (and (weak-dagp-aux rev-dag)
                (array1p 'size-array size-array)
                (all-< (strip-cars rev-dag) (alen1 'size-array size-array))
                (consecutivep (strip-cars rev-dag)))
           (equal (alen1 'size-array (make-size-array-for-rev-dag-aux rev-dag size-array))
                  (alen1 'size-array size-array)))
  :hints (("Goal" :expand ((weak-dagp-aux rev-dag)
                           (weak-dagp-aux (cdr rev-dag)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (make-size-array-for-rev-dag-aux
                            caar-of-cdr-when-consecutivep-of-strip-cars
                            <-of-car-of-car-when-all-<-of-strip-cars)
                           (natp)))))

;;;
;;; make-size-array-for-dag
;;;

;; Makes an array named 'SIZE-ARRAY and populates it with a size for every
;; node in the dag.
;; Smashes the array named 'size-array.
(defund make-size-array-for-dag (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (top-nodenum-of-dag dag) 2147483646))))
  (make-size-array-for-rev-dag-aux (reverse-list dag)
                                   (make-empty-array 'size-array (+ 1 (top-nodenum-of-dag dag)))))

(defthm size-arrayp-of-make-size-array-for-dag
  (implies (and (pseudo-dagp dag)
                (< (top-nodenum-of-dag dag) 2147483646)
                (<= bound (len dag))
                (natp bound))
           (size-arrayp 'size-array
                        (make-size-array-for-dag dag)
                        bound))
  :hints (("Goal" :cases ((= bound (len dag)))
           :in-theory (enable make-size-array-for-dag
                              car-of-car-when-pseudo-dagp-cheap))))

(defthm alen1-of-make-size-array-for-dag
  (implies (and (pseudo-dagp dag)
                (< (top-nodenum-of-dag dag) 2147483646))
           (equal (alen1 'size-array (make-size-array-for-dag dag))
                  (len dag)))
  :hints (("Goal" :in-theory (enable make-size-array-for-dag
                                     top-nodenum-when-pseudo-dagp
                                     car-of-car-when-pseudo-dagp-cheap))))

;;;
;;; dag-size-fast
;;;

;; Returns the size of the tree represented by the DAG (may be very large).
;; Smashes the array named 'size-array.
(defund dag-size-fast (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (top-nodenum-of-dag dag) 2147483646))
                  :guard-hints (("Goal"
                                 :use (:instance size-arrayp-of-make-size-array-for-dag
                                                 (bound (len dag)))
                                 :in-theory (e/d (top-nodenum-when-pseudo-dagp)
                                                 (size-arrayp-of-make-size-array-for-dag))))))
  (aref1 'size-array
         (make-size-array-for-dag dag)
         (top-nodenum-of-dag dag)))

(defthm natp-of-dag-size-fast
  (implies (and (pseudo-dagp dag)
                (< (len dag) 2147483647) ;weaken?
                )
           (natp (dag-size-fast dag)))
  :hints (("Goal" :in-theory (e/d (dag-size-fast
                                   top-nodenum-when-pseudo-dagp)
                                  (natp)))))

;;;
;;; dag-or-quotep-size-fast
;;;

;; Smashes the array named 'size-array.
(defund dag-or-quotep-size-fast (x)
  (declare (xargs :guard (or (and (pseudo-dagp x)
                                  (< (len x) 2147483647))
                             (myquotep x))))
  (if (quotep x)
      1
    (dag-size-fast x)))

(defthm natp-of-dag-or-quotep-size-fast
  (implies (or (and (pseudo-dagp x)
                    (< (len x) 2147483647))
               (myquotep x))
           (natp (dag-or-quotep-size-fast x)))
  :hints (("Goal" :in-theory (enable dag-or-quotep-size-fast))))

;;;
;;; dag-size-less-thanp
;;;

;; Smashes the array named 'size-array.
;; We could just compare to the result of dag-size-fast, but not if we optimize this to use the limit
(defund dag-size-less-thanp (dag limit)
  (declare (xargs :guard (and (and (pseudo-dagp dag)
                                   (< (len dag) 2147483647))
                              (natp limit))))
  (if (<= limit (len dag)) ;todo: avoid doing the whole len once limit items are found
      ;; Avoid any size computation for huge dags (assumes the dag is reduced
      ;; in that non-supporters have been dropped) because we know the size
      ;; exceeds the limit:
      nil
    ;; TODO: Consider passing in the limit and stopping as soon as a larger
    ;; node is found (assumes the dag is reduced):
    (< (dag-size-fast dag) limit)))

;;;
;;; dag-or-quotep-size-less-thanp
;;;

;; Smashes the array named 'size-array.
;; We could just compare to dag-or-quotep-size-fast, but not if we optimize this to use the limit
(defund dag-or-quotep-size-less-thanp (dag-or-quotep limit)
  (declare (xargs :guard (and (or (and (pseudo-dagp dag-or-quotep)
                                       (< (len dag-or-quotep) 2147483647))
                                  (myquotep dag-or-quotep))
                              (natp limit))))
  (if (quotep dag-or-quotep) ;size of a quotep is 1
      (< 1 limit)
    (dag-size-less-thanp dag-or-quotep limit)))
