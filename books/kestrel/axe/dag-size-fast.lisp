; More tools to compute DAG sizes
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

;; This version of the dag-size utility operates without turning the dag into an array.

(include-book "consecutivep")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "dags")
(local (include-book "consecutivep2"))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;dup
(def-typed-acl2-array size-arrayp (natp val) :default-satisfies-predp nil)

;dup
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

(local (in-theory (disable natp)))

;dup
(local
 (defthm natp-of-if
   (equal (natp (if test tp ep))
          (if test (natp tp) (natp ep)))))

;dup
(local
 (defthm natp-of-+-when-natp-and-natp
   (implies (and (natp x)
                 (natp y))
            (natp (+ x y)))))

;dup
(local
 (defthm acl2-numberp-when-natp
   (implies (natp x)
            (acl2-numberp x))))

(defthmd <-of-car-of-car-when-all-<-of-strip-cars
  (implies (and (all-< (strip-cars x) bound)
                (consp x))
           (< (car (car x)) bound))
  :hints (("Goal" :in-theory (enable strip-cars all-<))))

(defthm consecutivep-of-strip-cars-of-cdr
  (implies (consecutivep (strip-cars x))
           (consecutivep (strip-cars (cdr x))))
  :hints (("Goal" :in-theory (enable strip-cars))))

;todo: conflict in dagify2
(local
 (defthm all-<-of-strip-cars-of-cdr
  (implies (all-< (strip-cars x) bound)
           (all-< (strip-cars (cdr x)) bound))
  :hints (("Goal" :in-theory (enable strip-cars)))))

(defthm strip-cars-of-reverse-list
  (equal (strip-cars (reverse-list dag))
         (reverse-list (strip-cars dag)))
  :hints (("Goal" :in-theory (enable reverse-list strip-cars))))

;todo: have def-typed-acl-array-generate this
(defthm size-arrayp-of-aset1-at-end-gen
  (implies (and (size-arrayp array-name array index)
                (natp val)
                (< index (alen1 array-name array))
                (natp index)
                (natp bound)
                (<= bound (+ 1 index)))
           (size-arrayp array-name
                        (aset1 array-name array index val)
                        bound))
  :hints (("Goal" :use (:instance size-arrayp-of-aset1-at-end)
           :in-theory (disable size-arrayp-of-aset1-at-end))))

;;;
;;; add-arg-sizes
;;;

(defund add-arg-sizes (dargs size-array acc)
  (declare (xargs :guard (and (true-listp dargs)
                              (all-dargp dargs)
                              (size-arrayp 'size-array size-array (+ 1 (largest-non-quotep dargs)))
                              (natp acc))
                  :guard-hints (("Goal" :in-theory (disable natp)))))
  (if (endp dargs)
      acc
    (let ((darg (first dargs)))
      (add-arg-sizes (rest dargs)
                     size-array
                     (+ (if (consp darg) ;check for a quotep, which we say has size 1
                            1
                          ;; dargs is a nodenum, so look up its size:
                          (aref1 'size-array size-array darg))
                        acc)))))

(defthm natp-of-add-arg-sizes
  (implies (and ;(true-listp dargs)
                (all-dargp dargs)
                (size-arrayp 'size-array size-array (+ 1 (largest-non-quotep dargs)))
                (natp acc))
           (natp (add-arg-sizes dargs size-array acc)))
  :hints (("Goal" :in-theory (enable add-arg-sizes))))

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
                              (consecutivep (strip-cars rev-dag)))))
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
                                                (add-arg-sizes (dargs expr) size-array 1)))))))

(local (in-theory (disable weak-dagp-aux)))

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
                        bound
                        ))
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

(local (in-theory (disable top-nodenum)))

;; Makes an array named 'SIZE-ARRAY and populates it with a size for every
;; node in the dag.
;; Smashes the array named 'size-array.
(defund make-size-array-for-dag (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (top-nodenum-of-dag dag) 2147483646) ;gen?
                              )))
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
                              (< (len dag) 2147483647) ;weaken?
                              )
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
;;; dag-or-quotep-size-less-thanp
;;;

(defund dag-or-quotep-size-less-thanp (dag-or-quotep limit)
  (declare (xargs :guard (and (or (and (pseudo-dagp dag-or-quotep)
                                       (< (len dag-or-quotep) 2147483647))
                                  (myquotep dag-or-quotep))
                              (natp limit))))
  (if (quotep dag-or-quotep) ;size of a quotep is 1
      (< 1 limit)
    (if (<= limit (len dag-or-quotep)) ;todo: avoid doing the whole len once limit items are found
        ;; Avoid any size computation for huge dags (assumes the dag is reduced
        ;; in that non-supporters have been dropped) because we know the size
        ;; exceeds the limit:
        nil
      ;; TODO: Consider passing in the limit and stopping as soon as a larger
      ;; node is found (assumes the dag is reduced):
      (< (dag-size-fast dag-or-quotep) limit))))
