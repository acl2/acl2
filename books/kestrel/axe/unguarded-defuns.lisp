; Versions of functions with guards of t
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

(include-book "kestrel/bv/trim" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/leftrotate" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/bv-lists/bvchop-list2" :dir :system))

;; For each of these, the defun should be disabled and the defthm enabled:

(defund trim-unguarded (size i)
  (declare (xargs :guard t))
  (trim (nfix size) (ifix i)))

(defthm trim-unguarded-correct
  (equal (trim-unguarded size i)
         (trim size i))
  :hints (("Goal" :in-theory (enable trim trim-unguarded))))

(defund bvplus-unguarded (size x y)
  (declare (xargs :guard t))
  (bvplus (nfix size) (ifix x) (ifix y)))

(defthm bvplus-unguarded-correct
  (equal (bvplus-unguarded size x y)
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus bvplus-unguarded))))

(defund bvchop-unguarded (size i)
  (declare (xargs :guard t))
  (bvchop (nfix size) (ifix i)))

(defthm bvchop-unguarded-correct
  (equal (bvchop-unguarded size i)
         (bvchop size i))
  :hints (("Goal" :in-theory (enable bvchop-unguarded))))

(defund bvxor-unguarded (size x y)
  (declare (xargs :guard t))
  (bvxor (nfix size) (ifix x) (ifix y)))

(defthm bvxor-unguarded-correct
  (equal (bvxor-unguarded size x y)
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor bvxor-unguarded))))

(defund nthcdr-unguarded (n l)
  (declare (xargs :guard t))
  (if (or (not (natp n))
          (<= n 0))
      l
    (if (consp l)
        (nthcdr-unguarded (+ n -1) (cdr l))
      nil)))

(defthm nthcdr-unguarded-correct
  (equal (nthcdr-unguarded n l)
         (nthcdr n l))
  :hints (("Goal" :in-theory (enable nthcdr-unguarded))))

(defund take-unguarded (n lst)
  (declare (xargs :guard t))
  (if (true-listp lst)
      (take (nfix n) lst)
    (take (nfix n) (true-list-fix lst))))

(defthm take-unguarded-correct
  (equal (take-unguarded n lst)
         (take n lst))
  :hints (("Goal" :in-theory (e/d (take-unguarded take) ()))))

(defund reverse-list-unguarded (x)
  (declare (xargs :guard t))
  (if (true-listp x)
      (reverse-list x)
    (reverse-list (true-list-fix x))))

(defthm reverse-list-unguarded-correct
  (equal (reverse-list-unguarded x)
         (reverse-list x))
  :hints (("Goal" :in-theory (enable reverse-list-unguarded
                                     reverse-list))))

(defund repeat-unguarded (n x)
  (declare (xargs :guard t))
  (repeat (nfix n) x))

(defthm repeat-unguarded-correct
  (equal (repeat-unguarded n x)
         (repeat n x))
  :hints (("Goal" :in-theory (enable repeat-unguarded))))

(defund bv-array-write-unguarded (element-size len index val data)
  (declare (xargs :guard t))
  (if (and (natp len)
           (natp index)
           (natp element-size)
           (true-listp data))
      (bv-array-write element-size len index val data)
    (bv-array-write (nfix element-size)
                    (nfix len)
                    (BVCHOP (CEILING-OF-LG (nfix LEN)) (IFIX INDEX)) ;(nfix index) ;todo: conside treatment of negative indices
                    val
                    (true-list-fix data))))

(defund bv-array-read-unguarded (element-size len index data)
  (declare (xargs :guard t))
  (bv-array-read (nfix element-size) (nfix len) (ifix index) (true-list-fix data)))

(defthm bv-array-read-unguarded-correct
  (equal (bv-array-read-unguarded element-size len index data)
         (bv-array-read element-size len index data))
  :hints (("Goal" :in-theory (enable bv-array-read-unguarded bv-array-read))))

;move
(local
 (defthm update-nth-of-true-list-fix
   (equal (update-nth key val (true-list-fix l))
          (true-list-fix (update-nth key val l)))
   :hints (("Goal" :in-theory (enable true-list-fix update-nth)))))


;move
(local
 (defthm update-nth2-of-true-list-fix
   (equal (update-nth2 len key val (true-list-fix lst))
          (update-nth2 len key val lst))
   :hints (("Goal" :in-theory (e/d (update-nth2 ;update-nth
                                    )
                                   (true-list-fix))))))

(defthm bv-array-write-unguarded-correct
  (equal (bv-array-write-unguarded element-size len index val data)
         (bv-array-write           element-size len index val data))
  :hints (("Goal" :in-theory (enable bv-array-write-unguarded bv-array-write))))

(DEFUNd LEFTROTATE32-unguarded (AMT VAL)
  (declare (xargs :guard t))
  (LEFTROTATE 32 (ifix AMT) (ifix VAL)))

(defthm LEFTROTATE32-unguarded-correct
  (equal (LEFTROTATE32-unguarded amt val)
         (LEFTROTATE32 amt val))
  :hints (("Goal" :in-theory (enable LEFTROTATE32-unguarded
                                     LEFTROTATE32
                                     LEFTROTATE))))
;;
;; width-of-widest-int-unguarded
;;

(defun map-ifix (x)
  (declare (xargs :guard t))
  (if (atom x)
      x
    (cons (ifix (first x))
          (map-ifix (rest x)))))

;; TODO: Make this more efficient?
(defund width-of-widest-int-unguarded (ints)
  (declare (xargs :guard t))
  (width-of-widest-int (map-ifix ints)))

(defthm width-of-widest-int-unguarded-correct
  (equal (width-of-widest-int-unguarded ints)
         (width-of-widest-int ints))
  :hints (("Goal" :in-theory (enable width-of-widest-int-unguarded
                                     width-of-widest-int
                                     integer-length))))

(defund logtail-unguarded (size i)
  (declare (xargs :guard t))
  (logtail (nfix size) (ifix i)))

(defthm logtail-unguarded-correct
  (equal (logtail-unguarded size i)
         (logtail size i))
  :hints (("Goal" :in-theory (enable logtail-unguarded))))

(defund slice-unguarded (high low val)
  (declare (xargs :guard t))
  (let ((low (ifix low))
        (high (ifix high)))
       (bvchop-unguarded (+ 1 high (- low))
                         (logtail-unguarded low val))))

(defthm slice-unguarded-correct
  (equal (slice-unguarded high low val)
         (slice high low val))
  :hints (("Goal" :in-theory (enable slice slice-unguarded))))
