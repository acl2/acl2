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
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/leftrotate" :dir :system)
(include-book "kestrel/bv/leftrotate32" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/bv/bitor" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(include-book "kestrel/bv/bvuminus" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv-lists/bvchop-list2" :dir :system))

;; For each of these, the defun should be disabled and the defthm enabled:

(defund trim-unguarded (size i)
  (declare (xargs :guard t))
  (trim (nfix size) (ifix i)))

(defthm trim-unguarded-correct
  (equal (trim-unguarded size i)
         (trim size i))
  :hints (("Goal" :in-theory (enable trim trim-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvlt-unguarded (size x y)
  (declare (xargs :guard t))
  (bvlt (nfix size) (ifix x) (ifix y)))

(defthm bvlt-unguarded-correct
  (equal (bvlt-unguarded size x y)
         (bvlt size x y))
  :hints (("Goal" :in-theory (enable bvlt-unguarded bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sbvlt-unguarded (size x y)
  (declare (xargs :guard t))
  (if (not (posp size))
      (sbvlt 1 (ifix x) (ifix y))
    (sbvlt size (ifix x) (ifix y))))

(defthm sbvlt-unguarded-correct
  (equal (sbvlt-unguarded size x y)
         (sbvlt size x y))
  :hints (("Goal" :in-theory (enable sbvlt sbvlt-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvplus-unguarded (size x y)
  (declare (xargs :guard t))
  (bvplus (nfix size) (ifix x) (ifix y)))

(defthm bvplus-unguarded-correct
  (equal (bvplus-unguarded size x y)
         (bvplus size x y))
  :hints (("Goal" :in-theory (enable bvplus bvplus-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvmult-unguarded (size x y)
  (declare (xargs :guard t))
  (bvmult (nfix size) (ifix x) (ifix y)))

(defthm bvmult-unguarded-correct
  (equal (bvmult-unguarded size x y)
         (bvmult size x y))
  :hints (("Goal" :in-theory (enable bvmult bvmult-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvchop-unguarded (size i)
  (declare (xargs :guard t))
  (bvchop (nfix size) (ifix i)))

(defthm bvchop-unguarded-correct
  (equal (bvchop-unguarded size i)
         (bvchop size i))
  :hints (("Goal" :in-theory (enable bvchop-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvxor-unguarded (size x y)
  (declare (xargs :guard t))
  (bvxor (nfix size) (ifix x) (ifix y)))

(defthm bvxor-unguarded-correct
  (equal (bvxor-unguarded size x y)
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor bvxor-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund take-unguarded (n lst)
  (declare (xargs :guard t))
  (if (true-listp lst)
      (take (nfix n) lst)
    (take (nfix n) (true-list-fix lst))))

(defthm take-unguarded-correct
  (equal (take-unguarded n lst)
         (take n lst))
  :hints (("Goal" :in-theory (e/d (take-unguarded take) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund repeat-unguarded (n x)
  (declare (xargs :guard t))
  (repeat (nfix n) x))

(defthm repeat-unguarded-correct
  (equal (repeat-unguarded n x)
         (repeat n x))
  :hints (("Goal" :in-theory (enable repeat-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bv-array-read-unguarded (element-size len index data)
  (declare (xargs :guard t))
  (bv-array-read (nfix element-size) (nfix len) (ifix index) (true-list-fix data)))

(defthm bv-array-read-unguarded-correct
  (equal (bv-array-read-unguarded element-size len index data)
         (bv-array-read element-size len index data))
  :hints (("Goal" :in-theory (enable bv-array-read-unguarded bv-array-read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund leftrotate32-unguarded (amt val)
  (declare (xargs :guard t))
  (leftrotate 32 (ifix amt) (ifix val)))

(defthm leftrotate32-unguarded-correct
  (equal (leftrotate32-unguarded amt val)
         (leftrotate32 amt val))
  :hints (("Goal" :in-theory (enable leftrotate32-unguarded
                                     leftrotate32
                                     leftrotate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logtail-unguarded (size i)
  (declare (xargs :guard t))
  (logtail (nfix size) (ifix i)))

(defthm logtail-unguarded-correct
  (equal (logtail-unguarded size i)
         (logtail size i))
  :hints (("Goal" :in-theory (enable logtail-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund coerce-unguarded (x y)
  (declare (xargs :guard t))
  (cond ((equal y 'list)
         (if (stringp x)
             (coerce x 'list)
           nil))
        (t (coerce (make-character-list x) 'string))))

(defthm coerce-unguarded-correct
  (equal (coerce-unguarded x y)
         (coerce x y))
  :hints (("Goal" :in-theory (enable coerce-unguarded)
           :use (:instance completion-of-coerce))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund lg-unguarded (x)
  (declare (xargs :guard t))
  (lg (ifix x)))

(defthm lg-unguarded-correct
  (equal (lg-unguarded x)
         (lg x))
  :hints (("Goal" :in-theory (enable lg lg-unguarded integer-length))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bitnot-unguarded (x)
  (declare (xargs :guard t))
  (bitnot (ifix x)))

(defthm bitnot-unguarded-correct
  (equal (bitnot-unguarded x)
         (bitnot x))
  :hints (("Goal" :in-theory (enable bitnot-unguarded getbit-when-val-is-not-an-integer))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bitor-unguarded (x y)
  (declare (xargs :guard t))
  (bitor (ifix x) (ifix y)))

(defthm bitor-unguarded-correct
  (equal (bitor-unguarded x y)
         (bitor x y))
  :hints (("Goal" :in-theory (enable bitor-unguarded bitor bvor getbit-when-val-is-not-an-integer))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bitxor-unguarded (x y)
  (declare (xargs :guard t))
  (bitxor (ifix x) (ifix y)))

(defthm bitxor-unguarded-correct
  (equal (bitxor-unguarded x y)
         (bitxor x y))
  :hints (("Goal" :in-theory (e/d (bitxor-unguarded bitxor getbit-when-val-is-not-an-integer) (bvxor-1-becomes-bitxor)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bitand-unguarded (x y)
  (declare (xargs :guard t))
  (bitand (ifix x) (ifix y)))

(defthm bitand-unguarded-correct
  (equal (bitand-unguarded x y)
         (bitand x y))
  :hints (("Goal" :in-theory (e/d (bitand-unguarded bitand bvand getbit-when-val-is-not-an-integer) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund getbit-unguarded (n x)
  (declare (xargs :guard t))
  (getbit (nfix n) (ifix x)))

(defthm getbit-unguarded-correct
  (equal (getbit-unguarded n x)
         (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit-unguarded getbit bitand getbit-when-val-is-not-an-integer slice) (BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvnot-unguarded (size i)
  (declare (xargs :guard t))
  (bvnot (nfix size) (ifix i)))

(defthm bvnot-unguarded-correct
  (equal (bvnot-unguarded size i)
         (bvnot size i))
  :hints (("Goal" :in-theory (enable bvnot-unguarded bvnot))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvuminus-unguarded (size i)
  (declare (xargs :guard t))
  (bvuminus (nfix size) i))

(defthm bvuminus-unguarded-correct
  (equal (bvuminus-unguarded size i)
         (bvuminus size i))
  :hints (("Goal" :in-theory (e/d (bvuminus-unguarded bvuminus bvminus) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvor-unguarded (size x y)
  (declare (xargs :guard t))
  (bvor (nfix size) (ifix x) (ifix y)))

(defthm bvor-unguarded-correct
  (equal (bvor-unguarded size x y)
         (bvor size x y))
  :hints (("Goal" :in-theory (enable bvor bvor-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvand-unguarded (size x y)
  (declare (xargs :guard t))
  (bvand (nfix size) (ifix x) (ifix y)))

(defthm bvand-unguarded-correct
  (equal (bvand-unguarded size x y)
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand bvand-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvminus-unguarded (size x y)
  (declare (xargs :guard t))
  (bvminus (nfix size) (ifix x) (ifix y)))

(defthm bvminus-unguarded-correct
  (equal (bvminus-unguarded size x y)
         (bvminus size x y))
  :hints (("Goal" :in-theory (enable bvminus bvminus-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvmod-unguarded (size x y)
  (declare (xargs :guard t))
  (if (not (posp size))
      0
    (if (equal 0 (bvchop size (ifix y)))
        (bvchop size (ifix x))
      (bvmod size (ifix x) (ifix y)))))

(defthm bvmod-unguarded-correct
  (equal (bvmod-unguarded size x y)
         (bvmod size x y))
  :hints (("Goal" :in-theory (enable bvmod bvmod-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvdiv-unguarded (size x y)
  (declare (xargs :guard t))
  (if (not (posp size))
      0
    (if (equal 0 (bvchop size (ifix y)))
        0
      (bvdiv size (ifix x) (ifix y)))))

(defthm bvdiv-unguarded-correct
  (equal (bvdiv-unguarded size x y)
         (bvdiv size x y))
  :hints (("Goal" :in-theory (enable bvdiv bvdiv-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvcat-unguarded (highsize highval lowsize lowval)
  (declare (xargs :guard t))
  (logapp (nfix lowsize)
          (ifix lowval) (bvchop (nfix highsize) (ifix highval))))

(defthm bvcat-unguarded-correct
  (equal (bvcat-unguarded highsize highval lowsize lowval)
         (bvcat highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (e/d (bvcat bvcat-unguarded) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund eql-unguarded (x y)
  (declare (xargs :guard t))
  (equal x y))

(defthm eql-unguarded-correct
  (equal (eql-unguarded x y)
         (eql x y))
  :hints (("Goal" :in-theory (enable eql-unguarded eql))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund eq-unguarded (x y)
  (declare (xargs :guard t))
  (equal x y))

(defthm eq-unguarded-correct
  (equal (eq-unguarded x y)
         (eq x y))
  :hints (("Goal" :in-theory (enable eq-unguarded eq))))
