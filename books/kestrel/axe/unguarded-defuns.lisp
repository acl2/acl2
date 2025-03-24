; Versions of functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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
;(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/bv/sbvlt" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/bv/bitor" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(include-book "kestrel/bv/bvuminus" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvashr" :dir :system)
(include-book "kestrel/bv/bvequal" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/bit-to-bool-def" :dir :system)
(include-book "kestrel/bv/bool-to-bit-def" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(include-book "kestrel/bv-lists/array-patterns" :dir :system)
(include-book "kestrel/bv-lists/negated-elems-listp" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "unguarded-built-ins") ; for assoc-equal-unguarded
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/bv-lists/bvchop-list2" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

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

(defund bvle-unguarded (size x y)
  (declare (xargs :guard t))
  (bvle (nfix size) (ifix x) (ifix y)))

(defthm bvle-unguarded-correct
  (equal (bvle-unguarded size x y)
         (bvle size x y))
  :hints (("Goal" :in-theory (enable bvle bvle-unguarded bvlt))))

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

(defund sbvle-unguarded (size x y)
  (declare (xargs :guard t))
  (if (not (posp size))
      (sbvle 1 (ifix x) (ifix y))
    (sbvle size (ifix x) (ifix y))))

(defthm sbvle-unguarded-correct
  (equal (sbvle-unguarded size x y)
         (sbvle size x y))
  :hints (("Goal" :in-theory (enable sbvle sbvle-unguarded sbvlt))))

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

(defund bvif-unguarded (size test thenpart elsepart)
  (declare (xargs :guard t))
  (if test (bvchop-unguarded size thenpart)
      (bvchop-unguarded size elsepart)))

(defthm bvif-unguarded-correct
  (equal (bvif-unguarded highsize highval lowsize lowval)
         (bvif           highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (enable bvif bvif-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvequal-unguarded (size x y)
  (declare (xargs :guard t))
  (equal (bvchop-unguarded size x) (bvchop-unguarded size y)))

(defthm bvequal-unguarded-correct
  (equal (bvequal-unguarded size x y)
         (bvequal size x y))
  :hints (("Goal" :in-theory (enable bvequal bvequal-unguarded))))

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
  (let* ((len (nfix len))
         (index (ifix index))
         (numbits (ceiling-of-lg len))
         (index (bvchop numbits index)))
    (if (< index len)
        (bvchop (nfix element-size) (ifix (nth-unguarded-aux index data)))
      0)))

(defthm bv-array-read-unguarded-correct
  (equal (bv-array-read-unguarded element-size len index data)
         (bv-array-read element-size len index data))
  :hints (("Goal" :use (:instance nth-unguarded-correct
                                  (n (bvchop (ceiling-of-lg (nfix len)) (ifix index)))
                                  (l data))
           :in-theory (e/d (bv-array-read-unguarded bv-array-read nth-unguarded)
                           (nth nth-unguarded-correct)))))

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

(defund bvcat-unguarded (highsize highval lowsize lowval)
  (declare (xargs :guard t))
  (logapp (nfix lowsize)
          (ifix lowval) (bvchop (nfix highsize) (ifix highval))))

(defthm bvcat-unguarded-correct
  (equal (bvcat-unguarded highsize highval lowsize lowval)
         (bvcat highsize highval lowsize lowval))
  :hints (("Goal" :in-theory (enable bvcat bvcat-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logtail$inline-unguarded (size i)
  (declare (xargs :guard t))
  (logtail$inline (nfix size) (ifix i)))

(defthm logtail$inline-unguarded-correct
  (equal (logtail$inline-unguarded size i)
         (logtail$inline size i))
  :hints (("Goal" :in-theory (enable logtail$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund slice-unguarded (high low val)
  (declare (xargs :guard t))
  (let ((low (ifix low))
        (high (ifix high)))
       (bvchop-unguarded (+ 1 high (- low))
                         (logtail$inline-unguarded low val))))

(defthm slice-unguarded-correct
  (equal (slice-unguarded high low val)
         (slice high low val))
  :hints (("Goal" :in-theory (enable slice slice-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund leftrotate-unguarded (width amt val)
  (declare (xargs :guard t))
  (if (equal 0 width)
      0
    (let* ((amt (mod-unguarded (ifix amt) width)))
      ;; leftify?
      (bvcat-unguarded (binary-+-unguarded width (unary---unguarded amt))
                       (slice-unguarded (binary-+-unguarded -1 (binary-+-unguarded width (unary---unguarded amt))) 0 val)
                       amt
                       (slice-unguarded (binary-+-unguarded -1 width)
                                        (binary-+-unguarded width (unary---unguarded amt))
                                        val)))))

(defthm leftrotate-unguarded-correct
  (equal (leftrotate-unguarded width amt val)
         (leftrotate width amt val))
  :hints (("Goal" :in-theory (enable leftrotate-unguarded
                                     leftrotate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund leftrotate32-unguarded (amt val)
  (declare (xargs :guard t))
  (leftrotate 32 (mod-unguarded (ifix amt) 32) (ifix val)))

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

(defund map-ifix (x)
  (declare (xargs :guard t))
  (if (atom x)
      x
    (cons (ifix (first x))
          (map-ifix (rest x)))))

;; todo: optimize
(defthm width-of-widest-int-of-map-ifix
  (equal (width-of-widest-int (map-ifix ints))
         (width-of-widest-int ints))
  :hints (("Goal" :in-theory (enable map-ifix
                                     width-of-widest-int))))

;; TODO: Make this more efficient?
(defund width-of-widest-int-unguarded (ints)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable map-ifix)))))
  (width-of-widest-int (map-ifix ints)))

(defthm width-of-widest-int-unguarded-correct
  (equal (width-of-widest-int-unguarded ints)
         (width-of-widest-int ints))
  :hints (("Goal" :in-theory (enable width-of-widest-int-unguarded
                                     width-of-widest-int
                                     integer-length))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund lg-unguarded (x)
  (declare (xargs :guard t))
  (+ -1 (integer-length-unguarded x)))

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
  :hints (("Goal" :in-theory (enable bitand-unguarded bitand bvand getbit-when-val-is-not-an-integer))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund getbit-unguarded (n x)
  (declare (xargs :guard t))
  (getbit (nfix n) (ifix x)))

(defthm getbit-unguarded-correct
  (equal (getbit-unguarded n x)
         (getbit n x))
  :hints (("Goal" :in-theory (e/d (getbit-unguarded getbit bitand getbit-when-val-is-not-an-integer slice) ()))))

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
  :hints (("Goal" :in-theory (enable bvuminus-unguarded bvminus))))

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

(defund lookup-equal-unguarded (key alist)
  (declare (xargs :guard t))
  (let ((res (assoc-equal-unguarded key alist)))
    (if (consp res)
        (cdr res)
      nil)))

(defthm lookup-equal-unguarded-correct
  (equal (lookup-equal-unguarded key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal
                                     lookup-equal-unguarded))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund repeatbit-unguarded (n bit)
  (declare (xargs :guard t))
  (if (natp n)
      (repeatbit n (getbit 0 (ifix bit)))
    0))

(defthm repeatbit-unguarded-correct
  (equal (repeatbit-unguarded n bit)
         (repeatbit n bit))
  :hints (("Goal" :in-theory (enable repeatbit-unguarded
                                     repeatbit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvsx-unguarded (new-size old-size val)
  (declare (xargs :guard t))
  (if (not (posp old-size))
      0
      (if (<-unguarded new-size old-size)
          (bvchop-unguarded new-size val)
          (bvcat-unguarded (- new-size old-size)
                           (repeatbit-unguarded (- new-size old-size)
                                                (getbit-unguarded (+ -1 old-size) val))
                           old-size
                           val))))

(defthm bvsx-unguarded-correct
  (equal (bvsx-unguarded new-size old-size val)
         (bvsx new-size old-size val))
  :hints (("Goal" :in-theory (enable bvsx bvsx-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvshl-unguarded (width x shift-amount)
  (declare (xargs :guard t))
  (let ((shift-amount (nfix shift-amount)))
    (bvcat-unguarded (- (nfix width) shift-amount) x shift-amount 0)))

(defthm bvshl-unguarded-correct
  (equal (bvshl-unguarded width x shift-amount)
         (bvshl width x shift-amount))
  :hints (("Goal" :in-theory (enable bvshl bvshl-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvshr-unguarded (width x shift-amount)
  (declare (xargs :guard t))
  (let ((shift-amount (nfix shift-amount)))
    (slice-unguarded (+ -1 (nfix width)) shift-amount x)))

(defthm bvshr-unguarded-correct
  (equal (bvshr-unguarded width x shift-amount)
         (bvshr width x shift-amount))
  :hints (("Goal" :in-theory (enable bvshr bvshr-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvashr-unguarded (width x shift-amount)
  (declare (xargs :guard t))
  (bvsx-unguarded width
                  (- (fix width) (fix shift-amount))
                  (bvshr-unguarded width x shift-amount)))

(defthm bvashr-unguarded-correct
  (equal (bvashr-unguarded width x shift-amount)
         (bvashr width x shift-amount))
  :hints (("Goal" :in-theory (enable bvashr bvashr-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund ceiling-of-lg-unguarded (x)
  (declare (xargs :guard t))
  (if (integerp x)
      (ceiling-of-lg x)
    0))

(defthm ceiling-of-lg-unguarded-correct
  (equal (ceiling-of-lg-unguarded x)
         (ceiling-of-lg x))
  :hints (("Goal" :cases ((acl2-numberp x))
           :in-theory (enable ceiling-of-lg ceiling-of-lg-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logext-unguarded (size i)
  (declare (xargs :guard t))
  (if (integerp size)
      (if (not (posp size))
          ;; unusual case:
          (if (equal (getbit 0 (ifix i)) 0) 0 -1)
        ;; usual case:
        (logext size (ifix i)))
    (if (not (acl2-numberp size))
        ;; unusual case:
        (if (equal (getbit 0 (ifix i)) 0) 0 -1)
      ;; unusual case:
      (if (equal 0 (if (integerp i) (getbit 0 i) 0)) 0 -1))))

(defthm logext-unguarded-correct
  (equal (logext-unguarded size i)
         (logext size i))
  :hints (("Goal" :in-theory (enable logext logext-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sbvdiv-unguarded (n x y)
  (declare (xargs :guard t))
  (bvchop-unguarded n (truncate-unguarded (logext-unguarded n x) (logext-unguarded n y))))

(defthm sbvdiv-unguarded-correct
  (equal (sbvdiv-unguarded size x y)
         (sbvdiv size x y))
  :hints (("Goal" :in-theory (enable sbvdiv sbvdiv-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund firstn-unguarded (n lst)
  (declare (xargs :guard t))
  (if (true-listp lst)
      (firstn (nfix n) lst)
    (firstn (nfix n) (true-list-fix lst))))

(defthm firstn-unguarded-correct
  (equal (firstn-unguarded n lst)
         (firstn n lst))
  :hints (("Goal" :in-theory (enable firstn-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logapp-unguarded (size i j)
  (declare (xargs :guard t))
  (logapp (nfix size) (ifix i) (ifix j)))

(defthm logapp-unguarded-correct
  (equal (logapp-unguarded size i j)
         (logapp size i j))
  :hints (("Goal" :in-theory (enable logapp-unguarded logapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund every-nth-unguarded (n vals)
  (declare (xargs :guard t))
  (if (not (posp n)) ; for termination
      nil
    (let ((vals (true-list-fix vals)))
      (every-nth-exec n vals))))

(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(local
  (defthm every-nth-of-true-list-fix
    (equal (every-nth n (true-list-fix vals))
           (every-nth n vals))
    :hints (("Goal" :expand (every-nth n (true-list-fix vals))
             :induct t
             :in-theory (enable every-nth)))))

(defthm every-nth-unguarded-correct
  (equal (every-nth-unguarded n vals)
         (every-nth n vals))
  :hints (("Goal" :in-theory (enable every-nth-unguarded
                                     every-nth
                                     every-nth-exec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund negated-elems-listp-unguarded (width lst1 lst2)
  (declare (xargs :guard t))
  (negated-elems-listp (nfix width) lst1 lst2))

(defthm negated-elems-listp-unguarded-correct
  (equal (negated-elems-listp-unguarded width lst1 lst2)
         (negated-elems-listp width lst1 lst2))
  :hints (("Goal" :in-theory (enable negated-elems-listp-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund all-equal$-unguarded (x lst)
  (declare (xargs :guard t))
  (if (not (consp lst))
      t
    (and (equal x (first lst))
         (all-equal$-unguarded x (rest lst)))))

(defthm all-equal$-unguarded-correct
  (equal (all-equal$-unguarded x lst)
         (all-equal$ x lst))
  :hints (("Goal" :in-theory (enable all-equal$-unguarded all-equal$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund packbv-unguarded (itemcount itemsize items)
  (declare (xargs :guard t))
  (if (zp (nfix itemcount))
      0
    (bvcat-unguarded itemsize (ifix (car-unguarded items))
                           (* (fix itemsize) (fix (+ -1 (fix itemcount))))
                           (packbv-unguarded (+ -1 (fix itemcount))
                                                   itemsize (cdr-unguarded items)))))

(defthm packbv-unguarded-correct
  (equal (packbv-unguarded itemcount itemsize items)
         (packbv itemcount itemsize items))
  :hints (("Goal" :in-theory (enable packbv-unguarded
                                     packbv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bit-to-bool-unguarded (x)
  (declare (xargs :guard t))
  (if (eql x 0) nil t))

(defthm bit-to-bool-unguarded-correct
  (equal (bit-to-bool-unguarded x)
         (bit-to-bool x))
  :hints (("Goal" :in-theory (enable bit-to-bool-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bool-to-bit-unguarded (test)
  (declare (xargs :guard t))
  (if test 1 0))

(defthm bool-to-bit-unguarded-correct
  (equal (bool-to-bit-unguarded x)
         (bool-to-bit x))
  :hints (("Goal" :in-theory (enable bool-to-bit-unguarded bool-to-bit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bvchop-list-unguarded-exec (size lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (cons (bvchop-unguarded size (car lst))
          (bvchop-list-unguarded-exec size (cdr lst)))))

(defund bvchop-list-unguarded (size lst)
  (declare (xargs :guard t))
  (if (unsigned-byte-listp size lst)
      lst
    (bvchop-list-unguarded-exec size lst)))

(defthm bvchop-list-unguarded-correct
  (equal (bvchop-list-unguarded size lst)
         (bvchop-list size lst))
  :hints (("Goal" :in-theory (enable bvchop-list-unguarded
                                     bvchop-list-unguarded-exec
                                     bvchop-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund getbit-list-unguarded (n lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (cons (getbit-unguarded n (car lst))
          (getbit-list-unguarded n (cdr lst)))))

(defthm getbit-list-unguarded-correct
  (equal (getbit-list-unguarded size lst)
         (getbit-list size lst))
  :hints (("Goal" :in-theory (enable getbit-list-unguarded
                                     getbit-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun subrange-unguarded (start end lst)
  (declare (xargs :guard t))
  (nthcdr-unguarded start (take-unguarded (binary-+-unguarded 1 end) lst)))

(defthm subrange-unguarded-correct
  (equal (subrange-unguarded start end lst)
         (subrange start end lst))
  :hints (("Goal" :in-theory (enable subrange-unguarded
                                     subrange))))
