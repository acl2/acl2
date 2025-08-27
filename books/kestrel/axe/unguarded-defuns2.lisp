; More unguarded defuns (not used in evaluator-basic)
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

(include-book "unguarded-defuns")
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(local (include-book "kestrel/bv/bitops" :dir :system))
;(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund integer-range-p-unguarded (lower upper x)
  (declare (xargs :guard t))
  (and (integerp x)
       (not (<-unguarded x lower))
       (<-unguarded x upper)))

(defthm integer-range-p-unguarded-correct
  (equal (integer-range-p-unguarded lower upper x)
         (integer-range-p lower upper x))
  :hints (("Goal" :in-theory (enable integer-range-p-unguarded
                                     integer-range-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund loghead$inline-unguarded (n x)
  (declare (xargs :guard t))
  (loghead$inline (nfix n) (ifix x)))

(defthm loghead$inline-unguarded-correct
  (equal (loghead$inline-unguarded n x)
         (loghead$inline n x))
  :hints (("Goal" :in-theory (enable loghead$inline-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logbitp-unguarded (i j)
  (declare (xargs :guard t))
  (logbitp (nfix i) (ifix j)))

(defthm logbitp-unguarded-correct
  (equal (logbitp-unguarded i j)
         (logbitp i j))
  :hints (("Goal" :in-theory (enable logbitp-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-logand-unguarded (i j)
  (declare (xargs :guard t))
  (binary-logand (ifix i) (ifix j)))

(defthm binary-logand-unguarded-correct
  (equal (binary-logand-unguarded i j)
         (binary-logand i j))
  :hints (("Goal" :in-theory (enable binary-logand-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-logior-unguarded (i j)
  (declare (xargs :guard t))
  (binary-logior (ifix i) (ifix j)))

(defthm binary-logior-unguarded-correct
  (equal (binary-logior-unguarded i j)
         (binary-logior i j))
  :hints (("Goal" :in-theory (enable binary-logior-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bitops::part-select-width-low$inline-unguarded (x width low)
  (declare (xargs :guard t))
  (loghead$inline-unguarded width (logtail$inline-unguarded low x)))

(defthm bitops::part-select-width-low$inline-unguarded-correct
  (equal (bitops::part-select-width-low$inline-unguarded x width low)
         (bitops::part-select-width-low$inline x width low))
  :hints (("Goal" :in-theory (enable bitops::part-select-width-low$inline-unguarded bitops::part-select-width-low$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund zip-unguarded (x)
  (declare (xargs :guard t))
  (zip (ifix x)))

(defthm zip-unguarded-correct
  (equal (zip-unguarded x)
         (zip x))
  :hints (("Goal" :in-theory (enable zip-unguarded zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund evenp-unguarded (x)
  (declare (xargs :guard t ))
  (integerp (binary-*-unguarded x (unary-/-unguarded 2))))

(defthm evenp-unguarded-correct
  (equal (evenp-unguarded x)
         (evenp x))
  :hints (("Goal" :in-theory (enable evenp-unguarded evenp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund logcount-unguarded (x)
  (declare (xargs :guard t ))
  (logcount (ifix x)))

(defthm logcount-unguarded-correct
  (equal (logcount-unguarded x)
         (logcount x))
  :hints (("Goal" :in-theory (enable logcount-unguarded logcount))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund ash-unguarded (i c)
  (declare (xargs :guard t ))
  (ash (ifix i) (ifix c)))

(defthm ash-unguarded-correct
  (equal (ash-unguarded i c)
         (ash i c))
  :hints (("Goal" :in-theory (enable ash-unguarded ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::assoc-keyword-unguarded (key l)
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((equal key (car l)) l)
        (t (assoc-keyword-unguarded key (acl2::cdr-unguarded (acl2::cdr-unguarded l))))))

(defthm assoc-keyword-unguarded-correct
  (equal (acl2::assoc-keyword-unguarded key l)
         (assoc-keyword key l))
  :hints (("Goal" :in-theory (enable acl2::assoc-keyword-unguarded))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::header-unguarded (name l)
  (declare (xargs :guard t))
  (if (or (array1p name l)
          (array2p name l))
      (header name l)
    ;; todo: make an assoc-eq-unguarded:
    (acl2::assoc-equal-unguarded :header l)))

(defthm header-unguarded-correct
  (equal (acl2::header-unguarded name l)
         (acl2::header name l))
  :hints (("Goal" :in-theory (enable acl2::header-unguarded acl2::header))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::default-unguarded (name l)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable dimensions default)))))
  (if (or (array1p name l)
          (array2p name l))
      ;; normal case:
      (cadr (assoc-keyword :default (cdr (header name l))))
    (acl2::car-unguarded (acl2::cdr-unguarded (acl2::assoc-keyword-unguarded :default (acl2::cdr-unguarded (acl2::header-unguarded name l)))))))

(defthm default-unguarded-correct
  (equal (acl2::default-unguarded name l)
         (acl2::default name l))
  :hints (("Goal" :in-theory (enable acl2::default-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I hope this is still fast in the normal case.
;; TOOD: For some reason, I am seeing slow array warnings.
(defund acl2::aref1-unguarded (name l n)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable array1p header dimensions default)))))
  (if (and (symbolp name)
           (array1p name l)
           (natp n)
           (let ((dims (dimensions name l)))
             (and (consp dims)
                  (let ((len (car dims)))
                    (and (natp len)
                         (< n len))))))
      ;; hope this is fast:
      (aref1 name l n)
    (let ((x (and (not (eq n :header))
                  (acl2::assoc-equal-unguarded n l))))
      (cond ((null x) (acl2::default-unguarded name l))
            (t (acl2::cdr-unguarded x))))))

(defthm aref1-unguarded-correct
  (equal (acl2::aref1-unguarded name l n)
         (acl2::aref1 name l n))
  :hints (("Goal" :in-theory (enable acl2::aref1-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bv-array-read-chunk-little-unguarded (element-count element-size array-len index array)
  (declare (xargs :guard t))
  (if (zp-unguarded element-count)
      0
    (bvcat-unguarded (binary-*-unguarded element-size (binary-+-unguarded -1 element-count))
                     (bv-array-read-chunk-little-unguarded (binary-+-unguarded -1 element-count) element-size array-len (binary-+-unguarded 1 index) array)
                     element-size
                     (bv-array-read-unguarded element-size array-len index array))))

(defthm bv-array-read-chunk-little-unguarded-correct
  (equal (bv-array-read-chunk-little-unguarded element-count element-size array-len index array)
         (bv-array-read-chunk-little element-count element-size array-len index array))
  :hints (("Goal" :in-theory (enable bv-array-read-chunk-little-unguarded
                                     bv-array-read-chunk-little))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
