; A library for reasoning about ACL2 arrays (aref1, aset1, etc.)
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

(include-book "kestrel/lists-light/reverse-list" :dir :system) ;make local?
(include-book "bounded-nat-alists")
(include-book "alen1")
(include-book "aref1")
(include-book "aset1")
(include-book "default")
(include-book "header")
(include-book "array1p")
(include-book "bounded-integer-alistp")
(include-book "dimensions") ; make local?
(include-book "compress1") ; make local?
(include-book "compress11") ; make local?
(include-book "maximum-length") ; make local?
(include-book "make-empty-array")
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/utilities/assoc-keyword" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; We disable functions about arrays, because this book introduces rules about
;; them:
(in-theory (disable dimensions
                    header
                    default
                    maximum-length
                    array1p
                    aset1
                    aref1
                    compress1
                    compress11
                    bounded-integer-alistp
                    array-order))

(local (in-theory (disable true-listp
                           assoc-keyword)))

;;;
;;; Normalize names (most of these functions ignore the name param)
;;;

(local (in-theory (enable normalize-alen1-name
                          normalize-header-name
                          normalize-default-name
                          normalize-maximum-length-name
                          normalize-dimensions-name
                          normalize-compress11-name
                          normalize-compress1-name
                          normalize-aref1-name
                          normalize-aset1-name)))

(defthmd normalize-compress211-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress211 name l i x j default)
                  (compress211 :fake-name l i x j default)))
  :hints (("Goal" :in-theory (enable compress211))))

(local (in-theory (enable normalize-compress211-name)))

(defthmd normalize-compress21-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress21 name l n i j default)
                  (compress21 :fake-name l n i j default)))
  :hints (("Goal" :in-theory (enable compress21))))

(local (in-theory (enable normalize-compress21-name)))

(defthmd normalize-compress2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress2 name l)
                  (compress2 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress2))))

(local (in-theory (enable normalize-compress2-name)))

(defthmd normalize-aset2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aset2 name l i j val)
                  (aset2 :fake-name l i j val)))
  :hints (("Goal" :in-theory (enable aset2))))

;; (local (in-theory (enable normalize-aset2-name)))

(defthmd normalize-aref2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref2 name l i j)
                  (aref2 :fake-name l i j)))
  :hints (("Goal" :in-theory (enable aref2))))

;; (local (in-theory (enable normalize-aref2-name)))

(local (in-theory (enable normalize-array1p-name)))

(defthmd normalize-array2p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array2p name l)
                  (and (symbolp name)
                       (array2p :fake-name l))))
  :hints (("Goal" :in-theory (enable array2p))))

;; (local (in-theory (enable normalize-array2p-name)))

;; The -1 is here because array1p requries the length to be strictly less than
;; the :MAXIMUM-LENGTH (why?), and the :MAXIMUM-LENGTH is at most
;; *maximum-positive-32-bit-integer* .
(defconst *maximum-1-d-array-length* (+ -1 *maximum-positive-32-bit-integer*))

(local
  (defthm alistp-of-reverse-list
    (equal (alistp (reverse-list x))
           (alistp (true-list-fix x)))
    :hints (("Goal" :in-theory (enable alistp reverse-list)))))

;; (defthm alistp-of-reverse-list
;;   (implies (alistp x)
;;            (alistp (reverse-list x)))
;;   :hints (("Goal" :in-theory (enable reverse-list))))

(local
  (defthm assoc-equal-of-reverse-list-iff
    (implies (or (alistp x)
                 key)
             (iff (assoc-equal key (reverse-list x))
                  (assoc-equal key x)))
    :hints (("Goal" :in-theory (enable reverse-list)))))

(local (in-theory (enable revappend-becomes-append-of-reverse-list)))

;use list fix in concl?
(defthm bounded-integer-alistp-of-reverse-list
  (implies (true-listp x)
           (equal (bounded-integer-alistp (reverse-list x) n)
                  (bounded-integer-alistp x n)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp reverse-list))))

(defthmd assoc-equal-when-assoc-equal-of-reverse-list
  (implies (and (assoc-equal key (reverse-list alist))
                (alistp alist))
           (assoc-equal key alist))
  :hints (("Goal" :in-theory (enable assoc-equal reverse-list))))

;; ;might be better to strip the keys and call NO-DUPLICATESP?
(defun myduplicate-keysp (alist)
  (cond ((endp alist) nil)
        ((assoc-equal (caar alist) (cdr alist))
         t)
        (t (myduplicate-keysp (cdr alist)))))

(defthm assoc-equal-of-reverse-list
  (implies (and (not (myduplicate-keysp alist))
                (alistp alist))
           (equal (assoc-equal key (reverse-list alist))
                  (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable assoc-equal reverse-list
                                     assoc-equal-when-assoc-equal-of-reverse-list))))


;; ;can be expensive?
;; (defthmd consp-when-true-listp-and-non-nil
;;   (implies (and x ;limit?
;;                 (true-listp x))
;;            (consp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm natp-of-car-of-assoc-equal
;;   (equal (natp (car (assoc-equal :header array)))
;;          nil)
;;   :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm not-of-myduplicate-keysp-of-compress11
  (not (myduplicate-keysp (compress11 name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

;; (in-theory (disable (:i assoc-equal)))

;move this and all the supporting stuff above!
(defthm aref1-of-aset1-same
  (implies (and (array1p array-name array) ;;(alistp array)
                (natp index)
                (< index (alen1 array-name array))
                )
           (equal (aref1 array-name (aset1 array-name2 array index val) index)
                  val))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   ;compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-diff
  (implies (and (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                ;; (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name array index1 val) index2)
                  (aref1 array-name array index2)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-both
  (implies (and (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name array index1 val) index2)
                  (if (equal index1 index2)
                      val
                    (aref1 array-name array index2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Not quite true...
;; (defthm aset1-of-aset1-same
;;   (implies (and (array1p array-name array)
;;                 (natp index)
;;                 (< index (alen1 array-name array)))
;;            (equal (aset1 array-name (aset1 array-name array index val1) index val2)
;;                   (aset1 array-name array index val2)))
;;   :hints (("Goal" :in-theory (e/d (array1p-rewrite
;;                                    compress1
;;                                    header
;;                                    default
;;                                    aset1
;;                                    dimensions
;;                                    alen1)
;;                                   (dimensions-intro
;;                                    alen1-intro
;;                                    alen1-intro2)))))

;; A simple theorem like aset1-of-aset1-same would not be true
(defthm aref1-of-aset1-of-aset1-same
  (implies (and (array1p array-name array)
                (natp index)
                ;; (< index (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index val1) index val2) read-index)
                  (aref1 array-name (aset1 array-name array index val2) read-index)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-of-aset1-same-diff
  (implies (and (syntaxp (smaller-termp index2 index1))
                (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index1 val1) index2 val2) read-index)
                  (aref1 array-name (aset1 array-name (aset1 array-name array index2 val2) index1 val1) read-index)))
  :hints (("Goal" :in-theory (e/d (aref1
                                   array1p-rewrite
                                   compress1
                                   header
                                   default
                                   aset1
                                   dimensions
                                   alen1)
                                  (dimensions-intro
                                   default-intro
                                   alen1-intro
                                   alen1-intro2)))))

(defthm aref1-of-aset1-of-aset1-same-both
  (implies (and (syntaxp (smaller-termp index2 index1)) ;prevent loops
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
                (natp index2)
                (< index2 (alen1 array-name array))
                (natp read-index)
                (< read-index (alen1 array-name array)))
           (equal (aref1 array-name (aset1 array-name (aset1 array-name array index1 val1) index2 val2) read-index)
                  (if (equal index1 index2)
                      (aref1 array-name (aset1 array-name array index2 val2) read-index)
                    (aref1 array-name (aset1 array-name (aset1 array-name array index2 val2) index1 val1) read-index)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Copies the values at locations INDEX down to 0 from FROM-ARRAY to the same
;; locations in TO-ARRAY.  Requires that the arrays be big enough for INDEX to
;; be a valid index.  NOTE: when copying a whole array, consider calling
;; compress1 for speed?
(defund copy-array-vals (index from-array-name from-array to-array-name to-array)
  (declare (xargs :measure (nfix (+ 1 index))
                  :guard (and (rationalp index)
                              (array1p from-array-name from-array)
                              (array1p to-array-name to-array)
                              (< index (alen1 from-array-name from-array))
                              (< index (alen1 to-array-name to-array)))))
  (if (not (natp index))
      to-array
    (let ((to-array (aset1 to-array-name to-array index (aref1 from-array-name from-array index))))
      (copy-array-vals (+ -1 index) from-array-name from-array to-array-name to-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun print-array-vals (high-index low-index array-name array)
  (declare (xargs :measure (+ 1 (nfix (- (+ 1 high-index) low-index)))
                  :guard (and (symbolp array-name)
                              (integerp high-index)
                              (array1p array-name array)
                              (< high-index (alen1 array-name array)))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  )
           (type (integer 0 *) low-index))
  (if (or (< high-index low-index)
          (not (natp low-index))
          (not (natp high-index)))
      nil
    (print-array-vals (prog2$ (cw " ~y0"
                                  (cons high-index (aref1 array-name array high-index)) ;save this cons?
                                  )
                              (+ -1 high-index))
                      low-index
                      array-name
                      array)))


;fixme whitespace before and/or after isn't quite right
;does this do the right thing for very small arrays?
;prints the low elems-to-print elements
(defun print-array2 (array-name array elem-count-to-print)
  (declare (type (integer 0 *) elem-count-to-print)
           (xargs :guard (implies (not (eql 0 elem-count-to-print))
                                  (and (symbolp array-name)
                                       (array1p array-name array)
                                       (<= elem-count-to-print (alen1 array-name array))))
                  :guard-hints (("Goal" :in-theory (enable ARRAY1P-rewrite)))))
  (prog2$
   ;;print the open paren:
   (cw "(")
   (prog2$
    ;;print the elements
    (if (eql 0 elem-count-to-print)
        nil
      (if (equal 1 elem-count-to-print)
          (cw "~x0" (cons 0 (aref1 array-name array 0)))
        (prog2$ (cw "~y0" (cons (+ -1 elem-count-to-print) (aref1 array-name array (+ -1 elem-count-to-print)))) ;can we skip the conses?
                (prog2$ (print-array-vals (+ -2 elem-count-to-print) 1 array-name array)
                        (cw " ~x0" (cons 0 (aref1 array-name array 0))) ;no newline
                        ))))
    ;;print the close paren:
    (cw ")~%"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:executable-counterpart break$))) ;keeps it from breaking when it's evaluated during a proof, e.g., proofs about aset1-safe

;this makes sure the index is in bounds, which prevents memory from getting trashed if this is called on bad arguments
(defund aset1-safe (name l n val)
  (declare (xargs :guard (and (array1p name l)
                              (integerp n)
                              (>= n 0)
                              (< n (alen1 name l)))))
  (if (< n (alen1 name l))
      (aset1 name l n val)
    (progn$ ;(print-list l)
            (cw "Bad index, ~x0, for array ~x1 with len ~x2." n name (alen1 name l))
            (break$) ;(car 7) ;this causes a crash and is better than a hard-error since it puts us into the debugger.
            ;;aset1-safe is logically just aset1
            (aset1 name l n val))))

(defthm aset1-safe-becomes-aset1
  (implies t ;(< n (alen1 name l))
           (equal (aset1-safe name l n val)
                  (aset1 name l n val)))
  :hints (("Goal" :in-theory (enable aset1-safe))))
