; A library for reasoning about ACL2 arrays (aref1, aset1, etc.)
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

(include-book "kestrel/lists-light/reverse-list" :dir :system) ;make local?
(include-book "bounded-nat-alists")
(include-book "alen1")
(include-book "aset1")
(include-book "default")
(include-book "header")
(include-book "bounded-integer-alistp")
(include-book "dimensions") ; make local?
(include-book "compress1") ; make local?
(include-book "compress11") ; make local?
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
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
                    bounded-integer-alistp))

(in-theory (disable array1p-linear)) ; does not reflect our normal form

(local (in-theory (disable true-listp
                           assoc-keyword)))

;;;
;;; Normalize names (most of these functions ignore the name param)
;;;

(local (in-theory (enable normalize-alen1-name)))

(defthmd normalize-header-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (header name l)
                  (header :fake-name l)))
  :hints (("Goal" :in-theory (enable header))))

(local (in-theory (enable normalize-header-name)))

(defthmd normalize-default-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (default name l)
                  (default :fake-name l)))
  :hints (("Goal" :in-theory (e/d (default) (default-intro)))))

(local (in-theory (enable normalize-default-name)))

(defthmd normalize-maximum-length-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (maximum-length name l)
                  (maximum-length :fake-name l)))
  :hints (("Goal" :in-theory (enable maximum-length))))

(local (in-theory (enable normalize-maximum-length-name)))

(defthmd normalize-dimensions-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (dimensions name l)
                  (dimensions :fake-name l)))
  :hints (("Goal" :in-theory (e/d (dimensions) (dimensions-intro)))))

(local (in-theory (enable normalize-dimensions-name)))

(defthmd normalize-compress11-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress11 name l i n default)
                  (compress11 :fake-name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(local (in-theory (enable normalize-compress11-name)))

(defthmd normalize-compress1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress1 name l)
                  (compress1 :fake-name l)))
  :hints (("Goal" :in-theory (enable compress1))))

(local (in-theory (enable normalize-compress1-name)))

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

(defthmd normalize-aref1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref1 name l n)
                  (aref1 :fake-name l n)))
  :hints (("Goal" :in-theory (enable aref1))))

(local (in-theory (enable normalize-aref1-name)))

(defthmd normalize-aset1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aset1 name l n val)
                  (aset1 :fake-name l n val)))
  :hints (("Goal" :in-theory (enable aset1))))

(local (in-theory (enable normalize-aset1-name)))

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

(defthmd normalize-array1p-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (array1p name l)
                  (and (symbolp name)
                       (array1p :fake-name l))))
  :hints (("Goal" :in-theory (enable array1p))))

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

;; This is perhaps how array1p should be defined (but see the comment about
;; array1p in the ACL2 sources).
(defthmd array1p-rewrite
  (equal (array1p name l)
         (and
          (symbolp name)
          (alistp l)
          (let
              ((header-keyword-list (cdr (header name l))))
            (and
             (keyword-value-listp header-keyword-list)
             (let* ((dimensions (dimensions name l))
                    (len (car dimensions))
                    (maximum-length (maximum-length name l)))
               (and (true-listp dimensions)
                    (equal (len dimensions) 1)
                    (integerp len)
                    (integerp maximum-length)
                    (< 0 len)
                    (< len maximum-length)
                    (<= maximum-length *maximum-positive-32-bit-integer*)
                    (bounded-integer-alistp l len)))))))
  :hints (("Goal" :in-theory (e/d (array1p header dimensions maximum-length)
                                  (dimensions-intro)))))

;; Here we also introduce alen1
(defthmd array1p-rewrite2
  (equal (array1p name l)
         (and
          (symbolp name)
          (alistp l)
          (let
              ((header-keyword-list (cdr (header name l))))
            (and
             (keyword-value-listp header-keyword-list)
             (let* ((dimensions (dimensions name l))
                    (len (alen1 name l))
                    (maximum-length (maximum-length name l)))
               (and (true-listp dimensions)
                    (equal (len dimensions) 1)
                    (integerp len)
                    (integerp maximum-length)
                    (< 0 len)
                    (< len maximum-length)
                    (<= maximum-length *maximum-positive-32-bit-integer*)
                    (bounded-integer-alistp l len)))))))
  :hints (("Goal" :in-theory (e/d (array1p-rewrite)
                                  ()))))

(defthm alistp-of-reverse-list
  (equal (alistp (reverse-list x))
         (alistp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable alistp reverse-list))))

;; (defthm alistp-of-reverse-list
;;   (implies (alistp x)
;;            (alistp (reverse-list x)))
;;   :hints (("Goal" :in-theory (enable reverse-list))))

(defthm maximum-length-of-cons
  (equal (maximum-length name (cons a x))
         (if (equal :header (car a))
             (cadr (assoc-keyword :maximum-length (cdr a)))
           (maximum-length name x)))
  :hints (("Goal" :in-theory (enable maximum-length header))))

(defthm assoc-equal-of-reverse-list-iff
  (implies (or (alistp x)
               key)
           (iff (assoc-equal key (reverse-list x))
                (assoc-equal key x)))
  :hints (("Goal" :in-theory (enable reverse-list))))

(local (in-theory (enable revappend-lemma)))

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

;might be better to strip the keys and call NO-DUPLICATESP?
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


;can be expensive?
(defthmd consp-when-true-listp-and-non-nil
  (implies (and x ;limit?
                (true-listp x))
           (consp x)))

(defthm alen1-of-aset1
  (equal (alen1 array-name (aset1 array-name array n val))
         (if (eq :header n)
             (car (cadr (assoc-keyword :dimensions val)))
           (alen1 array-name array)))
  :hints (("Goal" :in-theory (e/d (alen1)
                                  (alen1-intro alen1-intro2)))))

(in-theory (disable array-order)) ; move

(defthm array1p-of-aset1
  (implies (and (natp index)
                (< index (alen1 array-name array))
                (array1p array-name array))
           (array1p array-name (aset1 array-name array index val)))
  :hints (("Goal" :in-theory (e/d (aset1 array1p-rewrite2 dimensions ALEN1 maximum-length)
                                  (dimensions-intro
                                   alen1-intro
                                   alen1-intro2)))))

;; Make an array where every element is the default.
;; TODO: Rename this, since "empty" here doesn't mean an array of length 0 but rather that the alist is empty.
;according to array1p, the maximum-length field of an array can be at most *maximum-positive-32-bit-integer* = 2147483647
;and the length (first dimension) of the array is at most 2147483646 since it must be strictly smaller than the :maximum-length (why strictly?)
;; Note that array1p disallows arrays of size 0 (why?), so this function does also.
(defund make-empty-array-with-default (name size default)
  (declare (type symbol name)
           (type (integer 1 2147483646) size)
           (xargs :guard-hints (("Goal" :in-theory (enable array1p)))))
  (compress1 name
             (acons-fast :header (list :dimensions (list size)
                                       ;;ffixme think about this:
                                       :maximum-length (min (* 2 size) *maximum-positive-32-bit-integer* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                            )
                                       :default default
                                       ;; no :order given here means the order is effectively <
                                       :name name ;; could perhaps omit this
                                       )
                         nil)))

(in-theory (disable (:e make-empty-array-with-default))) ;; Avoid making arrays during proofs (might be huge)

(defthm default-of-make-empty-array-with-default
  (equal (default dag-parent-array-name (make-empty-array-with-default dag-parent-array-name size default))
         default)
  :hints (("Goal" :in-theory (e/d (make-empty-array-with-default default) (default-intro)))))

;; Make an array with SIZE elements (and name NAME), where every index has the value nil.
(defund make-empty-array (name size)
  (declare (type symbol name)
           (type (integer 1 2147483646) size)
           (xargs :guard-hints (("Goal" :in-theory (enable array1p len)))))
  (make-empty-array-with-default name size nil))

(in-theory (disable (:e make-empty-array))) ;; Avoid exposing a constant involving a :header

(defthm default-of-make-empty-array
  (equal (default dag-parent-array-name (make-empty-array dag-parent-array-name size))
         nil)
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm array1p-of-make-empty-array-with-default
  (equal (array1p array-name (make-empty-array-with-default array-name len default))
         (and (posp len)
              (<= len 2147483646)
              (symbolp array-name)))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm array1p-of-make-empty-array
  (equal (array1p array-name (make-empty-array array-name len))
         (and (posp len)
              (<= len 2147483646)
              (symbolp array-name)))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm dimensions-of-make-empty-array-with-default
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (dimensions array-name (make-empty-array-with-default array-name len default))
                  (list len)))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm alen1-of-make-empty-array-with-default
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (alen1 array-name (make-empty-array-with-default array-name len default))
                  len))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm dimensions-of-make-empty-array
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (dimensions array-name (make-empty-array array-name len))
                  (list len)))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm alen1-of-make-empty-array
  (implies (and (posp len)
                (<= len 2147483646)
                (symbolp array-name))
           (equal (alen1 array-name (make-empty-array array-name len))
                  len))
  :hints (("Goal" :in-theory (enable make-empty-array))))

;requires that the arrays must be big enough for max-index to be a valid index
;when copying a whole array, consider calling compress1 for speed?
(defun copy-array-vals (max-index from-array-name from-array to-array-name to-array)
  (declare (xargs :measure (nfix (+ 1 max-index))
                  :guard (and (rationalp max-index)
                              (array1p from-array-name from-array)
                              (array1p to-array-name to-array)
                              (< max-index (alen1 from-array-name from-array))
                              (< max-index (alen1 to-array-name to-array)))))
  (if (not (natp max-index))
      to-array
    (copy-array-vals (+ -1 max-index)
                     from-array-name
                     from-array
                     to-array-name
                     (aset1 to-array-name to-array max-index (aref1 from-array-name from-array max-index)))))

;; (defthm natp-of-car-of-assoc-equal
;;   (equal (natp (car (assoc-equal :header array)))
;;          nil)
;;   :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm not-of-myduplicate-keysp-of-compress11
  (not (myduplicate-keysp (compress11 name l i n default)))
  :hints (("Goal" :in-theory (enable compress11))))

(defthm assoc-equal-of-compress1
  (implies (and (natp index)
                ;; (< index (car (dimensions name l)))
                (array1p name l) ;name is mostly irrel here?
                )
           (equal (assoc-equal index (compress1 name l))
                  (if (and (equal (cdr (assoc-equal index l))
                                  (default name l))
                           (or (equal (array-order (assoc-equal :header l)) '>)
                               (equal (array-order (assoc-equal :header l)) '<)))
                      ;;if it's equal to the default and we are sorting, then it gets removed
                      nil
                    (assoc-equal index l))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (compress1 array1p-rewrite2
                                      header
                                      not-assoc-equal-when-bounded-integer-alistp-out-of-bounds
                                      )
                           (ASSOC-EQUAL array1p)))))

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

(defthm aref1-of-aset1-diff
  (implies (and (not (equal index1 index2))
                (array1p array-name array)
                (natp index1)
                (< index1 (alen1 array-name array))
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

;; (defthm assoc-equal-of-compress1
;;   (implies (and (natp index)
;; ;                (< index (car (dimensions name l)))
;;                 (array1p name l)
;;                 ;;fixme:
;;                 (or (equal '< (ARRAY-ORDER (HEADER NAME L)))
;;                     (equal '> (ARRAY-ORDER (HEADER NAME L)))))
;;            (equal (assoc-equal index (compress1 name l))
;;                   ;;improve this?
;;                   (if (equal (cdr (assoc-equal index l)) (default name l))
;;                       nil
;;                     (assoc-equal index l))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable compress1 array1p header dimensions
;;                               assoc-equal-when-bounded-integer-alistp-out-of-bounds))))

(defthm array1p-of-cons-header
  (equal (ARRAY1P NAME2 (CONS (LIST :HEADER
                                    :DIMENSIONS (LIST dim)
                                    :MAXIMUM-LENGTH max
                                    :DEFAULT NIL
                                    :NAME NAME)
                              ALIST))
         (and (bounded-integer-alistp alist dim)
              (posp dim)
              (< dim max)
              (symbolp name2)
              (<= MAX 2147483647)
              (integerp max)))
  :hints (("Goal" :in-theory (enable ARRAY1P-rewrite))))

(defthm aref1-of-make-empty-array-with-default
  (implies (and (symbolp array-name)
                (natp index) ;gen?
;                (< index len) ;we get nil if the index is out of bounds
		(posp len)
		(< len 2147483647)
                )
           (equal (aref1 array-name (make-empty-array-with-default array-name len default) index)
                  default))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              array-order
                              make-empty-array-with-default
                              aref1))))

(defthm aref1-of-make-empty-array
  (implies (and (symbolp array-name)
                (natp index) ;gen?
;                (< index len) ;we get nil if the index is out of bounds
		(posp len)
		(< len 2147483647)
                )
           (equal (aref1 array-name (make-empty-array array-name len) index)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              array-order
			      make-empty-array
                              aref1))))

(in-theory (disable (:executable-counterpart break$))) ;keeps it from breaking when it's evaluted during a proof, e.g., proofs about aset1-safe

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
  (implies (< n (alen1 name l))
           (equal (aset1-safe name l n val)
                  (aset1 name l n val)))
  :hints (("Goal" :in-theory (enable aset1-safe))))

;drop?
(defun valid-array-indexp (index array-name array)
  (declare (xargs :guard (array1p array-name array)))
  (and (natp index)
       (< index (alen1 array-name array))))

(defthmd not-assoc-equal-when-array1p-out-of-bounds
  (implies (and (<= (alen1 array-name array) index)
                (array1p array-name array)
                (natp index))
           (not (assoc-equal index array)))
  :hints (("Goal" :in-theory (e/d (not-assoc-equal-when-bounded-integer-alistp-out-of-bounds
                                   array1p-rewrite header)
                                  ()))))

;; Disabled since this can be expensive and is rarely needed.
(defthmd aref1-when-too-large
  (implies (and (<= (alen1 array-name array) n)
                (array1p array-name array)
                (natp n))
           (equal (aref1 array-name array n)
                  (default array-name array)))
  :hints (("Goal" :in-theory (e/d (AREF1 ARRAY1P-rewrite HEADER not-assoc-equal-when-bounded-integer-alistp-out-of-bounds)
                                  ()))))

(defthm aref1-when-too-large-cheap
  (implies (and (<= (alen1 array-name array) n)
                (array1p array-name array)
                (natp n))
           (equal (aref1 array-name array n)
                  (default array-name array)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable aref1-when-too-large))))

(local
 (defthm aref1-of-compress1-small
   (implies (and (< n (alen1 array-name array))
                 (natp n)
                 ;;(array1p array-name array)
                 (alistp array)
                 (integerp (ALEN1 ARRAY-NAME ARRAY))
                 )
            (equal (aref1 array-name (compress1 array-name2 array) n)
                   (aref1 array-name array n)))
   :hints (("Goal" :in-theory (e/d (aref1 compress1 header default) (default-intro))))))

(local
 (defthm aref1-of-compress1-too-large
   (implies (and (<= (alen1 array-name array) n)
                 (natp n)
                 (array1p array-name array) ; drop?
                 (alistp array)
                 ;;(integerp (ALEN1 ARRAY-NAME ARRAY))
                 )
            (equal (aref1 array-name (compress1 array-name2 array) n)
                   (default array-name array)))
   :hints (("Goal" :in-theory (e/d (default aref1-when-too-large aref1 compress1 header) (default-intro))))))

(defthm aref1-of-compress1
  (implies (and (natp n)
                (array1p array-name array))
           (equal (aref1 array-name (compress1 array-name2 array) n)
                  (if (< n (alen1 array-name array))
                      (aref1 array-name array n)
                    (default array-name array))))
  :hints (("Goal" :in-theory (e/d (aref1-when-too-large aref1 compress1 header default) (default-intro)))))

(defthm aref1-of-cons-of-cons-of-header
  (implies (natp n)
           (equal (aref1 array-name (cons (cons :header header) alist) n)
                  (if (assoc-equal n alist)
                      (aref1 array-name alist n)
                    (cadr (assoc-keyword :default header)))))
  :hints (("Goal" :in-theory (enable aref1 header))))

;; This one has no IF in the RHS
(defthm aref1-of-cons-of-cons-of-header-alt
  (implies (and (natp n)
                (equal (default array-name array)
                       (cadr (assoc-keyword :default header-args))))
           (equal (aref1 array-name (cons (cons :header header-args) array) n)
                  (aref1 array-name array n)))
  :hints (("Goal" :in-theory (enable aref1 header))))

(defthmd aref1-when-not-assoc-equal
  (implies (not (assoc-equal n alist))
           (equal (aref1 array-name alist n)
                  (default array-name alist)))
  :hints (("Goal" :in-theory (enable aref1))))

;; (defthm assoc-equal-of-header-of-compress1
;;   (equal (assoc-equal :header (compress1 array-name array))
;;          (assoc-equal :header array))
;;   :hints (("Goal" :in-theory (e/d (compress1) ()))))

(defthm array1p-forward-to-<=-of-alen1
  (implies (array1p array-name array)
           (<= (alen1 array-name array)
               2147483646))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm array1p-forward-to-<=-of-alen1-2
  (implies (array1p array-name array)
           (<= 1 (alen1 array-name array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array1p-rewrite))))

(defthm dimensions-when-not-consp-of-header-cheap
  (implies (not (consp (header name l)))
           (equal (dimensions name l)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (dimensions) (dimensions-intro)))))

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
                (< index (alen1 array-name array))
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

(defthm array1p-of-cons-of-header-and-nil
  (equal (array1p array-name
                  (list (list :header
                              :dimensions dims
                              :maximum-length maximum-length
                              :default default
                              :name array-name)))
         (and (symbolp array-name)
              (equal 1 (len dims))
              (true-listp dims)
              (posp (car dims))
              (natp maximum-length)
              (< (car dims) maximum-length)
              (<= maximum-length 2147483647)))
  :hints (("Goal" :in-theory (enable array1p-rewrite))))
