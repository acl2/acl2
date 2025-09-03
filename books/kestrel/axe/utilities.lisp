; Utilities for stating claims to be proved by Axe
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

;; TODO: Give this book a better name

(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/utilities/make-cons-nest" :dir :system)
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; TODO: For these functions, should the count or the base name come first?  Be consistent.
;; TODO: When creating numbered vars consider using 00, 01, etc. instead of 0, 1, etc (assuming 2 digit numbers).

;; Make a symbolic list term (a cons nest) containing the variables <base-name>0
;; through <base-name>(len-1).  Can be useful when unrolling specs.
;; rename symbolic-var-list?
(defund symbolic-list (base-name len)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp len))))
  (make-cons-nest (make-var-names base-name len)))

(defthmd pseudo-termp-of-symbolic-list
  (pseudo-termp (symbolic-list base-name len))
  :hints (("Goal" :in-theory (enable symbolic-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A version of symbolic-list that makes clear by its name that the vars are
;; intended to be bytes (that fact should actually get enforced by additional
;; assumptions).
(defund symbolic-byte-list (base-name len)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp len))))
  (symbolic-list base-name len))

(defthmd pseudo-termp-of-symbolic-byte-list
  (pseudo-termp (symbolic-byte-list base-name len))
  :hints (("Goal" :in-theory (enable symbolic-byte-list))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund symbolic-array-aux (current-index len element-size var-name)
  (declare (xargs :measure (nfix (+ 1 (- len current-index)))
                  :guard (and (natp current-index)
                              (natp len)
                              (posp element-size)
                              (symbolp var-name))))
  (if (or (<= len current-index)
          (not (natp len))
          (not (natp current-index)))
      (list 'quote (repeat len '0))
    `(bv-array-write ',element-size
                     ',len
                     ',current-index
                     ,(pack$ var-name (nat-to-string current-index))
                     ,(symbolic-array-aux (+ 1 current-index) len element-size var-name))))

(local
  (defthm pseudo-termp-of-symbolic-array-aux
    (implies (and (natp current-index)
                  (natp len)
                  (posp element-size)
                  (symbolp var-name))
             (pseudo-termp (symbolic-array-aux current-index len element-size var-name)))
    :hints (("Goal" :in-theory (enable symbolic-array-aux)))))

;; Makes a term representing a symbolic array of bit vector variables, named
;; BASE-NAME0 through BASE-NAME(length-1), each of ELEMENT-WIDTH bits.
(defund symbolic-array (base-name length element-width)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp length)
                              (posp element-width))))
  (symbolic-array-aux 0 length element-width base-name))

(defthm pseudo-term-listp-of-symbolic-array
  (implies (and (symbolp base-name)
                (natp length)
                (posp element-width))
           (pseudo-termp (symbolic-array base-name length element-width)))
  :hints (("Goal" :in-theory (enable symbolic-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;total-size should be (* item-size (len items)))
;we pass in total-size to avoid calling (len items) over and over
(defund bvcat-nest-for-items-aux (items item-size total-size)
  (declare (xargs :guard (and (true-listp items)
                              (<= 1 (len items))
                              (natp item-size)
                              (equal total-size (* item-size (len items))))))
  (if (endp items)
      (er hard? 'error-in-bvcat-nest-for-items-aux "Unexpected case: no items.")
    (if (endp (rest items))
        (first items)
      (let ((size-of-rest (- total-size item-size)))
        `(bvcat ',item-size
                ,(first items)
                ',size-of-rest
                ,(bvcat-nest-for-items-aux (rest items) item-size size-of-rest))))))

(defthm pseudo-termp-of-bvcat-nest-for-items-aux
  (implies (pseudo-term-listp items)
           (pseudo-termp (bvcat-nest-for-items-aux items item-size total-size)))
  :hints (("Goal" :in-theory (enable bvcat-nest-for-items-aux))))

;; The first item becomes the most significant part of the resulting term.
(defund bvcat-nest-for-items (items item-size)
  (declare (xargs :guard (and (true-listp items)
                              (<= 2 (len items))
                              (natp item-size))))
  (bvcat-nest-for-items-aux items item-size (* item-size (len items))))

(defthm pseudo-termp-of-bvcat-nest-for-items
  (implies (pseudo-term-listp items)
           (pseudo-termp (bvcat-nest-for-items items item-size)))
  :hints (("Goal" :in-theory (enable bvcat-nest-for-items))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bit-blasted-symbolic-array-aux (current-index len element-size var-name)
  (declare (xargs :measure (nfix (+ 1 (- len current-index)))
                  :guard (and (natp current-index)
                              (natp len)
                              (integerp element-size)
                              (<= 2 element-size) ; or else we don't need a bvcat for each element
                              (symbolp var-name))))
  (if (or (<= len current-index)
          (not (natp len))
          (not (natp current-index)))
      (list 'quote (repeat len '0))
    `(bv-array-write ',element-size
                     ',len
                     ',current-index
                     ,(bvcat-nest-for-items (reverse (make-var-names (pack$ var-name "_" current-index "_") element-size)) 1)
                     ,(bit-blasted-symbolic-array-aux (+ 1 current-index) len element-size var-name))))

(defthm pseudo-termp-of-bit-blasted-symbolic-array-aux
  (implies (and (natp current-index)
                (natp len)
                (posp element-size)
                (symbolp var-name))
           (pseudo-termp (bit-blasted-symbolic-array-aux current-index len element-size var-name)))
  :hints (("Goal" :in-theory (enable bit-blasted-symbolic-array-aux
                                     pseudo-term-listp-when-symbol-listp))))

(defund bit-blasted-symbolic-array (base-name length element-width)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp length)
                              (integerp element-width)
                              (<= 2 element-width))))
  (bit-blasted-symbolic-array-aux 0 length element-width base-name))

(defthm pseudo-termp-of-bit-blasted-symbolic-array
  (implies (and (symbolp base-name)
                (natp length)
                (posp element-width))
           (pseudo-termp (bit-blasted-symbolic-array base-name length element-width)))
  :hints (("Goal" :in-theory (enable bit-blasted-symbolic-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;drop?
;; (defun bv-array-write-nest-for-bit-vars-aux (current-index len element-size base-var-name)
;;   (declare (xargs :measure (nfix (+ 1 (- len current-index)))))
;;   (if (or (<= len current-index)
;;           (not (natp len))
;;           (not (natp current-index)))
;;       (list 'quote (repeat len '0))
;;     `(bv-array-write ',element-size
;;                      ',len
;;                      ',current-index
;;                      ,(bvcat-nest-for-items (make-var-names-aux base-var-name (* 8 current-index) (+ 7 (* 8 current-index))) 1)
;;                      ,(bv-array-write-nest-for-bit-vars-aux (+ 1 current-index) len element-size base-var-name))))

;; ;the 0th element of the array will contain (bvcat in0 1 (bvcat in1 1 ...))
;; ;swap the params?
;; (defun bv-array-write-nest-for-bit-vars (base-name element-count element-size)
;;   (bv-array-write-nest-for-bit-vars-aux 0 element-count element-size base-name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;dups?
(defun make-bit-blasted-expression (bit-index name)
  (if (zp bit-index)
      (pack$ name "_" 0)
    `(bvcat '1 ,(pack$ name "_" bit-index)
            ',bit-index ,(make-bit-blasted-expression (+ -1 bit-index) name))))

(defun bit-blast-byte-names (byte-name-lst)
  (if (endp byte-name-lst)
      nil
    (cons (make-bit-blasted-expression 7 (car byte-name-lst))
          (bit-blast-byte-names (cdr byte-name-lst)))))

(defun bit-blasted-symbolic-byte-list (base-name num-vars)
  ;; todo: omit the _, making names like in0_0 ?
  (let* ((byte-var-names (make-var-names (pack$ base-name '_) num-vars))
         ;; this is a list of bvcat terms:
         (bit-blasted-bytes (bit-blast-byte-names byte-var-names)))
    (make-cons-nest bit-blasted-bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun append-numbers (n name)
  (declare (xargs :measure (nfix (+ 1 n))))
  (if (not (natp n))
      nil
    (cons (pack$ name "_" n)
          (append-numbers (+ -1 n) name))))

;makes a list of the variable names for the bits in the indicated bytes
(defun make-list-of-bit-variable-names (base-name byte-num acc)
  (declare (xargs :measure (nfix (+ 1 byte-num))))
  (if (not (natp byte-num))
      acc
    (make-list-of-bit-variable-names base-name
                                     (+ -1 byte-num)
                                     (append (append-numbers 7 (pack$ base-name "_" byte-num)) acc))))

;assumes the array elements are bytes
(defun make-bit-variable-list-for-array (array-name length)
  (make-cons-nest (make-list-of-bit-variable-names array-name (+ -1 length) nil)))

;(local (in-theory (disable ORDINAL-TRICHOTOMY))) ;looped before i added the (not (natp x)) stuff below

;; (defun make-bit-blasted-array-expression-aux (index length name)
;;   (declare (xargs :measure (+ 1 (nfix (- length index)))))
;;   (if (or (<= length index)
;;           (not (natp length))
;;           (not (natp index)))
;;       'nil
;;     `(cons ,(make-bit-blasted-expression 7 (pack$ name "_" index))
;;            ,(make-bit-blasted-array-expression-aux (+ 1 index) length name))))

;; (defun make-bit-blasted-array-expression (length name)
;; ;;   (declare (xargs :guard (and (symbolp name)
;; ;;                               (natp length))))
;;   (make-bit-blasted-array-expression-aux 0 length name))b

;BBOZO this largely duplicates the above?
(defun make-bit-var-list-for-byte (bit-index name)
  (if (zp bit-index)
      (list (pack$ name "_" 0))
    (cons (pack$ name "_" bit-index)
          (make-bit-var-list-for-byte (+ -1 bit-index) name))))

(defun make-bit-var-list-for-bytes-aux (index length name)
  (declare (xargs :measure (+ 1 (nfix (- length index)))))
  (if (or (<= length index)
          (not (natp length))
          (not (natp index)))
      nil
    (append (make-bit-var-list-for-byte 7 (pack$ name "_" index))
            (make-bit-var-list-for-bytes-aux (+ 1 index) length name))))

(defun make-bit-var-list-for-bytes (length name)
;;   (declare (xargs :guard (and (symbolp name)
;;                               (natp length))))
  (make-bit-var-list-for-bytes-aux 0 length name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;used in lots of axe examples
(defun pairlis$-safe (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (equal (len x) (len y))
      (pairlis$ x y)
    (er hard? 'pairlis$-safe "Lists lengths unequal")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Making hyps that assert that lists of vars are bvs/bits.

(defun unsigned-byte-p-hyp (size-term item)
  (declare (xargs :guard t)) ; args may be untranslated terms
  `(unsigned-byte-p ,size-term ,item))

(defun unsigned-byte-p-hyps (size-term ; often a quoted constant
                             items ; may be untranslated terms
                             )
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      nil
    (cons (unsigned-byte-p-hyp size-term (first items))
          (unsigned-byte-p-hyps size-term (rest items)))))

;; This makes calls of unsigned-byte-p.  Instead, it could make calls of bitp.
(defun bit-hyps (items)
  (declare (xargs :guard (true-listp items)))
  (unsigned-byte-p-hyps ''1 items))

(defun byte-hyps (items)
  (declare (xargs :guard (true-listp items)))
  (unsigned-byte-p-hyps ''8 items))

;; ;; todo: improve name
;; (defun int-hyps (items)
;;   (declare (xargs :guard (true-listp items)))
;;   (unsigned-byte-p-hyps ''32 items))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a list of assumptions that together assert that the variables
;; base-name0 through base-name(count-1) are bytes.
(defund symbolic-byte-assumptions (base-name count)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp count))))
  (byte-hyps (make-var-names base-name count)))

;; ;; Makes a list of assumptions that together assert that the variables
;; ;; base-name0 through base-name(count-1) are unsigned-byte 32s.
;; (defund symbolic-int-assumptions (base-name count)
;;   (declare (xargs :guard (and (symbolp base-name)
;;                               (natp count))))
;;   (int-hyps (make-var-names base-name count)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Creates a list of assumptions asserting that the VARS are all booleans.
(defun boolean-hyps (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      nil
    (cons `(booleanp ,(first vars))
          (boolean-hyps (rest vars)))))
