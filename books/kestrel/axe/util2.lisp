; Utilities for stating claims to be proved by Axe
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system) ;(local (include-book "kestrel/lists-light/repeat" :dir :system))
(include-book "kestrel/utilities/make-cons-nest" :dir :system)
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; TODO: For these functions, should the count or the base name come first?  Be consistent.
;; TODO: When creating numbered vars consider using 00, 01, etc. instead of 0, 1, etc (assuming 2 digit numbers).

;; Make a symbolic list term (a cons nest) containing the variables <base-name>0
;; through <base-name>(len-1).  Can be useful when unrolling specs.
(defun symbolic-list (base-name len)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp len))))
  (make-cons-nest (make-var-names-aux base-name 0 (+ -1 len))))

(defthmd pseudo-termp-of-symbolic-list
  (pseudo-termp (symbolic-list base-name len)))

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

;fixme pass in a size
(defund bvcat-nest-for-vars (index size base-name)
  (declare (xargs :guard (and (natp index)
                              (natp size)
                              (symbolp base-name))))
  (if (zp index)
      (pack$ base-name (nat-to-string index))
    `(bvcat ',size
            ,(pack$ base-name (nat-to-string index))
            ',(* index size)
            ,(bvcat-nest-for-vars (+ -1 index) size base-name))))

(defthm pseudo-termp-of-bvcat-nest-for-vars
  (implies (and (natp index)
                (natp size)
                (symbolp base-name))
           (pseudo-termp (bvcat-nest-for-vars index size base-name)))
  :hints (("Goal" :in-theory (enable bvcat-nest-for-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bit-blasted-bv-array-write-nest-for-vars-aux (current-index len element-size var-name)
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
                     ,(bvcat-nest-for-vars (+ -1 element-size) 1 (pack$ var-name "_" current-index "_"))
                     ,(bit-blasted-bv-array-write-nest-for-vars-aux (+ 1 current-index) len element-size var-name))))

(defthm pseudo-termp-of-bit-blasted-bv-array-write-nest-for-vars-aux
  (implies (and (natp current-index)
                (natp len)
                (posp element-size)
                (symbolp var-name))
           (pseudo-termp (bit-blasted-bv-array-write-nest-for-vars-aux current-index len element-size var-name)))
  :hints (("Goal" :in-theory (enable bit-blasted-bv-array-write-nest-for-vars-aux))))

;is var-count really element-count?
(defund bit-blasted-bv-array-write-nest-for-vars (var-name var-count element-size)
  (declare (xargs :guard (and (symbolp var-name)
                              (natp var-count)
                              (posp element-size))))
  (bit-blasted-bv-array-write-nest-for-vars-aux 0 var-count element-size var-name))

(defthm pseudo-termp-of-bit-blasted-bv-array-write-nest-for-vars
  (implies (and (symbolp var-name)
                (natp var-count)
                (posp element-size))
           (pseudo-termp (bit-blasted-bv-array-write-nest-for-vars var-name var-count element-size)))
  :hints (("Goal" :in-theory (enable bit-blasted-bv-array-write-nest-for-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund bv-array-write-nest-for-vars-aux (current-index len element-size var-name)
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
                     ,(PACK$ var-name (NAT-TO-STRING current-index))
                     ,(bv-array-write-nest-for-vars-aux (+ 1 current-index) len element-size var-name))))

(defthm pseudo-termp-of-bv-array-write-nest-for-vars-aux
  (implies (and (natp current-index)
                (natp len)
                (posp element-size)
                (symbolp var-name))
           (pseudo-termp (bv-array-write-nest-for-vars-aux current-index len element-size var-name)))
  :hints (("Goal" :in-theory (enable bv-array-write-nest-for-vars-aux))))

(defund bv-array-write-nest-for-vars (var-name var-count element-size)
  (declare (xargs :guard (and (symbolp var-name)
                              (natp var-count)
                              (posp element-size))))
  (bv-array-write-nest-for-vars-aux 0 var-count element-size var-name))

(defthm pseudo-termp-of-bv-array-write-nest-for-vars
  (implies (and (symbolp var-name)
                (natp var-count)
                (posp element-size))
           (pseudo-termp (bv-array-write-nest-for-vars var-name var-count element-size)))
  :hints (("Goal" :in-theory (enable bv-array-write-nest-for-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;items should have length at least 2?
;total-size should be (* item-size (len items)))
;we pass in total-size to avoid calling (len items) over and over
(defun bvcat-nest-for-items-aux (items total-size item-size)
  (if (endp items)
      'error-in-bvcat-nest-for-items-aux
    (if (endp (cdr items))
        (car items)
      `(bvcat ',item-size
              ,(car items)
              ',(- total-size item-size)
              ,(bvcat-nest-for-items-aux (cdr items) (- total-size item-size) item-size)))))

;bozo use this more?
(defun bvcat-nest-for-items (items item-size)
  (bvcat-nest-for-items-aux items (* item-size (len items)) item-size))

(defun bv-array-write-nest-for-bit-vars-aux (current-index len element-size base-var-name)
  (declare (xargs :measure (nfix (+ 1 (- len current-index)))))
  (if (or (<= len current-index)
          (not (natp len))
          (not (natp current-index)))
      (list 'quote (repeat len '0))
    `(bv-array-write ',element-size
                     ',len
                     ',current-index
                     ,(bvcat-nest-for-items (make-var-names-aux base-var-name (* 8 current-index) (+ 7 (* 8 current-index))) 1)
                     ,(bv-array-write-nest-for-bit-vars-aux (+ 1 current-index) len element-size base-var-name))))

;the 0th element of the array will contain (bvcat in0 1 (bvcat in1 1 ...))
;swap the params?
(defun bv-array-write-nest-for-bit-vars (base-name element-count element-size)
  (bv-array-write-nest-for-bit-vars-aux 0 element-count element-size base-name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun unsigned-byte-p-hyps (var-size-alist)
  (declare (xargs :guard (and (symbol-alistp var-size-alist)
                              (nat-listp (strip-cdrs var-size-alist)))))
  (if (endp var-size-alist)
      nil
    (let* ((entry (car var-size-alist))
           (var-name (car entry))
           (size (cdr entry)))
      (cons `(unsigned-byte-p ',size ,var-name)
            (unsigned-byte-p-hyps (cdr var-size-alist))))))

;used in lots of axe examples
(defun pairlis$-safe (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (equal (len x) (len y))
      (pairlis$ x y)
    (hard-error 'pairlis$-safe "Lists lengths unequal" nil)))

(defmacro bit-hyps (names)
  `(unsigned-byte-p-hyps (pairlis$ ,names
                                   (repeat (len ,names) 1))))

(defmacro byte-hyps (names)
  `(unsigned-byte-p-hyps (pairlis$ ,names
                                   (repeat (len ,names) 8))))

(defmacro int-hyps (names)
  `(unsigned-byte-p-hyps (pairlis$ ,names
                                   (repeat (len ,names) 32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund symbolic-byte-assumptions (base-name count)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp count))))
  (byte-hyps (make-var-names base-name count)))

(defund symbolic-int-assumptions (base-name count)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp count))))
  (int-hyps (make-var-names base-name count)))

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
  (let* ((byte-var-names (make-var-names-aux (pack$ base-name '_) 0 (+ -1 num-vars)))
         ;; this is a list of bvcat terms:
         (bit-blasted-byte-var-names (bit-blast-byte-names byte-var-names)))
    (make-cons-nest bit-blasted-byte-var-names)))

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


(defun make-bit-variable-list-for-array (array-name length)
  (make-cons-nest (make-list-of-bit-variable-names array-name (+ -1 length) nil)))

;(local (in-theory (disable ORDINAL-TRICHOTOMY))) ;looped before i added the (not (natp x)) stuff below

(defun make-bit-blasted-array-expression-aux (index length name)
  (declare (xargs :measure (+ 1 (nfix (- length index)))))
  (if (or (<= length index)
          (not (natp length))
          (not (natp index)))
      'nil
    `(cons ,(make-bit-blasted-expression 7 (pack$ name "_" index))
           ,(make-bit-blasted-array-expression-aux (+ 1 index) length name))))

(defun make-bit-blasted-array-expression (length name)
;;   (declare (xargs :guard (and (symbolp name)
;;                               (natp length))))
  (make-bit-blasted-array-expression-aux 0 length name))


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

;move
;; Make a term representing a symbolic array of bit vectors variables NAME0,
;; ...,  NAME(length-1), each of ELEMENT-WIDTH bits.
(defun symbolic-array (name length element-width)
  (declare (xargs :guard (and (symbolp name)
                              (natp length)
                              (posp element-width))))
  (bv-array-write-nest-for-vars name length element-width))

(defund bit-blasted-symbolic-array (name length element-width)
  (declare (xargs :guard (and (symbolp name)
                              (natp length)
                              (posp element-width))))
  (bit-blasted-bv-array-write-nest-for-vars name length element-width))

(defthm pseudo-termp-of-bit-blasted-symbolic-array
  (implies (and (symbolp name)
                (natp length)
                (posp element-width))
           (pseudo-termp (bit-blasted-symbolic-array name length element-width)))
  :hints (("Goal" :in-theory (enable bit-blasted-symbolic-array))))
