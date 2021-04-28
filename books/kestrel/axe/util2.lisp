; Utilities for stating claims to be proved by Axe
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

(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system) ;(local (include-book "kestrel/lists-light/repeat" :dir :system))
(include-book "kestrel/utilities/make-cons-nest" :dir :system)

(defun cons-nest-of-vars (name var-count)
  (declare (xargs :guard (and (symbolp name)
                              (natp var-count))))
  (make-cons-nest (make-var-names-aux name 0 (+ -1 var-count))))

;; Make a symbolic list term (cons nest) containing the variables base-name0
;; through base-name(len-1).  Can be useful when unrolling specs.
(defun symbolic-list (base-name len)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp len))))
  (cons-nest-of-vars base-name len))

;; A version of symbolic-list that makes clear by its name that the vars are
;; intended to be bytes (that fact should actually get enforced by additional
;; assumptions).
(defun symbolic-bytes (base-name len)
  (declare (xargs :guard (and (symbolp base-name)
                              (natp len))))
  (symbolic-list base-name len))

;fixme pass in a size
(defun bvcat-nest-for-vars (index size base-name)
  (declare (xargs :guard (and (natp index)
                              (natp size)
                              (symbolp base-name))))
  (if (zp index)
      (pack$ base-name (nat-to-string index))
    `(bvcat ',size
            ,(pack$ base-name (nat-to-string index))
            ',(* index size)
            ,(bvcat-nest-for-vars (+ -1 index) size base-name))))

(defun bit-blasted-bv-array-write-nest-for-vars-aux (current-index len element-size var-name)
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

;is var-count really element-count?
(defun bit-blasted-bv-array-write-nest-for-vars (var-name var-count element-size)
  (declare (xargs :guard (and (symbolp var-name)
                              (natp var-count)
                              (posp element-size))))
  (bit-blasted-bv-array-write-nest-for-vars-aux 0 var-count element-size var-name))

(defun bv-array-write-nest-for-vars-aux (current-index len element-size var-name)
  (DECLARE (XARGS :measure (nfix (+ 1 (- len current-index)))
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

(defun bv-array-write-nest-for-vars (var-name var-count element-size)
  (declare (xargs :guard (and (symbolp var-name)
                              (natp var-count)
                              (posp element-size))))
  (bv-array-write-nest-for-vars-aux 0 var-count element-size var-name))

;the numbering starts at 0
(defmacro var-names (base-symbol count)
  `(make-var-names-aux ,base-symbol 0 (+ -1 ,count)))

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
  (declare (xargs :measure (nfix (+ 1 (- len current-index)))
                  :mode :program))
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
  (declare (xargs :mode :program))
  (bv-array-write-nest-for-bit-vars-aux 0 element-count element-size base-name))


;needs at least 2 symbols
(defun bvcat-nest-for-bits-aux (symbols count)
  (if (endp symbols)
      'error
    (if (endp (cdr symbols))
        `,(car symbols)
      `(bvcat '1
              ,(car symbols)
              ',(+ -1 count)
              ,(bvcat-nest-for-bits-aux (cdr symbols) (+ -1 count))))))

;high bits come first
(defun bvcat-nest-for-bits (symbols)
  (if (endp symbols)
      ''0
    (if (endp (cdr symbols))
        `(getbit '0 ,(car symbols))
      (bvcat-nest-for-bits-aux symbols (len symbols)))))

(defun bvcat-nest-for-input-nodes (base-name start-num end-num)
  (declare (xargs :mode :program))
  (bvcat-nest-for-bits (reverse (make-var-names-aux base-name start-num end-num))))

(defun unsigned-byte-p-hyps (var-size-alist)
  (if (endp var-size-alist)
      nil
    (let* ((entry (car var-size-alist))
           (var-name (car entry))
           (size (cdr entry)))
      (cons `(unsigned-byte-p ',size ,var-name)
            (unsigned-byte-p-hyps (cdr var-size-alist))))))

;used in lots of axe examples
(defun pairlis$-safe (lst1 lst2)
  (if (equal (len lst1) (len lst2))
      (pairlis$ lst1 lst2)
    (hard-error 'pairlis$-safe "Lists lengths unequal" nil)))

(defmacro bit-hyps (names)
  `(unsigned-byte-p-hyps (pairlis$-safe ,names
                                        (repeat (len ,names) 1))))

(defmacro byte-hyps (names)
  `(unsigned-byte-p-hyps (pairlis$-safe ,names
                                        (repeat (len ,names) 8))))

(defmacro int-hyps (names)
  `(unsigned-byte-p-hyps (pairlis$-safe ,names
                                        (repeat (len ,names) 32))))

;move
(defun symbolic-byte-assumptions (basename count)
  (byte-hyps (make-var-names count basename)))

(defun symbolic-int-assumptions (basename count)
  (int-hyps (make-var-names count basename)))

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

(defun make-bit-blasted-cons-nest-for-vars (num-vars base-name)
  (declare (xargs :mode :program))
  (let* ((byte-var-names (make-var-names-aux (pack$ base-name '_) 0 (+ -1 num-vars)))
         ;this is a list of bvcat terms
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

(defun bit-blasted-symbolic-array (name length element-width)
  (declare (xargs :guard (and (symbolp name)
                              (natp length)
                              (posp element-width))))
  (bit-blasted-bv-array-write-nest-for-vars name length element-width))
