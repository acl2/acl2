; BV Lists Library: bytes-to-bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "byte-to-bits")
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../lists-light/append"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../lists-light/nth"))
(local (include-book "../lists-light/len"))
(local (include-book "../lists-light/take"))

;; Convert a sequence of 8-bit bytes to a sequence of bits.  The bits from
;; earlier bytes come earlier in the result.  For a given byte, the most
;; significant bit comes first, so this is "big endian."
(defund bytes-to-bits (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (if (atom bytes)
      nil
    (append (byte-to-bits (first bytes))
            (bytes-to-bits (rest bytes)))))

(defthm all-unsigned-byte-p-of-bytes-to-bits
  (all-unsigned-byte-p 1 (bytes-to-bits bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm all-integerp-of-bytes-to-bits
  (all-integerp (bytes-to-bits bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm len-of-bytes-to-bits
  (equal (len (bytes-to-bits lst))
         (* 8 (len lst)))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm consp-of-bytes-to-bits
  (equal (consp (bytes-to-bits bytes))
         (consp bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm car-of-bytes-to-bits
  (implies (consp bytes)
           (equal (car (bytes-to-bits bytes))
                  (getbit 7 (car bytes))))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm cadr-of-bytes-to-bits
  (implies (consp bytes)
           (equal (cadr (bytes-to-bits bytes))
                  (getbit 6 (car bytes))))
  :hints (("Goal" :in-theory (enable bytes-to-bits byte-to-bits))))

(local
 (defun cdr-sub8-induct (bytes n)
   (if (atom bytes)
       (list bytes n)
     (cdr-sub8-induct (rest bytes) (+ -8  n)))))

(defthm nth-of-bytes-to-bits
  (implies (and (< n (* 8 (len bytes)))
                (natp n))
           (equal (nth n (bytes-to-bits bytes))
                  (getbit (- 7 (mod n 8))
                          (nth (floor n 8) bytes))))
  :hints (("Goal" :induct (cdr-sub8-induct bytes n)
           :in-theory (enable bytes-to-bits (:i nth)))))

(defthm nthcdr-of-8-and-bytes-to-bits
  (equal (nthcdr 8 (bytes-to-bits bytes))
         (bytes-to-bits (cdr bytes)))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm bytes-to-bits-of-cons
  (equal (bytes-to-bits (cons byte bytes))
         (append (byte-to-bits byte)
                 (bytes-to-bits bytes)))
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defthm bytes-to-bits-of-append
  (equal (bytes-to-bits (append lst1 lst2))
         (append (bytes-to-bits lst1)
                 (bytes-to-bits lst2)))
  :hints (("Goal" :in-theory (enable bytes-to-bits append))))

(defthm bytes-to-bits-of-nil
  (equal (bytes-to-bits nil)
         nil)
  :hints (("Goal" :in-theory (enable bytes-to-bits))))

(defun sub1-cdr-induct (n lst)
  (if (endp lst)
      (list n lst)
    (sub1-cdr-induct (+ -1 n) (cdr lst))))

(local
 (defthm <-of-times-8
   (implies (integerp n)
            (equal (< 0 (* 8 n))
                   (< 0 n)))
   :hints (("Goal" :cases ((< 0 N))))))

;move?
(defthm take-of-times-8-and-bytes-to-bits
  (implies (and (natp n)
                (<= n (len lst))
                (consp lst))
           (equal (take (* 8 n) (bytes-to-bits lst))
                  (bytes-to-bits (take n lst))))
  :hints (("Goal"
           :induct (sub1-cdr-induct n lst)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (zp byte-to-bits bytes-to-bits take
                               consp-to-len-bound)
                           (;;list::len-pos-rewrite
                            ;;list::len-when-at-most-1
                            ;;list::len-equal-0-rewrite
                            )))))

;move?
(defthm nthcdr-of-times-8-and-bytes-to-bits
  (implies (and (natp n)
                (<= n (len lst))
                (consp lst))
           (equal (nthcdr (* 8 n) (bytes-to-bits lst))
                  (bytes-to-bits (nthcdr n lst))))
  :hints (("Goal"
           :induct (sub1-cdr-induct n lst)
           :in-theory (e/d (bytes-to-bits byte-to-bits
                                          ;;list::nthcdr-of-cons
                                          )
                           (;len-of-cdr-better
                            )))))
