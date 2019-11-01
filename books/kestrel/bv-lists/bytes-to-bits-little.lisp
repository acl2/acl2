; BV Lists Library: bytes-to-bits-little
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "byte-to-bits-little")
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../lists-light/append"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../lists-light/nth"))
(local (include-book "../lists-light/len"))

;; Convert a sequence of 8-bit bytes to a sequence of bits.  The bits from
;; earlier bytes come earlier in the result.  But the least significant bit of
;; each byte comes first in the result, so this is "little endian".
(defund bytes-to-bits-little (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (if (endp bytes)
      nil
    (append (byte-to-bits-little (first bytes)) ;(reverse-list (unpackbv 8 1 (first bytes)))
            (bytes-to-bits-little (rest bytes)))))

(defthm all-unsigned-byte-p-of-bytes-to-bits-little
  (all-unsigned-byte-p 1 (bytes-to-bits-little bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))

(defthm all-integerp-of-bytes-to-bits-little
  (all-integerp (bytes-to-bits-little bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))

(defthm len-of-bytes-to-bits-little
  (equal (len (bytes-to-bits-little bytes))
         (* 8 (len bytes)))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))

(defthm consp-of-bytes-to-bits-little
  (equal (consp (bytes-to-bits-little bytes))
         (consp bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))

(defthm car-of-bytes-to-bits-little
  (implies (consp bytes)
           (equal (car (bytes-to-bits-little bytes))
                  (getbit 0 (car bytes))))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little bytes-to-bits-little))))

(defthm cadr-of-bytes-to-bits-little
  (implies (consp bytes)
           (equal (cadr (bytes-to-bits-little bytes))
                  (getbit 1 (car bytes))))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little BYTE-TO-BITS-LITTLE))))

(local
 (defun cdr-sub8-induct (bytes n)
   (if (atom bytes)
       (list bytes n)
     (cdr-sub8-induct (rest bytes) (+ -8  n)))))

(defthm nth-of-bytes-to-bits-little
  (implies (and (< n (* 8 (len bytes)))
                (natp n))
           (equal (nth n (bytes-to-bits-little bytes))
                  (getbit (mod n 8)
                          (nth (floor n 8) bytes))))
  :hints (("Goal" :induct (cdr-sub8-induct bytes n)
           :in-theory (enable bytes-to-bits-little))))

(defthm nthcdr-of-8-and-bytes-to-bits-little
  (equal (nthcdr 8 (bytes-to-bits-little bytes))
         (bytes-to-bits-little (cdr bytes)))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))

(defthm bytes-to-bits-little-of-cons
  (equal (bytes-to-bits-little (cons byte bytes))
         (append (byte-to-bits-little byte)
                 (bytes-to-bits-little bytes)))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))

(defthm bytes-to-bits-little-of-append
  (equal (bytes-to-bits-little (append lst1 lst2))
         (append (bytes-to-bits-little lst1)
                 (bytes-to-bits-little lst2)))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little append))))

(defthm bytes-to-bits-little-of-nil
  (equal (bytes-to-bits-little nil)
         nil)
  :hints (("Goal" :in-theory (enable bytes-to-bits-little))))
