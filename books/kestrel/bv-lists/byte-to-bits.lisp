; BV Lists Library: byte-to-bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../bv/getbit")
(include-book "all-unsigned-byte-p")
(local (include-book "../lists-light/nth"))

;; Convert a byte into a list of 8 bits. The most significant bit comes first,
;; so this is "big endian."  We could define this as (unpackbv 8 1 byte), but
;; that seems too complicated.
(defund byte-to-bits (byte)
  (declare (xargs :guard (integerp byte)
                  ;;(unsigned-byte-p 8 byte) ;todo: strengthen guard to this
                  ))
  (list (getbit 7 byte)
        (getbit 6 byte)
        (getbit 5 byte)
        (getbit 4 byte)
        (getbit 3 byte)
        (getbit 2 byte)
        (getbit 1 byte)
        (getbit 0 byte)))

(defthm all-unsigned-byte-p-of-byte-to-bits
  (all-unsigned-byte-p 1 (byte-to-bits byte))
  :hints (("Goal" :in-theory (enable byte-to-bits))))

(defthm all-integerp-of-byte-to-bits
  (all-integerp (byte-to-bits byte))
  :hints (("Goal" :in-theory (enable byte-to-bits))))

(defthm len-of-byte-to-bits
  (equal (len (byte-to-bits byte))
         8)
  :hints (("Goal" :in-theory (enable byte-to-bits))))

(defthm byte-to-bits-of-bvchop
  (implies (and (<= 8 size)
                (integerp size))
           (equal (byte-to-bits (bvchop size byte))
                  (byte-to-bits byte)))
  :hints (("Goal" :in-theory (enable byte-to-bits))))

(defthm nth-of-byte-to-bits
  (implies (and (natp n)
                (< n 8))
           (equal (nth n (byte-to-bits byte))
                  (getbit (- 7 n) byte)))
  :hints (("Goal" :in-theory (enable byte-to-bits))))

(defthm car-of-byte-to-bits
  (equal (car (byte-to-bits byte))
         (getbit 7 byte))
  :hints (("Goal" :in-theory (enable byte-to-bits))))
