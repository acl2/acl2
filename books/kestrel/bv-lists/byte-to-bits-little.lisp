; BV Lists Library: byte-to-bits-little
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

;; Convert a byte into a list of 8 bits. The least significant bit comes first
;; so this is "little endian."  We could define this as (reverse-list (unpackbv
;; 8 1 (first bytes))), but that seems too complicated.
(defund byte-to-bits-little (byte)
  (declare (xargs :guard (unsigned-byte-p 8 byte)))
  (list (getbit 0 byte)
        (getbit 1 byte)
        (getbit 2 byte)
        (getbit 3 byte)
        (getbit 4 byte)
        (getbit 5 byte)
        (getbit 6 byte)
        (getbit 7 byte)))

(defthm all-unsigned-byte-p-of-byte-to-bits-little
  (all-unsigned-byte-p 1 (byte-to-bits-little byte))
  :hints (("Goal" :in-theory (enable byte-to-bits-little))))

(defthm all-integerp-of-byte-to-bits-little
  (all-integerp (byte-to-bits-little byte))
  :hints (("Goal" :in-theory (enable byte-to-bits-little))))

(defthm len-of-byte-to-bits-little
  (equal (len (byte-to-bits-little byte))
         8)
  :hints (("Goal" :in-theory (enable byte-to-bits-little))))

(defthm byte-to-bits-little-of-bvchop
  (implies (and (<= 8 size)
                (integerp size))
           (equal (byte-to-bits-little (bvchop size byte))
                  (byte-to-bits-little byte)))
  :hints (("Goal" :in-theory (enable byte-to-bits-little))))

(defthm nth-of-byte-to-bits-little
  (implies (and (natp n)
                (< n 8))
           (equal (nth n (byte-to-bits-little byte))
                  (getbit n byte)))
  :hints (("Goal" :in-theory (enable byte-to-bits-little))))

(defthm car-of-byte-to-bits-little
  (equal (car (byte-to-bits-little byte))
         (getbit 0 byte))
  :hints (("Goal" :in-theory (enable byte-to-bits-little))))
