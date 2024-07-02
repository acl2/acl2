; Rules combining bits-to-byte, etc. with packbv, etc.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also packing.lisp.

(include-book "packbv")
(include-book "unpackbv")
(include-book "bits-to-bytes")
(include-book "bytes-to-bits")
(local (include-book "packbv-theorems"))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;; We keep all these rules disabled because they switch between two different
;; sets of similar functions each of which has its own set of rules.

(defthmd bits-to-byte-becomes-packbv
  (equal (bits-to-byte bits)
         (packbv 8 1 bits))
  :hints (("Goal" :in-theory (enable bits-to-byte packbv slice-becomes-getbit))))

(defthmd packbv-becomes-bits-to-byte
  (equal (packbv 8 1 bits)
         (bits-to-byte bits))
  :hints (("Goal" :in-theory (enable bits-to-byte packbv slice-becomes-getbit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd byte-to-bits-becomes-unpackbv
  (equal (byte-to-bits byte)
         (unpackbv 8 1 byte))
  :hints (("Goal" :in-theory (enable unpackbv byte-to-bits))))

(defthmd unpackbv-becomes-byte-to-bits
  (equal (unpackbv 8 1 byte)
         (byte-to-bits byte))
  :hints (("Goal" :in-theory (enable unpackbv byte-to-bits))))
