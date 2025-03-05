; A library about lists of bit vectors.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unsigned-byte-listp-def")
(include-book "unsigned-byte-listp")
(include-book "signed-byte-listp-def")

(include-book "byte-listp-def")
(include-book "byte-listp")

(include-book "bit-listp")
(include-book "bit-listp-rules")

(include-book "all-unsigned-byte-p")
(include-book "all-unsigned-byte-p2")
(include-book "all-all-unsigned-byte-p")

(include-book "all-signed-byte-p")

(include-book "len-mult-of-8p")
(include-book "len-mult-of-8p-rules")

(include-book "bits-to-byte")
(include-book "bits-to-byte-little")
(include-book "bits-to-byte-little-rules")
(include-book "bits-to-bytes")
(include-book "bits-to-bytes2")
(include-book "bits-to-bytes-little")
(include-book "bits-to-bytes-little2")
(include-book "byte-to-bits")
(include-book "byte-to-bits-little")
(include-book "bytes-to-bits")
(include-book "bytes-to-bits2")
(include-book "bytes-to-bits-little")
(include-book "bytes-to-bits-little2")
(include-book "bits-and-bytes-inversions")
(include-book "bits-and-bytes-inversions-little")

;; Map BV functions over lists:
(include-book "bvxor-list")
(include-book "bvxor-list-rules")
(include-book "bvnot-list")
(include-book "bvchop-list")
(include-book "getbit-list")
(include-book "map-slice") ; todo: call this slice-list?

(include-book "width-of-widest-int")

(include-book "packbv-def")
(include-book "packbv")
(include-book "packbv-theorems")
(include-book "unpackbv")
(include-book "packbv-and-unpackbv")
(include-book "map-packbv")
(include-book "map-packbv-little")
(include-book "map-unpackbv-little")
(include-book "packing0")
(include-book "packing")

(include-book "packbv-little")
(include-book "unpackbv-little")
(include-book "packbv-little-and-unpackbv-little")

(include-book "packbvs")
(include-book "packbvs-little")

(include-book "bv-arrayp")
(include-book "bv-array-read")
(include-book "bv-array-read-rules")
(include-book "bv-array-write")
(include-book "bv-array-clear")
(include-book "bv-array-if")
(include-book "append-arrays")
(include-book "array-of-zeros")
(include-book "bv-arrays")
(include-book "bv-array-conversions")
(include-book "bv-array-conversions2")
(include-book "bv-array-conversions-gen")

(include-book "bv-array-read-chunk-little")

(include-book "bvnth")

(include-book "list-patterns")

(include-book "bvplus-list")

(include-book "logext-list")

(include-book "byte-fix-list")
