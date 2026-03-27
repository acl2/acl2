; A library about arrays of bit vectors.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-arrayp")
(include-book "bv-array-read")
(include-book "bv-array-read-rules")
(include-book "bv-array-write")
(include-book "bv-array-clear")
(include-book "bv-array-clear-range")
(include-book "bv-array-if")
(include-book "append-arrays")
(include-book "array-of-zeros")
(include-book "bv-arrays")
(include-book "bv-array-conversions")
(include-book "bv-array-conversions2")
(include-book "bv-array-conversions-gen")
(include-book "array-patterns")

(include-book "bv-array-read-chunk-little")
