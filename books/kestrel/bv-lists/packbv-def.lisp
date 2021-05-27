; BV Lists Library: definition of packbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a utility for packing (i.e., assembling) smaller bit
;; vectors into larger bit vectors.  The smaller bit vectors can of course be
;; single bits.

(include-book "../typed-lists-light/all-integerp")
(include-book "../bv/bvcat-def")

;; Pack the ITEMS, each of which should be a bit-vector of size ITEMSIZE, into
;; a single bit-vector, with earlier items occupying more significant bits of
;; the result.  This is a big-endian operation.  The length of ITEMS should be
;; ITEMCOUNT.  If an item is wider then ITEMSIZE bits, any excess bits are
;; ignored.  If the length of ITEMS is less than ITEMCOUNT, missing items are
;; treated as 0.  If the length of ITEMS is greater than ITEMCOUNT, extra items
;; are ignored.
;todo: make a wrapper that computes the itemcount from the items
(defund packbv (itemcount itemsize items)
  (declare (type (integer 0 *) itemsize)
           (type (integer 0 *) itemcount)
           (xargs :guard (and (true-listp items)
                              (all-integerp items))))
  (if (zp itemcount)
      0
    (bvcat itemsize
           (ifix (car items))
           (* itemsize (+ -1 itemcount))
           (packbv (+ -1 itemcount) itemsize (cdr items)))))
