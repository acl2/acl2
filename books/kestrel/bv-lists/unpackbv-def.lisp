; BV Lists Library: Defintion of unpackbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a utility for unpacking (i.e., diassembling) larger bit
;; vectors into smaller bit vectors.  The smaller bit vectors can of course be
;; single bits.

(include-book "../bv/bvcat-def")
(include-book "../bv/slice-def")

;num is the number of chunks, size is the number of bits per chunk.
;The higher bits of BV come first in the result.
(defund unpackbv (num size bv)
  (declare (type (integer 0 *) size) ;todo: disallow 0?
           (type (integer 0 *) num)
           (type integer bv))
  (if (zp num)
      nil
    (cons (slice (+ -1 (* num size))
                 (* (+ -1 num) size)
                 bv)
          (unpackbv (+ -1 num) size bv))))
