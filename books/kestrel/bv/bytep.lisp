; A lightweight book that provides bytep
;
; Copyright (C) 2021 Kestrel Institute
; The definition of bytep is in books/std/basic/bytep.lisp.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The purpose of this book is to provide bytep without bringing in any other
;; machinery.

;; Note that the BV library usually uses (unsigned-byte-p 8 ...) instead of
;; bytep.

(defun bytep (x)
  (declare (xargs :guard t))
  (mbe :logic (unsigned-byte-p 8 x)
       :exec (and (integerp x) (<= 0 x) (< x 256))))
