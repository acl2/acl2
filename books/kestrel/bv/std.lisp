; Connecting some notions from this library to some notions from STD
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "bit-to-bool")
(include-book "bool-to-bit")

(defthm bool->bit-becomes-bool-to-bit
  (equal (bool->bit x)
         (bool-to-bit x))
  :hints (("Goal" :in-theory (enable bool->bit))))

;; Note that bit->bool checks for equality with 1, so non-bits are false.
;; but bit-to-bool checks for non-equality with 0, so non-bits are true.
(defthm bit->bool-becomes-bit-to-bool
  (equal (bit->bool x)
         (if (unsigned-byte-p 1 x)
             (bit-to-bool x)
           nil))
  :hints (("Goal" :in-theory (enable bit->bool))))
