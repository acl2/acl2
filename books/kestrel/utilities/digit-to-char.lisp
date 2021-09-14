; A lightweight book about digit-to-char
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable digit-to-char))

(defthm equal-of-0-and-digit-to-char
  (equal (equal #\0 (digit-to-char n))
         (or (equal n 0)
             (not (natp n))
             (< 15 n)))
  :hints (("Goal" :in-theory (enable digit-to-char))))

;; digit-to-char is essentially injective
(defthm equal-of-digit-to-char-and-digit-to-char
  (equal (equal (digit-to-char n1) (digit-to-char n2))
         (if (or (zp n1)
                 (< 15 n1))
             (or (zp n2)
                 (< 15 n2))
           (equal n1 n2)))
  :hints (("Goal" :in-theory (enable digit-to-char))))
