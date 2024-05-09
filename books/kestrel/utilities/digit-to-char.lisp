; A lightweight book about the built-in function digit-to-char
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable digit-to-char))

(defthm our-digit-char-p-of-digit-to-char
  (implies (and (natp n)
                (< n radix))
           (our-digit-char-p (digit-to-char n) radix))
  :hints (("Goal" :in-theory (enable our-digit-char-p digit-to-char))))

;; Note that our-digit-char-p is deceptively named, as it is not boolean.
(defthm our-digit-char-p-of-digit-to-char-gen
  (implies (< 0 radix)
           (iff (our-digit-char-p (digit-to-char n) radix)
                (if (and (< n 16) ; so digit-to-char works
                         (natp n))
                    (< n radix)
                  t)))
  :hints (("Goal" :in-theory (enable our-digit-char-p digit-to-char))))

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
