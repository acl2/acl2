; A lightweight book about the built-in function our-digit-char-p
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that our-digit-char-p is deceptively named, as it is not boolean.

(in-theory (disable our-digit-char-p))

(defthm our-digit-char-p-of-0-arg1
  (equal (our-digit-char-p #\0 radix)
         (if (< 0 radix)
             0
           nil))
  :hints (("Goal" :in-theory (enable our-digit-char-p))))
