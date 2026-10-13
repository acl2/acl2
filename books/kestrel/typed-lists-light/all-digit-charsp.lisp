; Recognize a list of digit-chars.
;
; Copyright (C) 2023-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This may often be a good idea, but we make it local
;; here so as not to break others' proofs:
(local (in-theory (disable digit-char-p))) ;expensive to open

(defund all-digit-charsp (chars radix)
  (declare (xargs :guard (and (character-listp chars)
                              (integerp radix)
                              (<= 2 radix)
                              (<= radix 36))))
  (if (endp chars)
      (null chars)
    (and (digit-char-p (first chars) radix)
         (all-digit-charsp (rest chars) radix))))
