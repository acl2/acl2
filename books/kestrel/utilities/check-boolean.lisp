; Checking that a value is boolean
;
; Copyright (C) 2022 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Logically the identity
;; Throws an error if VAL is not boolean.
(defund check-boolean (val)
  (declare (xargs :guard t))
  (if (member-eq val '(t nil))
      val
    (prog2$ (er hard? 'check-boolean "Value is not boolean: ~x0." val)
            val)))

(defthm check-boolean-rewrite
  (equal (check-boolean val)
         val)
  :hints (("Goal" :in-theory (enable check-boolean))))
