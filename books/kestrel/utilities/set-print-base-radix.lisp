; A lightweight book about the built-in function set-print-base-radix
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable set-print-base-radix))

(defthm w-of-set-print-base-radix
  (equal (w (set-print-base-radix base state))
         (w state))
  :hints (("Goal" :in-theory (enable set-print-base-radix w))))
