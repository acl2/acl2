; A lightweight book about print-base-p
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; print-base-p is already disabled when ACL2 starts

(defthm print-base-p-forward
  (implies (print-base-p print-base)
           (and (integerp print-base)
                (<= 2 print-base)
                (<= print-base 16)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable print-base-p))))
