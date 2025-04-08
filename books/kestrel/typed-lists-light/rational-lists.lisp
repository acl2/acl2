; Mixed rules about functions/predicates over rational lists
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-less")
(include-book "all-less-than-or-equal")

;; todo: make a cheap version?
(defthm all-<=-when-all-<
  (implies (all-< x n)
           (all-<= x n))
  :hints (("Goal" :in-theory (enable all-< all-<=))))
