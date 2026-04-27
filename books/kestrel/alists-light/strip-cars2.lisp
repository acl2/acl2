; Theorems mixing strip-cars with non-built-in functions
;
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm strip-cars-of-reverse-list
  (equal (strip-cars (reverse-list x))
         (reverse-list (strip-cars x)))
  :hints (("Goal" :in-theory (enable reverse-list))))
