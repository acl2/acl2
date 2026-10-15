; Theorems mixing strip-cdrs with non-built-in functions
;
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also strip-cdrs.lisp.

(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm strip-cdrs-of-reverse-list
  (equal (strip-cdrs (reverse-list x))
         (reverse-list (strip-cdrs x)))
  :hints (("Goal" :in-theory (enable reverse-list))))
