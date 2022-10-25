; A lightweight book about the built-in function char
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/nth" :dir :system))

(defthm characterp-of-char
  (equal (characterp (char s n))
         (and (stringp s)
              (< (nfix n) (length s))))
  :hints (("Goal" :cases ((characterp (nth n (coerce s 'list)))))))
