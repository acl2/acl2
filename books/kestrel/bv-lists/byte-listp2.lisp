; More rules about byte-listp
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book mixes byte-listp with other non-built-in functions.

(include-book "byte-listp-def")
(include-book "kestrel/lists-light/repeat-def" :dir :system)

;avoid name clash with std
(defthm byte-listp-of-repeat-strong
  (equal (byte-listp (repeat n x))
         (or (bytep x)
             (zp n)))
  :hints (("Goal" :in-theory (enable byte-listp repeat))))
