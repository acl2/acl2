; Tests of hex-digit-chars-to-code-point
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "hex-digit-chars-to-code-point")

;; Test for the slash character (mentioned in ECMA 404, the JSON standard)
(assert!
 (mv-let (erp code-point)
   (hex-digit-chars-to-code-point #\0 #\0 #\2 #\F)
   (and (not erp)
        (equal code-point (char-code #\/)))))

;; Same as above but with lower case f
(assert!
 (mv-let (erp code-point)
   (hex-digit-chars-to-code-point #\0 #\0 #\2 #\f)
   (and (not erp)
        (equal code-point (char-code #\/)))))
