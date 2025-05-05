; Some tests of THM
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(thm t)
(thm 3) ; 3 is a non-nil constant
(thm '(3)) ; '(3) is a non-nil constant

(must-fail (thm nil))
(must-fail (thm 'nil))
(thm ''nil) ;since ''nil is a non-nil constant
