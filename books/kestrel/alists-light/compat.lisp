; Check compatibility of this library with STD
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Makes sure we can include both this libary and std/alists without any name
;; clashes:
(include-book "std/alists/top" :dir :system)
(include-book "std/typed-alists/top" :dir :system)
(include-book "top")
