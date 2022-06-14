; Check compatibility with std
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Make sure we can include all of these libraries without errors:
(include-book "std/typed-lists/top" :dir :system)
(include-book "top")
(include-book "kestrel/fty/top" :dir :system)
