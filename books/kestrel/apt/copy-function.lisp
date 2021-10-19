; A transformation to copy a function
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book exists so that copy-function can be easily included in the
;; standard way (by including a book in apt/ that has the same name as the
;; desired transformation) without knowing where copy-function is actually
;; defined.

;; Copy function is actually defined here:
(include-book "utilities/def-equality-transformation")
