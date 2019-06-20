; A book that fixes some issues with arithmetic/top-with-meta.
;
; Copyright (C) 2016-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We include top-with-meta, which also brings in arithmetic/equalities and
;; arithmetic/inequalities:
(include-book "../../arithmetic/top-with-meta")

;; Now bring in the fixes for arithmetic/equalities:
(include-book "arithmetic-equalities")

;; Now bring in the fixes for arithmetic/inequalities:
(include-book "arithmetic-inequalities")
