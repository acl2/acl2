; A lightweight book about the built-in operations + and -.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that DISTRIBUTIVITY-OF-MINUS-OVER-+ and INVERSE-OF-+ are built in to
;; ACL2.

(defthm +-of-+-of---same
  (equal (+ x (- x) y)
         (fix y)))
