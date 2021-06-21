; Tests for make-term-into-dag-array-basic, etc.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-term-into-dag-array-basic")

(assert-event
 (mv-let (erp dag-or-quotep)
   (make-term-into-dag-basic '(foo a b) nil)
   (and (not erp)
        (equal dag-or-quotep '((2 FOO 0 1) (1 . B) (0 . A))))))

(assert-event
 (mv-let (erp dag-or-quotep)
   (make-term-into-dag-basic '(if 't '3 (foo a b)) nil)
   (and (not erp)
        (equal dag-or-quotep ''3))))
