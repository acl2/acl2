; Tests of setenv$-event
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "setenv-dollar-event")
(include-book "std/testing/assert-bang-stobj" :dir :system)

(setenv$-event "foo" "bar")

;; Checks that "bar" got stored as the value of "foo":
(assert!-stobj
 (mv-let (erp val state)
   (getenv$ "foo" state)
   (mv (and (null erp)
            (equal val "bar"))
       state))
 state)
