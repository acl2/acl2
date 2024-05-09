; A version of setenv$ that is an event
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Sets the value of the environment variable VAR to the string VAL.
;; Note: This only seems to affect VAR within a book.
(defmacro setenv$-event (var val)
  `(value-triple (setenv$ ,var ,val)))

;; Example: (setenv$-event "foo" "bar")
