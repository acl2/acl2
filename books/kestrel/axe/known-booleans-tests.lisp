; Tests of the known-booleans machinery
;
; Copyright (C) 2016-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/eval" :dir :system) ;for ensure-soft-error
(include-book "known-booleans")

(defun foo1 (x y z)
  (if (< x (+ y z))
      t
    nil))

(add-known-boolean foo1)
(add-known-boolean foo1) ;okay to do it twice

(ensure-soft-error (add-known-boolean len)) ; len does not return a boolean

(ensure-soft-error (add-known-boolean dfdfdg)) ;undefined function

(ensure-soft-error (add-known-boolean translate)) ; not in logic mode
