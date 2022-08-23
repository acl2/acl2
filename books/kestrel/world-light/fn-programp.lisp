; A lightweight utility to test whether a function is in :program mode
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund fn-programp (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld)
                              (function-symbolp fn wrld))))
  (not (logicp fn wrld)))
