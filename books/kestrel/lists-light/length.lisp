; A lightweight book about the built-in function length
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We prefer to reason about len instead of length, since len doesn't have to
;; handle strings.  But length is much faster than len, so it may appear in
;; code.  An alternative to this could be to leave length enabled.
(defthm length-becomes-len
  (implies (not (stringp x))
           (equal (length x)
                  (len x))))
