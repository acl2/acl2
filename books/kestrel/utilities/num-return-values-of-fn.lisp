; A utility to get the number of return values of a function
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns the number of return values (in the sense of MV) of FN.
(defund num-return-values-of-fn (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (not (member-eq fn *stobjs-out-invalid*))
                              (plist-worldp wrld))))
  (len (stobjs-out fn wrld)))
