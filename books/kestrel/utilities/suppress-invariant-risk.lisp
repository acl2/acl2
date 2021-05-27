; A utility to suppress invariant-risk slowdown
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Wrap this around a :program mode function to avoid invariant-risk slowdown
;; when it runs (TODO: Only applies when the function is called from the
;; top-level??).  You can also wrap this around a logic mode function to avoid
;; it being tagged as having invariant risk.
(defmacro suppress-invariant-risk (form)
  `(encapsulate ()
     (set-register-invariant-risk nil)
     ,form))
