; A lightweight utility to test whether a function is defined
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also [books]/kestrel/std/system/definedp.lisp, but that doesn't support
;; :program mode functions.

;; Checks whether the function FN is defined (has a body).
(defund fn-definedp (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld)
                              (function-symbolp fn wrld))))
  (if (logicp fn wrld)
      ;; :logic mode, so check for unnormalized-body:
      (if (getpropc fn 'unnormalized-body nil wrld)
          t
        nil)
    ;; :program mode (have to handle predefined functions separately):
    (if (getpropc fn 'predefined nil wrld)
        ;; special case: predefined :program mode functions don't have the unnormalized-body property
        t ;; todo: check that all such functions are defined
      (if (getpropc fn 'unnormalized-body nil wrld)
          t
        nil))))
