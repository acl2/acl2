; Utilities for making fresh symbols not defined in the given world
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

; Utilities for making fresh symbols with no properties in the given world
; (e.g., names of new functions or theorems)

(include-book "fresh-names")
(include-book "symbol-has-propsp")

(defun make-new-name-aux (num max base-name state)
  (declare (xargs :stobjs state
                  :measure (nfix (+ 1 max))
                  :guard (and (natp max)
                              (natp num))))
  (if (zp max)
      (hard-error 'make-new-name-aux "Could not find a fresh name/" nil)
    (let ((name-to-try (pack$ base-name '-fresh- num)))
      (if (symbol-has-propsp name-to-try state)
          (make-new-name-aux (+ 1 num) (+ -1 max) base-name state)
        name-to-try))))

;;this is really to make the new name of a function/theorem?!
(defun make-new-name (desired-name state)
  (declare (xargs :stobjs state
                  :guard (symbolp desired-name)))
  (if (not (symbol-has-propsp desired-name state))
      desired-name
    (make-new-name-aux 0 1000000 ;gross?
                       desired-name state)))

;;this is really to make the new name of a function/theorem?!
;takes state implicitly
(defmacro packnew (&rest rst)
  `(make-new-name (pack$ ,@rst) state))
