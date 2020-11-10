; Utilities dealing with redundant events
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pack")

;WHOLE-FORM is a call of the command, e.g, (prove-equivalence ...)
(defun command-is-redundantp (whole-form state)
  (declare (xargs :stobjs state
                  :guard (and (consp whole-form)
                              (symbolp (car whole-form)))))
  (let* ((command-name (car whole-form))
         (table-name (pack$ command-name "-TABLE"))
         (table-alist (table-alist table-name (w state))))
    (if (not (alistp table-alist))
        (er hard? 'command-is-redundantp "The table ~x0 is ill-formed.  Table-alist failed to return an alist, instead giving ~x1."
            table-name
            table-alist)
      (if (assoc-equal whole-form table-alist) ; the form must be identical
          (prog2$ (cw "NOTE: The command (~x0 ...) is redundant.~%" command-name)
                  t)
        nil))))
