; A lightweight function to read an object from a file
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "open-input-channel"))

;; Returns (mv erp object state) where either ERP is non-nil (meaning an error
;; occurred) or else OBJECT is the first Lisp object in the file.
;; TODO: Add option to set the package of the symbols read in?
(defun read-object-from-file (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,filename) nil state)
      (mv-let (eof maybe-object state)
        (read-object channel state)
        (if eof
            ;; Error (no objects in file):
            (mv `(:end-of-file ,filename) nil state)
          (mv nil ; no error
              maybe-object
              state))))))
