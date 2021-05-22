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
(local (include-book "read-object"))

(local (in-theory (disable UPDATE-OPEN-INPUT-CHANNELS
                           OPEN-INPUT-CHANNELS
                           OPEN-INPUT-CHANNEL-ANY-P1
                           read-object)))

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
      (if ;; This check is needed for the guard of close-input-channel (can
          ;; this ever happen?):
          (member-eq channel
                     '(acl2-input-channel::standard-object-input-0
                       acl2-input-channel::standard-character-input-0))
          ;; Error:
          (mv `(:bad-channel ,filename) nil state)
        (mv-let (eof maybe-object state)
          (read-object channel state)
          (let ((state (close-input-channel channel state)))
            (if eof
                ;; Error (no objects in file):
                (mv `(:end-of-file ,filename) nil state)
              (mv nil ; no error
                  maybe-object
                  state))))))))
