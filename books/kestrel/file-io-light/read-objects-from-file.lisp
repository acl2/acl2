; A lightweight function to read the ACL2 objects from a channel
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "read-objects-from-channel")
(local (include-book "open-input-channel"))
(local (include-book "close-input-channel"))

;; Returns (mv erp objects state) where either ERP is non-nil (meaning an error
;; occurred) or else OBJECTS are the ACL2 objects in the file.
;; The package used for symbols read from the file that don't have explicit
;; packages is the current package, but see read-objects-from-file-with-pkg.
(defund read-objects-from-file (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,filename) nil state)
      (mv-let (objects state)
        (read-objects-from-channel channel state)
        (let ((state (close-input-channel channel state)))
          (mv nil ; no error
              objects
              state))))))

(defthm state-p1-of-mv-nth-2-of-read-objects-from-file
  (implies (and (stringp filename)
                (state-p1 state))
           (state-p1 (mv-nth 2 (read-objects-from-file filename state))))
  :hints (("Goal" :in-theory (enable read-objects-from-file))))

(defthm state-p-of-mv-nth-2-of-read-objects-from-file
  (implies (and (stringp filename)
                (state-p state))
           (state-p (mv-nth 2 (read-objects-from-file filename state))))
  :hints (("Goal" :in-theory (enable state-p))))
