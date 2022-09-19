; A variant of write-bytes-to-file for use during make-event, etc.
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-bytes-to-channel")
(local (include-book "open-output-channel-bang"))
(local (include-book "kestrel/utilities/w" :dir :system))

;; Needed because we call open-output-channel! below:
(defttag file-io!)

(local (in-theory (disable update-written-files
                           update-open-output-channels
                           update-file-clock)))

;; Writes the BYTES to file FILENAME, overwriting its previous contents.
;; Returns (mv erp state).  The ttag is needed because this calls
;; open-output-channel!, but that makes this version usable during make-event
;; expansion, clause-processors, etc.
(defun write-bytes-to-file! (bytes filename ctx state)
  (declare (xargs :stobjs state
                  :guard (and (all-bytep bytes)
                              (stringp filename))))
  (mv-let (channel state)
    (open-output-channel! filename :byte state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :byte output." filename)
                (mv t state))
      (pprogn (write-bytes-to-channel bytes channel state)
              (close-output-channel channel state)
              (mv nil state)))))
