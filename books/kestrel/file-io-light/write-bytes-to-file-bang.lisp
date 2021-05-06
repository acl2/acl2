; A variant of write-bytes-to-file for use during make-event, etc.
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-bytes-to-channel")
(local (include-book "std/io/base" :dir :system)) ;for reasoning support

(defttag file-io!)

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
      (if (eq channel 'acl2-output-channel::standard-character-output-0) ;todo: prove that this doesn't happen
          (prog2$ (er hard? ctx "Unexpected output channel name: ~x0." channel)
                  (mv t state))
        (pprogn (write-bytes-to-channel bytes channel state)
                (close-output-channel channel state)
                (mv nil state))))))
