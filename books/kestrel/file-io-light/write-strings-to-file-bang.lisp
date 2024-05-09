; A variant of write-strings-to-file that can be used in make-event, etc.
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-strings-to-channel")
(local (include-book "open-output-channel-bang"))
(local (include-book "kestrel/utilities/w" :dir :system))

(defttag file-io!)

(local (in-theory (disable w state-p
                           update-written-files
                           update-open-output-channels
                           update-file-clock)))

;; Writes the STRINGS to file FILENAME, overwriting its previous contents.
;; Effectively, all the STRINGS get concatenated and the result becomes the new
;; contents of the file.  Returns (mv erp state).  CTX is a context for error
;; printing.  The ttag is needed because this calls open-output-channel!, but
;; that makes this version usable during make-event expansion,
;; clause-processors, etc.
(defund write-strings-to-file! (strings filename ctx state)
  (declare (xargs :stobjs state
                  :guard (and (string-listp strings)
                              (stringp filename))))
  (mv-let (channel state)
    (open-output-channel! filename :character state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :character output." filename)
                (mv t state))
      (pprogn (write-strings-to-channel strings channel state)
              (close-output-channel channel state)
              (mv nil state)))))

(defthm w-of-mv-nth-1-of-write-strings-to-file!
  (equal (w (mv-nth 1 (write-strings-to-file! strings filename ctx state)))
         (w state))
  :hints (("Goal" :in-theory (enable write-strings-to-file!))))
