; A function to write a sequence of bytes to a file
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-bytes-to-channel")
(local (include-book "open-output-channel"))
(local (include-book "close-output-channel"))
(local (include-book "channels"))

(local (in-theory (disable state-p)))

;; Writes the BYTES to file FILENAME, overwriting its previous contents.
;; Returns (mv erp state).
(defund write-bytes-to-file (bytes filename ctx state)
  (declare (xargs :guard (and (all-bytep bytes)
                              (stringp filename))
                  :stobjs state))
  (mv-let (channel state)
    (open-output-channel filename :byte state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :byte output." filename)
                (mv t state))
      (pprogn (write-bytes-to-channel bytes channel state)
              (close-output-channel channel state)
              ;; no error:
              (mv nil state)))))

(defthm state-p1-of-mv-nth-1-of-write-bytes-to-file
  (implies (and (all-bytep bytes) ; rephrase?
                (state-p1 state))
           (state-p1 (mv-nth 1 (write-bytes-to-file bytes filename ctx state))))
  :hints (("Goal" :in-theory (enable write-bytes-to-file))))

(defthm state-p-of-mv-nth-1-of-write-bytes-to-file
  (implies (and (all-bytep bytes) ;  rephrase?
                (state-p state))
           (state-p (mv-nth 1 (write-bytes-to-file bytes filename ctx state)))))
