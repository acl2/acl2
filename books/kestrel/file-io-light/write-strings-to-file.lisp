; A function to write a sequence of strings to a file
;
; Copyright (C) 2017-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-strings-to-channel")
(local (include-book "close-output-channel"))
(local (include-book "open-output-channel"))

;; Writes the STRINGS to FILENAME, overwriting its previous contents.
;; Effectively, all the STRINGS get concatenated and the result becomes the new
;; contents of the file.  Returns (mv erp state).  CTX is a context for error
;; printing.
(defund write-strings-to-file (strings filename ctx state)
  (declare (xargs :guard (and (string-listp strings)
                              (stringp filename))
                  :stobjs state))
  (mv-let (channel state)
    (open-output-channel filename :character state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :character output." filename)
                (mv t state))
      (if (eq channel 'acl2-output-channel::standard-character-output-0) ;todo: prove that this doesn't happen
          (prog2$ (er hard? ctx "Unexpected output channel name: ~x0." channel)
                  (mv t state))
        (pprogn (write-strings-to-channel strings channel state)
                (close-output-channel channel state)
                (mv nil state))))))

(defthm state-p1-of-mv-nth-1-of-write-strings-to-file
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (write-strings-to-file strings filename ctx state))))
  :hints (("Goal" :in-theory (enable write-strings-to-file open-output-channel-p))))

(defthm state-p-of-mv-nth-1-of-write-strings-to-file
  (implies (state-p state)
           (state-p (mv-nth 1 (write-strings-to-file strings filename ctx state))))
  :hints (("Goal" :in-theory (enable write-strings-to-file open-output-channel-p))))

(defthm w-of-mv-nth-1-of-write-strings-to-file
  (equal (w (mv-nth 1 (write-strings-to-file strings filename ctx state)))
         (w state))
  :hints (("Goal" :in-theory (e/d (write-strings-to-file) (w)))))
