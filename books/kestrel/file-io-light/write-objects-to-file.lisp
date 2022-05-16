; A function to write a sequence of objects to a file
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Why does the resulting file always start with a blank line?

(include-book "write-objects-to-channel")
(local (include-book "std/io/base" :dir :system)) ;for reasoning support
(local (include-book "kestrel/utilities/state" :dir :system))

;move
(local
 (defthm get-serialize-character-of-mv-nth-1-of-open-output-channel
  (equal (get-serialize-character (mv-nth 1 (open-output-channel filename typ state)))
         (get-serialize-character state))
  :hints (("Goal" :in-theory (enable get-serialize-character open-output-channel
                                     update-open-output-channels
                                     get-global
                                     global-table
                                     update-file-clock)))))

;; Writes the OBJECTS to file FILENAME, overwriting its previous contents.
;; Returns (mv erp state).
(defun write-objects-to-file (objects filename ctx state)
  (declare (xargs :guard (and (true-listp objects)
                              (stringp filename)
                              ;; required by print-object$ (why?):
                              (member (get-serialize-character state)
                                      '(nil #\Y #\Z)))
                  :stobjs state))
  (mv-let (channel state)
    (open-output-channel filename :object state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :object output." filename)
                (mv t state))
      (pprogn (write-objects-to-channel objects channel state)
              (close-output-channel channel state)
              ;; no error:
              (mv nil state)))))
