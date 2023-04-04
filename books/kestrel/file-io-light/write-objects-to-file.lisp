; A function to write a sequence of objects to a file
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-objects-to-channel")
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/get-serialize-character" :dir :system))
(local (include-book "open-output-channel"))

(local (in-theory (disable put-global
                           open-output-channel-p1
                           open-output-channel-p)))

;; Writes the OBJECTS to FILENAME, each on a separate line, overwriting the
;; previous contents of FILENAME.  Returns (mv erp state).
(defund write-objects-to-file (objects filename ctx state)
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
