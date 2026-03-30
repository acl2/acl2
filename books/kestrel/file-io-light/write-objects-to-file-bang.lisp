; A variant of write-objects-to-file for use during make-event, etc.
;
; Copyright (C) 2017-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "write-objects-to-channel")
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "open-output-channel-bang"))
(local (include-book "close-output-channel"))

(defttag file-io!)

(local (in-theory (disable open-output-channel-p1 put-global)))

;; Writes the OBJECTS to FILENAME, each on a separate line, overwriting the
;; previous contents of FILENAME.  Returns (mv erp state).  The ttag is needed
;; because this calls open-output-channel!, but that makes this version usable
;; during make-event expansion, clause-processors, etc.
(defund write-objects-to-file! (objects filename ctx state)
  (declare (xargs :stobjs state
                  :guard (and (true-listp objects)
                              (stringp filename))))
  (mv-let (channel state)
    (open-output-channel! filename :object state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :object output." filename)
                (mv t state))
      (pprogn (write-objects-to-channel objects channel state)
              (close-output-channel channel state)
              (mv nil state)))))

(defthm state-p1-of-mv-nth-1-of-write-objects-to-file!
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (write-objects-to-file! objects filename ctx state))))
  :hints (("Goal" :in-theory (enable write-objects-to-file! open-output-channel-p))))

(defthm state-p-of-mv-nth-1-of-write-objects-to-file!
  (implies (state-p state)
           (state-p (mv-nth 1 (write-objects-to-file! objects filename ctx state))))
  :hints (("Goal" :in-theory (enable write-objects-to-file! open-output-channel-p))))

(defthm w-of-mv-nth-1-of-write-objects-to-file!
  (equal (w (mv-nth 1 (write-objects-to-file! objects filename ctx state)))
         (w state))
  :hints (("Goal" :in-theory (enable write-objects-to-file!))))
