; Testing whether a file is newer than a given date/time
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Tests whether the file at ABSOLUTE-PATH exists and is newer than the given DATE.
;; Returns (mv result state).
(defund file-is-newer-thanp (absolute-path date state)
  (declare (xargs :guard (and (stringp absolute-path)
                              (integerp date))
                  :stobjs state))
  (mv-let (file-date state)
    (file-write-date$ absolute-path state)
    (if (not file-date)
        (mv nil state) ; file doesn't seem to exist
      ;; TODO: Consider considering a file with the same
      ;; write-date (down to the second) to be 'newer' for these
      ;; purposes, since one was likely created immediately after
      ;; the other during the same build.  Or, can we get a
      ;; version of file-write-date$ that is more fine grained?
      (mv (> file-date date) state))))
