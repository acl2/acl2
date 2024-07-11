; A lightweight function to read a file's contents into a list of bytes
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also std/io/read-file-bytes.lisp.

(include-book "read-bytes-from-channel")
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
(local (include-book "open-input-channel"))
(local (include-book "close-input-channel"))

;; Returns (mv erp bytes state) where either ERP is non-nil (meaning an error
;; occurred) or else BYTES is the contents of the file indicated by
;; PATH-TO-FILE.  If PATH-TO-FILE is a relative path, it is interpreted
;; relative to the CBD.
(defund read-file-into-byte-list (path-to-file state)
  (declare (xargs :guard (stringp path-to-file)
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel path-to-file :byte state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,path-to-file) nil state)
      (mv-let (bytes state)
        (read-bytes-from-channel channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv nil ; no error
              bytes
              state))))))

(defthm unsigned-byte-listp-of-mv-nth-1-of-read-file-into-byte-list
  (unsigned-byte-listp 8 (mv-nth 1 (read-file-into-byte-list path-to-file state)))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list))))

(defthm true-listp-of-mv-nth-1-of-read-file-into-byte-list-type
  (true-listp (mv-nth 1 (read-file-into-byte-list path-to-file state)))
  :rule-classes :type-prescription
  :hints (("Goal" :use unsigned-byte-listp-of-mv-nth-1-of-read-file-into-byte-list
           :in-theory (disable unsigned-byte-listp-of-mv-nth-1-of-read-file-into-byte-list))))

(defthm state-p1-of-mv-nth-2-of-read-file-into-byte-list
  (implies (and (stringp path-to-file)
                (state-p1 state))
           (state-p1 (mv-nth 2 (read-file-into-byte-list path-to-file state))))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list))))

(defthm state-p-of-mv-nth-2-of-read-file-into-byte-list
  (implies (and (stringp path-to-file)
                (state-p state))
           (state-p (mv-nth 2 (read-file-into-byte-list path-to-file state)))))
