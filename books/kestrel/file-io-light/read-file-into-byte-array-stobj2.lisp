; A variant of read-file-into-byte-array-stobj.lisp
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also read-file-into-byte-array-stobj.lisp, but the utility in this file
;; might be faster, because it uses read-file-into-string.

(include-book "kestrel/utilities/byte-array-stobj" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
(local (include-book "kestrel/strings-light/char" :dir :system))
(local (include-book "kestrel/utilities/char-code" :dir :system))
(local (include-book "file-length-dollar"))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(local (in-theory (disable nth
                           char
                           read-file-into-string2
                           mv-nth)))

(defund write-string-chars-to-byte-array-stobj (index len str byte-array-stobj)
  (declare (xargs :guard (and (unsigned-byte-p 60 index)
                              (stringp str)
                              (unsigned-byte-p 60 len)
                              (<= len (length str))
                              (<= len (bytes-length byte-array-stobj)))
                  :stobjs byte-array-stobj
                  :measure (nfix (+ 1 (- len index)))
                  :split-types t)
           (type (unsigned-byte 60) index len)
           (type string str))
  (if (or (not (mbt (and (natp index) (natp len))))
          (>= index len))
      byte-array-stobj
    (let ((byte-array-stobj (update-bytesi index (char-code (char str index)) byte-array-stobj)))
      (write-string-chars-to-byte-array-stobj (the (unsigned-byte 60) (+ 1 index)) len str byte-array-stobj))))

;; Returns (mv erp byte-array-stobj state) where either ERP is non-nil (meaning an error
;; occurred) or else the bytes field of BYTE-ARRAY-STOBJ contains the contents of FILENAME.
(defund read-file-into-byte-array-stobj2 (filename byte-array-stobj state)
  (declare (xargs :guard (stringp filename)
                  :stobjs (byte-array-stobj state)))
  ;; Get the file lenght so we know how big to make the array (or I suppose we
  ;; could resize the array when needed):
  (mv-let (file-length state)
    (file-length$ filename state)
    (if (not file-length)
        (mv `(:failed-to-get-file-length ,filename) byte-array-stobj state)
      (if (not (unsigned-byte-p 59 file-length)) ; we could weaken this check, but it lets the indexing use fixnums
          (mv `(:file-too-long ,filename) byte-array-stobj state)
        (let ((str (read-file-into-string2 filename 0 nil :default state)))
          (if (or (not str)
                  (< (length str) file-length))
              (mv :error-reading-file byte-array-stobj state)
            (let* (;; make the array the right size:
                   (byte-array-stobj (resize-bytes file-length byte-array-stobj))
                   (byte-array-stobj (write-string-chars-to-byte-array-stobj 0 file-length str byte-array-stobj)))
              (mv nil ; no error
                  byte-array-stobj
                  state))))))))
