; A lightweight function to read a file's bytes into a stobj array of bytes
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also read-file-into-byte-array-stobj2.lisp, which might be faster.

(include-book "kestrel/utilities/byte-array-stobj" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
;; (include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "file-length-dollar"))
(local (include-book "open-input-channel"))
(local (include-book "open-input-channel-p"))
(local (include-book "read-byte-dollar"))
(local (include-book "channels"))
(local (include-book "kestrel/utilities/state" :dir :system))
;(local (include-book "kestrel/lists-light/cons" :dir :system))

(local (in-theory (disable assoc-equal
                           channel-contents
                           open-input-channel-p
                           open-input-channel-p1
                           update-nth
                           nth
                           member-equal
                           open-input-channel-any-p1
                           mv-nth)))

;; Copies bytes from CHANNEL into elements NEXT-INDEX through LIMIT-1 of the stobj array.
;; Returns (mv byte-array-stobj state).
;; TODO: Instead of limit, pass in a max-index or a num-bytes.
(defund read-bytes-into-byte-array-stobj (next-index limit channel byte-array-stobj state)
  (declare (xargs :guard (and (unsigned-byte-p 59 next-index) ; so that adding 1 still gives a fixnum
                              (unsigned-byte-p 59 limit)
                              (<= limit (bytes-length byte-array-stobj))
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :stobjs (byte-array-stobj state)
                  :measure (nfix (+ 1 (- limit next-index)))
                  :hints (("Goal" :in-theory (enable channel-contents)))
                  :guard-hints (("Goal" :in-theory (enable open-input-channel-p unsigned-byte-p)))
                  :split-types t)
           (type (unsigned-byte 59) limit next-index))
  (if (or (not (mbt (and (natp next-index) (natp limit))))
          (<= limit next-index))
      (mv byte-array-stobj state)
    (mv-let (maybe-byte state)
      (read-byte$ channel state)
      (if (not maybe-byte) ; no more bytes
          (prog2$ (er hard? 'read-bytes-into-byte-array-stobj "Too few bytes in file.") ; should not happen if LIMIT is the file length
                  (mv byte-array-stobj state))
        (let ((byte-array-stobj (update-bytesi next-index maybe-byte byte-array-stobj)))
          (read-bytes-into-byte-array-stobj (the (unsigned-byte 59) (+ 1 next-index))
                                            limit
                                            channel
                                            byte-array-stobj
                                            state))))))

(defthm bytes-length-of-mv-nth-0-of-read-bytes-into-byte-array-stobj
  (implies (and (natp next-index)
                (<= limit (bytes-length byte-array-stobj)))
           (equal (bytes-length (mv-nth 0 (read-bytes-into-byte-array-stobj next-index limit channel byte-array-stobj state)))
                  (bytes-length byte-array-stobj)))
  :hints (("Goal" :in-theory (enable read-bytes-into-byte-array-stobj))))

(local
 (defthm state-p1-of-mv-nth-1-of-read-bytes-into-byte-array-stobj
   (implies (and (open-input-channel-p channel :byte state) ; should this be open-input-channel-p1?
                 (state-p1 state))
            (state-p1 (mv-nth 1 (read-bytes-into-byte-array-stobj next-index limit channel byte-array-stobj state))))
   :hints (("Goal" :in-theory (enable read-bytes-into-byte-array-stobj open-input-channel-p)))))

(local
 (defthm open-input-channel-p1-of-mv-nth-1-of-read-bytes-into-byte-array-stobj
   (implies (and (open-input-channel-p1 channel typ state)
                 (state-p1 state))
            (open-input-channel-p1 channel typ (mv-nth 1 (read-bytes-into-byte-array-stobj next-index limit channel byte-array-stobj state))))
   :hints (("Goal" :in-theory (enable read-bytes-into-byte-array-stobj)))))

(local
 (defthm open-input-channel-any-p1-of-mv-nth-1-of-read-bytes-into-byte-array-stobj
   (implies (and (open-input-channel-any-p1 channel state)
                 (state-p1 state))
            (open-input-channel-any-p1 channel (mv-nth 1 (read-bytes-into-byte-array-stobj next-index limit channel byte-array-stobj state))))
   :hints (("Goal" :in-theory (enable open-input-channel-any-p1)))))

;; Returns (mv erp numbytes byte-array-stobj state) where either ERP is non-nil
;; (meaning an error occurred) or else the first NUMBYTES elements of the
;; bytes field of BYTE-ARRAY-STOBJ contain the contents of FILENAME.
(defund read-file-into-byte-array-stobj (filename byte-array-stobj state)
  (declare (xargs :guard (stringp filename)
                  :stobjs (byte-array-stobj state)))
  ;; Get the file length so we know how big to make the array (or I suppose we
  ;; could resize the array when needed):
  (mv-let (file-length state)
    (file-length$ filename state)
    (if (not file-length)
        (mv `(:failed-to-get-file-length ,filename) 0 byte-array-stobj state)
      (if (not (unsigned-byte-p 59 file-length)) ; we could weaken this check, but it lets the indexing use fixnums
          (mv `(:file-too-long ,filename) 0 byte-array-stobj state)
        (mv-let (channel state)
          (open-input-channel filename :byte state)
          (if (not channel)
              ;; Error:
              (mv `(:could-not-open-channel ,filename) 0 byte-array-stobj state)
            (let* (;; TODO: Consider reusing the array if it's already the
                   ;; right size (or perhaps larger, but in that case ensure that callers
                   ;; don't use the array length to mean the number of valid elements):
                   ;; Discard old contents, so the call to resize-bytes below doesn't copy them:
                   (byte-array-stobj (resize-bytes 0 byte-array-stobj))
                   ;; Make the array the right size:
                   (byte-array-stobj (resize-bytes file-length byte-array-stobj)))
              (mv-let (byte-array-stobj state)
                (read-bytes-into-byte-array-stobj 0 file-length channel byte-array-stobj state)
                (let ((state (close-input-channel channel state)))
                  (mv nil ; no error
                      file-length
                      byte-array-stobj
                      state))))))))))

(defthm natp-of-mv-nth-1-of-read-file-into-byte-array-stobj
  (natp (mv-nth 1 (read-file-into-byte-array-stobj filename byte-array-stobj state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-file-into-byte-array-stobj))))

(defthm <=-of-mv-nth-1-of-read-file-into-byte-array-stobj-and-byte-length-of-mv-nth-2-of-read-file-into-byte-array-stobj
  (<= (mv-nth 1 (read-file-into-byte-array-stobj filename byte-array-stobj state))
      (bytes-length (mv-nth 2 (read-file-into-byte-array-stobj filename byte-array-stobj state))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable read-file-into-byte-array-stobj))))
