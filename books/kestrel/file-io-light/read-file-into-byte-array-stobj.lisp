; A lightweight function to read a file's bytes into a stobj array of bytes
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/byte-array-stobj" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
;; (include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "file-length-dollar"))
(local (include-book "open-input-channel"))
(local (include-book "read-byte-dollar"))
(local (include-book "kestrel/utilities/channels" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))

(local (in-theory (disable assoc-equal
                           channel-contents
                           open-input-channel-p
                           open-input-channel-p1
                           update-nth
                           nth
                           member-equal
                           open-input-channel-any-p1
                           mv-nth)))

;; Returns (mv byte-array-stobj state).
(defund read-file-into-byte-array-stobj-aux (next-index len channel byte-array-stobj state)
  (declare (xargs :guard (and (symbolp channel)
                              (unsigned-byte-p 59 next-index) ; so that adding 1 still gives a fixnum
                              (unsigned-byte-p 59 len)
                              (equal len (bytes-length byte-array-stobj))
                              (open-input-channel-p channel :byte state))
                  :stobjs (byte-array-stobj state)
                  :measure (nfix (+ 1 (- len next-index)))
                  :hints (("Goal" :in-theory (enable channel-contents)))
                  :guard-hints (("Goal" :in-theory (enable open-input-channel-p unsigned-byte-p)))
                  :split-types t)
           (type (unsigned-byte 59) len)
           (type (unsigned-byte 59) next-index))
  (if (or (not (mbt (and (natp next-index) (natp len))))
          (<= len next-index))
      (mv byte-array-stobj state)
    (mv-let (maybe-byte state)
      (read-byte$ channel state)
      (if (not maybe-byte) ; no more bytes
          (prog2$ (er hard? 'read-file-into-byte-array-stobj-aux "Too few bytes in file.") ; should not happen since LEN is the file length
                  (mv byte-array-stobj state))
        (let ((byte-array-stobj (update-bytesi next-index maybe-byte byte-array-stobj)))
          (read-file-into-byte-array-stobj-aux (the (unsigned-byte 60) (+ 1 next-index))
                                               len
                                               channel
                                               byte-array-stobj
                                               state))))))

(local
 (defthm state-p1-of-mv-nth-1-of-read-file-into-byte-array-stobj-aux
   (implies (and (symbolp channel)
                 (open-input-channel-p channel :byte state)
                 (state-p1 state))
            (state-p1 (mv-nth 1 (read-file-into-byte-array-stobj-aux next-index len channel byte-array-stobj state))))
   :hints (("Goal" :in-theory (enable read-file-into-byte-array-stobj-aux)))))

(local
 (defthm open-input-channel-p1-of-mv-nth-1-of-read-file-into-byte-array-stobj-aux
   (implies (and (symbolp channel)
                 (open-input-channel-p1 channel typ state)
                 (state-p1 state))
            (open-input-channel-p1 channel typ (mv-nth 1 (read-file-into-byte-array-stobj-aux next-index len channel byte-array-stobj state))))
   :hints (("Goal" :in-theory (enable read-file-into-byte-array-stobj-aux)))))

(local
 (defthm open-input-channel-any-p1-of-mv-nth-1-of-read-file-into-byte-array-stobj-aux
   (implies (and (symbolp channel)
                 (open-input-channel-any-p1 channel state)
                 (state-p1 state))
            (open-input-channel-any-p1 channel (mv-nth 1 (read-file-into-byte-array-stobj-aux next-index len channel byte-array-stobj state))))
   :hints (("Goal" :in-theory (enable open-input-channel-any-p1)))))

;; Returns (mv erp byte-array-stobj state) where either ERP is non-nil (meaning an error
;; occurred) or else the bytes field of BYTE-ARRAY-STOBJ contains the contents of FILENAME.
(defund read-file-into-byte-array-stobj (filename byte-array-stobj state)
  (declare (xargs :guard (stringp filename)
                  :guard-debug t
                  :stobjs (byte-array-stobj state)))
  ;; Get the file lenght so we know how big to make the array (or I suppose we
  ;; could resize the array when needed):
  (mv-let (file-length state)
    (file-length$ filename state)
    (if (not file-length)
        (mv `(:failed-to-get-file-length ,filename) byte-array-stobj state)
      (if (not (unsigned-byte-p 59 file-length)) ; we could weaken this check, but it lets the indexing use fixnums
          (mv `(:file-too-long ,filename) byte-array-stobj state)
        (mv-let (channel state)
          (open-input-channel filename :byte state)
          (if (not channel)
              ;; Error:
              (mv `(:could-not-open-channel ,filename) byte-array-stobj state)
            (let ( ;; make the array the right size:
                  (byte-array-stobj (resize-bytes file-length byte-array-stobj)))
              (mv-let (byte-array-stobj state)
                (read-file-into-byte-array-stobj-aux 0 (bytes-length byte-array-stobj) channel byte-array-stobj state)
                (let ((state (close-input-channel channel state)))
                  (mv nil ; no error
                      byte-array-stobj
                      state))))))))))
