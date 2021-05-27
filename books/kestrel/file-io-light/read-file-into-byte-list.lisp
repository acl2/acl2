; A lightweight function to read a file's contents into a list of bytes
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
;; (include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "open-input-channel"))
(local (include-book "kestrel/utilities/channels" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "read-byte-dollar"))
(local (include-book "kestrel/lists-light/cons" :dir :system))

(local (in-theory (disable assoc-equal
                           channel-contents
                           open-input-channels
                           state-p)))

;; Returns (mv bytes state).
(defund read-file-into-byte-list-aux (channel acc state)
  (declare (xargs :guard (and (symbolp channel)
                              (open-input-channel-p channel :byte state)
                              (true-listp acc))
                  :stobjs state
                  :measure (len (cddr (assoc-equal channel (open-input-channels state))) ;;(channel-contents channel state)
                                )
                  :hints (("Goal" :in-theory (enable channel-contents)))
                  :guard-hints (("Goal" :in-theory (enable open-input-channel-p
                                                           )))))
  (if (not (mbt (and (open-input-channel-p channel :byte state) ; for termination
                     (state-p state))))
      (mv nil state)
    (mv-let (maybe-byte state)
      (read-byte$ channel state)
      (if (not maybe-byte)
          (mv (reverse acc) state)
        (read-file-into-byte-list-aux channel (cons maybe-byte acc) state)))))

(defthm state-p1-of-mv-nth-1-of-read-file-into-byte-list-aux
  (implies (and (symbolp channel)
                (open-input-channel-p channel :byte state)
                ;; (true-listp acc)
                (state-p1 state))
           (state-p1 (mv-nth 1 (read-file-into-byte-list-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list-aux
                                     open-input-channel-p
                                     open-input-channel-p1))))

;; (defthm state-p-of-mv-nth-1-of-read-file-into-byte-list-aux
;;   (implies (and (symbolp channel)
;;                 (open-input-channel-p channel :byte state)
;;                 ;; (true-listp acc)
;;                 (state-p state))
;;            (state-p (mv-nth 1 (read-file-into-byte-list-aux channel acc state))))
;;   :hints (("Goal" :in-theory (enable state-p))))

;todo
;; (defthm open-input-channels-of-mv-nth-1-of-read-file-into-byte-list-aux
;;   (implies (and (symbolp channel)
;;                 ;(open-input-channel-p channel typ state)
;;                 ;; (true-listp acc)
;;                 (state-p1 state))
;;            (equal (open-input-channels (mv-nth 1 (read-file-into-byte-list-aux channel acc state)))
;;                   (open-input-channels state)))
;;   :hints (("Goal" :in-theory (enable read-file-into-byte-list-aux
;;                                      open-input-channel-p
;;                                      open-input-channel-p1
;;                                      channel-contents))))

(defthm true-listp-of-mv-nth-0-of-read-file-into-byte-list-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 0 (read-file-into-byte-list-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list-aux
                                     open-input-channel-p
                                     open-input-channel-p1))))

(defthm unsigned-byte-listp-of-mv-nth-0-of-read-file-into-byte-list-aux
  (implies (unsigned-byte-listp 8 acc)
           (unsigned-byte-listp 8 (mv-nth 0 (read-file-into-byte-list-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list-aux
                                     open-input-channel-p
                                     open-input-channel-p1
                                     UNSIGNED-BYTE-LISTP))))

(defthm open-input-channel-p1-of-mv-nth-1-of-read-file-into-byte-list-aux
  (implies (and (symbolp channel)
                (open-input-channel-p channel typ state)
                ;; (true-listp acc)
                (state-p1 state))
           (open-input-channel-p1 channel typ (mv-nth 1 (read-file-into-byte-list-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list-aux
                                     open-input-channel-p
                                     open-input-channel-p1))))



;; Returns (mv erp bytes state) where either ERP is non-nil (meaning an error
;; occurred) or else BYTES is the contents of FILENAME.
(defund read-file-into-byte-list (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :byte state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,filename) nil state)
      (if ;; This check is needed for the guard of close-input-channel (can
          ;; this ever happen?):
          (member-eq channel
                     '(acl2-input-channel::standard-character-input-0
                       acl2-input-channel::standard-object-input-0))
          ;; Error:
          (mv `(:bad-channel ,filename) nil state)
        (mv-let (bytes state)
          (read-file-into-byte-list-aux channel nil state)
          (let ((state (close-input-channel channel state)))
            (mv nil ; no error
                bytes
                state)))))))

(defthm unsigned-byte-listp-of-mv-nth-1-of-read-file-into-byte-list
  (unsigned-byte-listp 8 (mv-nth 1 (read-file-into-byte-list filename state)))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list))))

(defthm true-listp-of-mv-nth-1-of-read-file-into-byte-list-type
  (true-listp (mv-nth 1 (read-file-into-byte-list filename state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-file-into-byte-list))))

(defthm state-p-of-mv-nth-2-of-read-file-into-byte-list
  (implies (and (stringp filename)
                (state-p state))
           (state-p (mv-nth 2 (read-file-into-byte-list filename state))))
  :hints (("Goal" :in-theory (enable read-file-into-byte-list state-p))))
