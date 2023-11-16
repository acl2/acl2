; A lightweight function to read a channel's contents into a list of bytes
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
(local (include-book "read-byte-dollar"))

(local (in-theory (disable assoc-equal
                           channel-contents
                           open-input-channels)))

;; Returns (mv bytes state).
(defund read-bytes-from-channel (channel acc state)
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
        (read-bytes-from-channel channel (cons maybe-byte acc) state)))))

(defthm state-p1-of-mv-nth-1-of-read-bytes-from-channel
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (read-bytes-from-channel channel acc state))))
  :hints (("Goal" :in-theory (enable read-bytes-from-channel))))

(defthm state-p-of-mv-nth-1-of-read-bytes-from-channel
  (implies (state-p state)
           (state-p (mv-nth 1 (read-bytes-from-channel channel acc state)))))

;todo
;; (defthm open-input-channels-of-mv-nth-1-of-read-bytes-from-channel
;;   (implies (and
;;                 ;(open-input-channel-p channel typ state)
;;                 ;; (true-listp acc)
;;                 (state-p1 state))
;;            (equal (open-input-channels (mv-nth 1 (read-bytes-from-channel channel acc state)))
;;                   (open-input-channels state)))
;;   :hints (("Goal" :in-theory (enable read-bytes-from-channel
;;                                      open-input-channel-p
;;                                      open-input-channel-p1
;;                                      channel-contents))))

(defthm true-listp-of-mv-nth-0-of-read-bytes-from-channel
  (implies (true-listp acc)
           (true-listp (mv-nth 0 (read-bytes-from-channel channel acc state))))
  :hints (("Goal" :in-theory (enable read-bytes-from-channel))))

(defthm unsigned-byte-listp-of-mv-nth-0-of-read-bytes-from-channel
  (implies (unsigned-byte-listp 8 acc)
           (unsigned-byte-listp 8 (mv-nth 0 (read-bytes-from-channel channel acc state))))
  :hints (("Goal" :in-theory (enable read-bytes-from-channel
                                     unsigned-byte-listp))))

(defthm open-input-channel-p1-of-mv-nth-1-of-read-bytes-from-channel
  (implies (open-input-channel-p1 channel typ state)
           (open-input-channel-p1 channel typ (mv-nth 1 (read-bytes-from-channel channel2 acc state))))
  :hints (("Goal" :in-theory (enable read-bytes-from-channel))))
