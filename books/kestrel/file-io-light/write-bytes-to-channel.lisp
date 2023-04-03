; A function to write a sequence of bytes to a channel
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "write-byte-dollar"))
(local (include-book "channels"))
(local (include-book "open-output-channel-p"))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (disable state-p state-p1
                           open-output-channels ; not done by a library?
                           open-output-channel-p1
                           )))

;; todo: use something else?
(defun all-bytep (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (let ((item (first lst)))
        (and (natp item)
             (< item 256)
             (all-bytep (rest lst))))
    t))

;; Writes the BYTES to CHANNEL.  Returns STATE.
(defund write-bytes-to-channel (bytes channel state)
  (declare (xargs :stobjs state
                  :guard (and (all-bytep bytes)
                              (symbolp channel)
                              (open-output-channel-p channel :byte state))))
  (if (atom bytes)
      state
    (pprogn (write-byte$ (car bytes) channel state)
            (write-bytes-to-channel (cdr bytes) channel state))))

(defthm open-output-channel-p1-of-write-bytes-to-channel
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (write-bytes-to-channel bytes channel2 state)))
  :hints (("Goal" :in-theory (enable write-bytes-to-channel))))

(defthm open-output-channel-p-of-write-bytes-to-channel
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (write-bytes-to-channel bytes channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm open-output-channel-any-p1-of-write-bytes-to-channel
  (implies (open-output-channel-any-p1 channel state)
           (open-output-channel-any-p1 channel (write-bytes-to-channel bytes channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p1))))

(defthm open-output-channel-any-p-of-write-bytes-to-channel
  (implies (open-output-channel-any-p channel state)
           (open-output-channel-any-p channel (write-bytes-to-channel bytes channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p))))

(defthm state-p1-of-write-bytes-to-channel
  (implies (and (open-output-channel-p1 channel :byte state)
                (state-p1 state)
                (all-bytep list))
           (state-p1 (write-bytes-to-channel list channel state)))
  :hints (("Goal" :in-theory (enable write-bytes-to-channel))))

(defthm state-p-of-write-bytes-to-channel
  (implies (and (open-output-channel-p channel :byte state)
                (state-p state)
                (all-bytep list))
           (state-p (write-bytes-to-channel list channel state)))
  :hints (("Goal" :in-theory (enable write-bytes-to-channel))))
