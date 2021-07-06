; A function to write a sequence of bytes to a channel
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/io/base" :dir :system)) ;for reasoning support
(local (include-book "write-byte-dollar"))

(defun all-bytep (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (let ((item (first lst)))
        (and (natp item)
             (< item 256)
             (all-bytep (rest lst))))
    t))

;; Write the elements of BYTES to CHANNEL.  Returns STATE.
(defund write-bytes-to-channel (bytes channel state)
  (declare (xargs :stobjs state
                  :guard (and (all-bytep bytes)
                              (symbolp channel)
                              (open-output-channel-p channel :byte state))
                  :guard-hints (("Goal" :in-theory (enable open-output-channel-p)))))
  (if (atom bytes)
      state
    (pprogn (write-byte$ (car bytes) channel state)
            (write-bytes-to-channel (cdr bytes) channel state))))

(defthm open-output-channel-p1-of-write-bytes-to-channel
  (implies (open-output-channel-p1 channel2 typ state)
           (open-output-channel-p1 channel2 typ (write-bytes-to-channel bytes channel state)))
  :hints (("Goal" :in-theory (enable write-bytes-to-channel))))

(defthm state-p1-of-write-bytes-to-channel
  (implies (and (open-output-channel-p1 channel :byte state)
                (symbolp channel)
                (state-p1 state)
                (all-bytep list))
           (state-p1 (write-bytes-to-channel list channel state)))
  :hints (("Goal" :in-theory (enable write-bytes-to-channel))))
