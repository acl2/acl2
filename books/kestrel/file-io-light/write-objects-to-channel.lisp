; A function to write a sequence of objects to a channel
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/io/base" :dir :system)) ;for reasoning support
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "print-object-dollar"))

;; Write the elements of OBJECTS to CHANNEL.  Returns STATE.
(defund write-objects-to-channel (objects channel state)
  (declare (xargs :stobjs state
                  :guard (and (true-listp objects)
                              (symbolp channel)
                              (open-output-channel-p channel :object state)
                              ;; required by print-object$ (why?):
                              (member (get-serialize-character state)
                                      '(nil #\Y #\Z)))
                  :guard-hints (("Goal" :in-theory (enable open-output-channel-p)))))
  (if (atom objects)
      state
    (pprogn (print-object$ (car objects) channel state)
            (write-objects-to-channel (cdr objects) channel state))))

(defthm open-output-channel-p1-of-write-objects-to-channel
  (implies (open-output-channel-p1 channel2 typ state)
           (open-output-channel-p1 channel2 typ (write-objects-to-channel list channel state)))
  :hints (("Goal" :in-theory (enable write-objects-to-channel))))

(defthm state-p1-of-write-objects-to-channel
  (implies (and (open-output-channel-p1 channel :object state)
                (symbolp channel)
                (state-p1 state))
           (state-p1 (write-objects-to-channel list channel state)))
  :hints (("Goal" :in-theory (enable write-objects-to-channel))))
