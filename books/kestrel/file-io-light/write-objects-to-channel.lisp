; A function to write a sequence of objects to a channel
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the function write-list in books/misc/file-io.lisp.

(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "print-object-dollar-fn"))
(local (include-book "print-object-dollar"))
(local (include-book "open-output-channel-p"))

(local (in-theory (disable open-output-channel-p open-output-channel-p1
                           print-object$-fn)))

;; Write each element of OBJECTS to CHANNEL, with a newline preceding each one.  Returns STATE.
(defund write-objects-to-channel-aux (objects channel state)
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
            (write-objects-to-channel-aux (cdr objects) channel state))))

(defthm open-output-channel-p1-of-write-objects-to-channel-aux
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (write-objects-to-channel-aux list channel2 state)))
  :hints (("Goal" :in-theory (enable write-objects-to-channel-aux))))

(defthm open-output-channel-p-of-write-objects-to-channel-aux
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (write-objects-to-channel-aux list channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm state-p1-of-write-objects-to-channel-aux
  (implies (and (open-output-channel-p1 channel :object state)
                (state-p1 state))
           (state-p1 (write-objects-to-channel-aux list channel state)))
  :hints (("Goal" :in-theory (enable write-objects-to-channel-aux
                                     open-output-channel-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns STATE.
(defund write-objects-to-channel (objects channel state)
  (declare (xargs :guard (and (true-listp objects)
                              (symbolp channel)
                              (open-output-channel-p channel :object state)
                              ;; required by print-object$ (why?):
                              (member (get-serialize-character state)
                                      '(nil #\Y #\Z)))
                  :guard-hints (("Goal" :in-theory (enable open-output-channel-p)))
                  :stobjs state))
  (if (endp objects)
      state
    (pprogn (print-object$+ (first objects) channel :header nil) ; suppresses initial newline
            (write-objects-to-channel-aux (rest objects) channel state))))

(defthm open-output-channel-p1-of-write-objects-to-channel
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (write-objects-to-channel list channel2 state)))
  :hints (("Goal" :in-theory (enable write-objects-to-channel))))

(defthm state-p1-of-write-objects-to-channel
  (implies (and (open-output-channel-p1 channel :object state)
                (state-p1 state))
           (state-p1 (write-objects-to-channel list channel state)))
  :hints (("Goal" :in-theory (enable write-objects-to-channel
                                     open-output-channel-p))))
