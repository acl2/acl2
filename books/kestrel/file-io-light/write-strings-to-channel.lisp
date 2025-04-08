; A function to write a sequence of strings to a channel
;
; Copyright (C) 2017-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "princ-dollar"))

(local (in-theory (disable open-output-channel-p1 open-output-channel-p)))

;; Returns state.
(defund write-strings-to-channel (strings channel state)
  (declare (xargs :guard (and (string-listp strings)
                              (symbolp channel)
                              (open-output-channel-p channel :character state))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable open-output-channel-p)))))
  (if (endp strings)
      state
    (pprogn (princ$ (car strings) channel state) ;todo: call something faster? (e.g., something that only works for strings)?
            (write-strings-to-channel (cdr strings) channel state))))

(defthm state-p1-of-write-strings-to-channel
  (implies (and (state-p1 state)
                (open-output-channel-p channel :character state))
           (state-p1 (write-strings-to-channel strings channel state)))
  :hints (("Goal" :in-theory (enable write-strings-to-channel))))

(defthm state-p-of-write-strings-to-channel
  (implies (and (state-p state)
                (open-output-channel-p channel :character state))
           (state-p (write-strings-to-channel strings channel state))))

(defthm open-output-channel-p1-of-write-strings-to-channel
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (write-strings-to-channel strings channel2 state)))
  :hints (("Goal" :in-theory (enable write-strings-to-channel))))

(defthm open-output-channel-p-of-write-strings-to-channel
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (write-strings-to-channel strings channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm open-output-channel-any-p1-of-write-strings-to-channel
  (implies (open-output-channel-any-p1 channel state)
           (open-output-channel-any-p1 channel (write-strings-to-channel strings channel2 state))))

(defthm open-output-channel-any-p-of-write-strings-to-channel
  (implies (open-output-channel-any-p channel state)
           (open-output-channel-any-p channel (write-strings-to-channel strings channel2 state))))

(defthm w-of-write-strings-to-channel
  (equal (w (write-strings-to-channel strings channel state))
         (w state))
  :hints (("Goal" :in-theory (e/d (write-strings-to-channel) (w)))))
