; A lightweight book about the built-in function write-byte$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "channels"))
(local (include-book "open-output-channel-p"))

(in-theory (disable write-byte$))

(local (in-theory (disable open-output-channel-p
                           open-output-channel-p1)))

;; Avoids name clash with std
(defthm state-p1-of-write-byte$-alt
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :byte state) ; note the "p1"
                (unsigned-byte-p 8 byte) ;this is what's different
                )
           (state-p1 (write-byte$ byte channel state)))
  :hints (("Goal" :in-theory (enable write-byte$
                                     open-output-channel-p
                                     open-output-channel-p1))))

(defthm state-p-of-write-byte$
  (implies (and (state-p state)
                (open-output-channel-p channel :byte state)
                (unsigned-byte-p 8 byte))
           (state-p (write-byte$ byte channel state)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm open-output-channel-p1-of-write-byte$-gen
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (write-byte$ byte channel2 state)))
  :hints (("Goal" :in-theory (enable write-byte$ open-output-channel-p1))))

(defthm open-output-channel-p-of-write-byte$-gen
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (write-byte$ byte channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm open-output-channel-any-p1-of-write-byte$-gen
  (implies (open-output-channel-any-p1 channel state)
           (open-output-channel-any-p1 channel (write-byte$ byte channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p1))))

(defthm open-output-channel-any-p-of-write-byte$-gen
  (implies (open-output-channel-any-p channel state)
           (open-output-channel-any-p channel (write-byte$ byte channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))
