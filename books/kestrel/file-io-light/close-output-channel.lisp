; Rules about close-output-channel
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "channels"))
(local (include-book "kestrel/utilities/state" :dir :system))

(in-theory (disable close-output-channel))

;todo: move to channels.lisp, but that depends on this so first separate out the basic stuff in this book
(defthm state-p1-of-close-output-channel-when-open-output-channel-p1
  (implies (and (open-output-channel-p1 channel typ state) ;typ is a free var
                (member-equal typ *file-types*)
                (state-p1 state))
           (state-p1 (close-output-channel channel state)))
  :hints (("Goal" :in-theory (enable close-output-channel
                                     stringp-of-caddr-when-channel-headerp
                                     integerp-of-cadddr-when-channel-headerp
                                     integerp-when-file-clock-p))))

;avoids free var
(defthm state-p1-of-close-output-channel
  (implies (and (open-output-channel-any-p1 channel state)
                (state-p1 state))
           (state-p1 (close-output-channel channel state)))
  :hints (("Goal" :in-theory (e/d (open-output-channel-any-p1)
                                  (open-output-channel-p1)))))

(defthm state-p-of-close-output-channel
  (implies (and (open-output-channel-any-p1 channel state)
                (state-p state))
           (state-p (close-output-channel channel state)))
  :hints (("Goal" :in-theory (enable state-p))))
