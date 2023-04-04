; Rules about close-input-channel
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

(in-theory (disable close-input-channel))

(defthm state-p1-of-close-input-channel
  (implies (state-p1 state)
           (equal (state-p1 (close-input-channel channel state))
                  (open-input-channel-any-p1 channel state)))
  :hints (("Goal" :in-theory (enable close-input-channel
                                     stringp-of-caddr-when-channel-headerp
                                     integerp-of-cadddr-when-channel-headerp
                                     integerp-when-file-clock-p
                                     state-p1))))

(defthm state-p-of-close-input-channel
  (implies (state-p state)
           (equal (state-p (close-input-channel channel state))
                  (open-input-channel-any-p channel state)))
  :hints (("Goal" :in-theory (enable state-p open-input-channel-any-p))))
