; Rules about close-output-channel
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "channels"))
(local (include-book "kestrel/utilities/state" :dir :system))

(in-theory (disable close-output-channel))

(defthm state-p1-of-close-output-channel
  (implies (state-p1 state)
           (equal (state-p1 (close-output-channel channel state))
                  (open-output-channel-any-p1 channel state)))
  :hints (("Goal" :in-theory (enable close-output-channel
                                     stringp-of-caddr-when-channel-headerp
                                     integerp-of-cadddr-when-channel-headerp
                                     integerp-when-file-clock-p state-p1))))

(defthm state-p-of-close-output-channel
  (implies (state-p state)
           (equal (state-p (close-output-channel channel state))
                  (open-output-channel-any-p channel state)))
  :hints (("Goal" :in-theory (enable state-p open-output-channel-any-p))))

(defthm w-of-close-output-channel
  (equal (w (close-output-channel channel state))
         (w state))
  :hints (("Goal" :in-theory (enable close-output-channel w))))
