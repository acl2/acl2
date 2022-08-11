; A lightweight book about the built-in function princ$.
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/w" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/channels" :dir :system))
(local (include-book "kestrel/utilities/explode-atom" :dir :system))

(in-theory (disable princ$))

(local (in-theory (disable open-output-channels open-output-channel-p1)))

(defthm open-output-channel-p1-of-princ$-gen
  (implies (open-output-channel-p1 channel2 typ state)
           (open-output-channel-p1 channel2 typ (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     princ$
                                     open-output-channel-p1
                                     ;open-output-channels
                                     open-output-channel-p))))

(defthm open-output-channel-p-of-princ$
  (implies (open-output-channel-p channel2 typ state)
           (open-output-channel-p channel2 typ (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm state-p-of-princ$
  (implies (and (state-p state)
                (symbolp channel)
                (open-output-channel-p channel :character state))
           (state-p (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable princ$ open-output-channel-p1))))

(defthm w-of-princ$
  (equal (w (princ$ x channel state))
         (w state))
  :hints (("Goal" :in-theory (e/d (princ$) (w update-open-output-channels)))))
