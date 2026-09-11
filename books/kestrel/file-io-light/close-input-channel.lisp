; Rules about close-input-channel
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "channels"))
(local (include-book "kestrel/alists-light/remove1-assoc-equal" :dir :system))
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

(defthm w-of-close-input-channel
  (equal (w (close-input-channel channel state))
         (w state))
    :hints (("Goal" :in-theory (enable close-input-channel w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm open-input-channels-of-close-input-channel
  (equal (open-input-channels (close-input-channel channel state))
         (remove1-assoc-equal channel (open-input-channels state)))
  :hints (("Goal" :in-theory (enable close-input-channel))))

;; Closing an input channel does not affect other input channels.
(defthm open-input-channel-p1-of-close-input-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-input-channel-p1 channel typ (close-input-channel channel2 state))
                  (open-input-channel-p1 channel typ state)))
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))

(defthm open-input-channel-p-of-close-input-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-input-channel-p channel typ (close-input-channel channel2 state))
                  (open-input-channel-p channel typ state)))
  :hints (("Goal" :in-theory (enable open-input-channel-p))))

(defthm open-input-channel-any-p1-of-close-input-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-input-channel-any-p1 channel (close-input-channel channel2 state))
                  (open-input-channel-any-p1 channel state)))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1))))

(defthm open-input-channel-any-p-of-close-input-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-input-channel-any-p channel (close-input-channel channel2 state))
                  (open-input-channel-any-p channel state)))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p))))

;; After closing a channel, it is no longer open.
(defthm open-input-channel-p1-of-close-input-channel-same
  (implies (state-p1 state)
           (not (open-input-channel-p1 channel typ (close-input-channel channel state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))

(defthm open-input-channel-p-of-close-input-channel-same
  (implies (state-p state)
           (not (open-input-channel-p channel typ (close-input-channel channel state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p state-p))))

(defthm open-input-channel-any-p1-of-close-input-channel-same
  (implies (state-p1 state)
           (not (open-input-channel-any-p1 channel (close-input-channel channel state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1))))

(defthm open-input-channel-any-p-of-close-input-channel-same
  (implies (state-p state)
           (not (open-input-channel-any-p channel (close-input-channel channel state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p state-p))))

;; Closing an input channel does not affect the output channels.
(defthm open-output-channels-of-close-input-channel
  (equal (open-output-channels (close-input-channel channel state))
         (open-output-channels state))
  :hints (("Goal" :in-theory (enable close-input-channel))))

;; Closing an input channel does not affect the output channels.
(defthm open-output-channel-p1-of-close-input-channel
  (equal (open-output-channel-p1 channel typ (close-input-channel channel2 state))
         (open-output-channel-p1 channel typ state))
  :hints (("Goal" :in-theory (enable open-output-channel-p1))))

(defthm open-output-channel-p-of-close-input-channel
  (equal (open-output-channel-p channel typ (close-input-channel channel2 state))
         (open-output-channel-p channel typ state))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm open-output-channel-any-p1-of-close-input-channel
  (equal (open-output-channel-any-p1 channel (close-input-channel channel2 state))
         (open-output-channel-any-p1 channel state))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p1))))

(defthm open-output-channel-any-p-of-close-input-channel
  (equal (open-output-channel-any-p channel (close-input-channel channel2 state))
         (open-output-channel-any-p channel state))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p))))
