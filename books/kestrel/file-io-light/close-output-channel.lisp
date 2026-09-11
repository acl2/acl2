; Rules about close-output-channel
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

(in-theory (disable close-output-channel))

(defthm state-p1-of-close-output-channel
  (implies (state-p1 state)
           (equal (state-p1 (close-output-channel channel state))
                  (open-output-channel-any-p1 channel state)))
  :hints (("Goal"
           :in-theory (enable close-output-channel
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm open-output-channels-of-close-output-channel
  (equal (open-output-channels (close-output-channel channel state))
         (remove1-assoc-equal channel (open-output-channels state)))
  :hints (("Goal" :in-theory (enable close-output-channel))))

;; Closing an output channel does not affect other output channels.
(defthm open-output-channel-p1-of-close-output-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-output-channel-p1 channel typ (close-output-channel channel2 state))
                  (open-output-channel-p1 channel typ state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p1))))

(defthm open-output-channel-p-of-close-output-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-output-channel-p channel typ (close-output-channel channel2 state))
                  (open-output-channel-p channel typ state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm open-output-channel-any-p1-of-close-output-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-output-channel-any-p1 channel (close-output-channel channel2 state))
                  (open-output-channel-any-p1 channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p1))))

(defthm open-output-channel-any-p-of-close-output-channel-diff
  (implies (not (equal channel channel2))
           (equal (open-output-channel-any-p channel (close-output-channel channel2 state))
                  (open-output-channel-any-p channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p))))

;; After closing a channel, it is no longer open.
(defthm open-output-channel-p1-of-close-output-channel-same
  (implies (state-p1 state)
           (not (open-output-channel-p1 channel typ (close-output-channel channel state))))
  :hints (("Goal" :in-theory (enable open-output-channel-p1))))

(defthm open-output-channel-p-of-close-output-channel-same
  (implies (state-p state)
           (not (open-output-channel-p channel typ (close-output-channel channel state))))
  :hints (("Goal" :in-theory (enable open-output-channel-p state-p))))

(defthm open-output-channel-any-p1-of-close-output-channel-same
  (implies (state-p1 state)
           (not (open-output-channel-any-p1 channel (close-output-channel channel state))))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p1))))

(defthm open-output-channel-any-p-of-close-output-channel-same
  (implies (state-p state)
           (not (open-output-channel-any-p channel (close-output-channel channel state))))
  :hints (("Goal" :in-theory (enable open-output-channel-any-p state-p))))

;; Closing an output channel does not affect the input channels.
(defthm open-input-channels-of-close-output-channel
  (equal (open-input-channels (close-output-channel channel state))
         (open-input-channels state))
  :hints (("Goal" :in-theory (enable close-output-channel))))

;; Closing an output channel does not affect the input channels.
(defthm open-input-channel-p1-of-close-output-channel
  (equal (open-input-channel-p1 channel typ (close-output-channel channel2 state))
         (open-input-channel-p1 channel typ state))
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))

(defthm open-input-channel-p-of-close-output-channel
  (equal (open-input-channel-p channel typ (close-output-channel channel2 state))
         (open-input-channel-p channel typ state))
  :hints (("Goal" :in-theory (enable open-input-channel-p))))

(defthm open-input-channel-any-p1-of-close-output-channel
  (equal (open-input-channel-any-p1 channel (close-output-channel channel2 state))
         (open-input-channel-any-p1 channel state))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1))))

(defthm open-input-channel-any-p-of-close-output-channel
  (equal (open-input-channel-any-p channel (close-output-channel channel2 state))
         (open-input-channel-any-p channel state))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p))))
