; A lightweight book about the built-in function princ$.
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/w" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "channels"))
(local (include-book "open-output-channel-p"))
(local (include-book "typed-io-listp"))
(local (include-book "kestrel/utilities/explode-atom" :dir :system))

(in-theory (disable princ$))

(local (in-theory (disable open-output-channels open-output-channel-p1)))

(local
 (defthm character-listp-of-explode-atom+
   (character-listp (explode-atom+ x print-base print-radix))
   :hints (("Goal" :in-theory (enable explode-atom+)))))

(defthm open-output-channel-p1-of-princ$-gen
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (princ$ x channel2 state)))
  :hints (("Goal" :in-theory (enable princ$ open-output-channel-p1))))

(defthm open-output-channel-p-of-princ$
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (princ$ x channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm open-output-channel-any-p1-of-princ$-gen
  (implies (open-output-channel-any-p1 channel state)
           (open-output-channel-any-p1 channel (princ$ x channel2 state)))
  :hints (("Goal" :in-theory (enable princ$ open-output-channel-p1))))

(defthm open-output-channel-any-p-of-princ$
  (implies (open-output-channel-any-p channel state)
           (open-output-channel-any-p channel (princ$ x channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm state-p1-of-princ$-gen ; avoid name clash with std
  (implies (and (state-p1 state)
                ;; Not sure if this should be open-output-channel-p1 or open-output-channel-p,
                ;; but the rule in STD has open-output-channel-p1, so we match that here:
                (open-output-channel-p1 channel :character state))
           (state-p1 (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable princ$ open-output-channel-p1))))

(defthm state-p-of-princ$
  (implies (and (state-p state)
                (open-output-channel-p channel :character state))
           (state-p (princ$ x channel state)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm w-of-princ$
  (equal (w (princ$ x channel state))
         (w state))
  :hints (("Goal" :in-theory (e/d (princ$) (w update-open-output-channels)))))
