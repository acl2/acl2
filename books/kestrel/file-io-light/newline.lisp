; A lightweight book about the built-in function newline
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "princ-dollar"))

(in-theory (disable newline))

(local (in-theory (disable open-output-channels open-output-channel-p1)))

(defthm open-output-channel-p1-of-newline
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (newline channel2 state)))
  :hints (("Goal" :in-theory (enable newline))))

(defthm open-output-channel-p-of-newline
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (newline channel2 state)))
  :hints (("Goal" :in-theory (enable newline))))

(defthm open-output-channel-any-p1-of-newline
  (implies (open-output-channel-any-p1 channel state)
           (open-output-channel-any-p1 channel (newline channel2 state)))
  :hints (("Goal" :in-theory (enable newline))))

(defthm open-output-channel-any-p-of-newline
  (implies (open-output-channel-any-p channel state)
           (open-output-channel-any-p channel (newline channel2 state)))
  :hints (("Goal" :in-theory (enable newline))))

(defthm state-p1-of-newline
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :character state))
           (state-p1 (newline channel state)))
  :hints (("Goal" :in-theory (enable newline))))

(defthm state-p-of-newline
  (implies (and (state-p state)
                (open-output-channel-p channel :character state))
           (state-p (newline channel state)))
  :hints (("Goal" :in-theory (enable newline))))

(defthm w-of-newline
  (equal (w (newline channel state))
         (w state))
  :hints (("Goal" :in-theory (enable newline))))
