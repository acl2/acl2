; A lightweight book about the built-in function open-input-channel-p
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "open-channels-p"))

;move
(defthm assoc-equal-of-open-input-channels-forward-to-symbolp
  (implies (and (assoc-equal channel (open-input-channels state))
                (state-p1 state))
           (symbolp channel))
  :rule-classes :forward-chaining)

(defthm open-input-channel-p1-forward-to-symbolp
  (implies (and (open-input-channel-p1 channel typ state)
                (state-p1 state))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm open-input-channel-p-forward-to-symbolp
  (implies (and (open-input-channel-p channel typ state)
                (state-p state))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-p1))))

;; TODO: How should we handle the p vs p1 functions?
(defthm open-input-channel-p-forward-to-open-input-channel-p1
   (implies (open-input-channel-p channel typ state)
            (open-input-channel-p1 channel typ state))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable open-input-channel-p))))
