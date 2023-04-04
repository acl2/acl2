; A lightweight book about the built-in function open-output-channel-p
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
(defthm assoc-equal-of-open-output-channels-forward-to-symbolp
  (implies (and (assoc-equal channel (open-output-channels state))
                (state-p1 state))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm open-output-channel-p1-forward-to-symbolp
  (implies (and (open-output-channel-p1 channel typ state)
                (state-p1 state))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm open-output-channel-p-forward-to-symbolp
  (implies (and (open-output-channel-p channel typ state)
                (state-p state))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-p1))))

;; TODO: How should we handle the p vs p1 functions?
(defthm open-output-channel-p-forward-to-open-output-channel-p1
   (implies (open-output-channel-p channel typ state)
            (open-output-channel-p1 channel typ state))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable open-output-channel-p))))
