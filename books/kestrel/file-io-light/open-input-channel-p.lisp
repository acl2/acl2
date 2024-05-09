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

(in-theory (disable open-input-channel-p
                    open-input-channel-p1))

(local (in-theory (disable state-p1 state-p)))

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
  :hints (("Goal" :in-theory (enable state-p1 open-input-channel-p1))))

(defthm open-input-channel-p-forward-to-symbolp
  (implies (and (open-input-channel-p channel typ state)
                (state-p state))
           (symbolp channel))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-p open-input-channel-p))))

;; TODO: How should we handle the p vs p1 functions?
(defthm open-input-channel-p-forward-to-open-input-channel-p1
   (implies (open-input-channel-p channel typ state)
            (open-input-channel-p1 channel typ state))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable open-input-channel-p))))

(defthmd open-input-channel-p1-becomes-open-input-channel-p
  (equal (open-input-channel-p1 channel typ state)
         (open-input-channel-p channel typ state))
  :hints (("Goal" :in-theory (enable open-input-channel-p))))

(theory-invariant (incompatible (:rewrite open-input-channel-p1-becomes-open-input-channel-p)
                                (:definition open-input-channel-p)))
