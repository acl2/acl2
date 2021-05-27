; A utility for reasoning about I/O channels
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: can we make this executable and just use it to get the contents?
(defund-nx channel-contents (channel state)
  (declare (xargs ;:guard (open-input-channel-any-p1 channel state)
                  ;:stobjs state
                  ))
  (cddr (assoc-equal channel (open-input-channels state))))

(defthm channel-contents-of-update-open-input-channels-of-add-pair
  (equal (channel-contents channel (update-open-input-channels (add-pair channel value channels) state))
         (cdr value))
  :hints (("Goal" :in-theory (enable channel-contents))))
