; A lightweight book about the built-in function read-object.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/channels" :dir :system))

;; So the rules in the book fire
(in-theory (disable mv-nth read-object))

(local (in-theory (disable open-input-channels
                           update-open-input-channels
                           member-equal)))

(defthm state-p1-of-mv-nth-2-of-read-object
  (implies (and (symbolp channel)
                (state-p1 state))
           (state-p1 (mv-nth 2 (read-object channel state))))
  :hints (("Goal" :in-theory (enable read-object))))

(defthm open-input-channel-p1-of-mv-nth-2-of-read-object
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (open-input-channel-p1 channel :object (mv-nth 2 (read-object channel state))))
  :hints (("Goal" :in-theory (enable read-object))))

;; Because it's an open :object channel
(defthm open-input-channel-any-p1-of-mv-nth-2-of-read-object
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (open-input-channel-any-p1 channel (mv-nth 2 (read-object channel state))))
  :hints (("Goal" :in-theory (e/d (open-input-channel-any-p1)
                                  (open-input-channel-p1)))))

(defthm open-input-channels-of-mv-nth-2-of-read-object
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (equal (open-input-channels (mv-nth 2 (read-object channel state)))
                  (if (cddr (assoc-equal channel (open-input-channels state)))
                      ;; more data to read:
                      (add-pair channel
                                (cons (cadr (assoc-equal channel (open-input-channels state))) ;header
                                      (cdddr (assoc-equal channel (open-input-channels state))) ;cdr of values
                                      )
                                (open-input-channels state))
                    ;; no more data to read:
                    (open-input-channels state))))
  :hints (("Goal" :in-theory (enable read-object))))
