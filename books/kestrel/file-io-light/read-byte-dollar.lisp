; A lightweight book about the built-in function read-byte$.
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
(local (include-book "kestrel/lists-light/cons" :dir :system))

;; So the rules in the book fire
(in-theory (disable mv-nth read-byte$))

(local (in-theory (disable open-input-channels
                           update-open-input-channels
                           member-equal)))

(defthm state-p1-of-mv-nth-1-of-read-byte$
  (implies (and (symbolp channel)
                (state-p1 state)
                (assoc-equal channel (open-input-channels state)))
           (state-p1 (mv-nth 1 (read-byte$ channel state))))
  :hints (("Goal" :in-theory (enable read-byte$))))

(defthm open-input-channel-p1-of-mv-nth-1-of-read-byte$
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :byte state))
           (open-input-channel-p1 channel :byte (mv-nth 1 (read-byte$ channel state))))
  :hints (("Goal" :in-theory (enable read-byte$))))

;; Because it's an open :byte channel
(defthm open-input-channel-any-p1-of-mv-nth-1-of-read-byte$
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :byte state))
           (open-input-channel-any-p1 channel (mv-nth 1 (read-byte$ channel state))))
  :hints (("Goal" :in-theory (e/d (open-input-channel-any-p1)
                                  (open-input-channel-p1)))))

(defthm open-input-channels-of-mv-nth-1-of-read-byte$
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :byte state))
           (equal (open-input-channels (mv-nth 1 (read-byte$ channel state)))
                  (if (cddr (assoc-equal channel (open-input-channels state)))
                      ;; more data to read:
                      (add-pair channel
                                (cons (cadr (assoc-equal channel (open-input-channels state))) ;header
                                      (cdddr (assoc-equal channel (open-input-channels state))) ;cdr of values
                                      )
                                (open-input-channels state))
                    ;; no more data to read:
                    (open-input-channels state))))
  :hints (("Goal" :in-theory (enable read-byte$))))
