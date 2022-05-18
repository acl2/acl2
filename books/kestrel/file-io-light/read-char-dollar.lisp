; A lightweight book about the built-in function read-char$.
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/channels" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;; So the rules in the book fire
(in-theory (disable mv-nth read-char$))

(local (in-theory (disable open-input-channels
                           update-open-input-channels
                           member-equal)))

(defthm state-p1-of-mv-nth-1-of-read-char$
  (implies (and (symbolp channel)
                (state-p1 state)
                (assoc-equal channel (open-input-channels state)))
           (state-p1 (mv-nth 1 (read-char$ channel state))))
  :hints (("Goal" :in-theory (enable read-char$))))

(defthm state-p-of-mv-nth-1-of-read-char$
  (implies (and (symbolp channel)
                (state-p1 state)
                (assoc-equal channel (open-input-channels state)))
           (state-p (mv-nth 1 (read-char$ channel state))))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm open-input-channel-p1-of-mv-nth-1-of-read-char$
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel typ state))
           (open-input-channel-p1 channel typ (mv-nth 1 (read-char$ channel state))))
  :hints (("Goal" :in-theory (enable read-char$))))

;; Because it's an open :character channel
(defthm open-input-channel-any-p1-of-mv-nth-1-of-read-char$
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :character state))
           (open-input-channel-any-p1 channel (mv-nth 1 (read-char$ channel state))))
  :hints (("Goal" :in-theory (e/d (open-input-channel-any-p1)
                                  (open-input-channel-p1)))))

(defthm open-input-channels-of-mv-nth-1-of-read-char$
  (implies (and (symbolp channel)
                (state-p1 state)
                (open-input-channel-p1 channel :character state))
           (equal (open-input-channels (mv-nth 1 (read-char$ channel state)))
                  (if (cddr (assoc-equal channel (open-input-channels state)))
                      ;; more data to read:
                      (add-pair channel
                                (cons (cadr (assoc-equal channel (open-input-channels state))) ;header
                                      (cdddr (assoc-equal channel (open-input-channels state))) ;cdr of values
                                      )
                                (open-input-channels state))
                    ;; no more data to read:
                    (open-input-channels state))))
  :hints (("Goal" :in-theory (enable read-char$))))

;; Reading gives a non-nil value iff the channel contents are non-empty
(defthm mv-nth-0-of-read-char$-iff
  (implies (and (open-input-channel-p channel :character state)
                (state-p1 state))
           (iff (mv-nth 0 (read-char$ channel state))
                (consp (channel-contents channel state)
                       ;; (cddr (assoc-equal channel (open-input-channels state)))
                       )))
  :hints (("Goal" :use (:instance character-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                                  (channels (open-input-channels state)))
           :in-theory (e/d (read-char$ channel-contents)
                           (character-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                            true-listp)))))

(defthm characterp-of-mv-nth-0-of-read-char$-iff
  (implies (and (open-input-channel-p channel :character state)
                (state-p1 state))
           (iff (characterp (mv-nth 0 (read-char$ channel state)))
                (mv-nth 0 (read-char$ channel state))))
  :hints (("Goal" :use (:instance character-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                                  (channels (open-input-channels state)))
           :in-theory (e/d (read-char$ channel-contents character-listp)
                           (character-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                            true-listp)))))

(defthm <-of-len-of-channel-contents-of-mv-nth-1-of-read-char$
  (implies (consp (channel-contents channel state))
           (< (len (channel-contents channel (mv-nth 1 (read-char$ channel state))))
              (len (channel-contents channel state))))
  :hints (("Goal" :in-theory (enable read-char$ channel-contents))))

;; this version has channel-contents inlined
;; or perhaps make a rule for (open-input-channels (mv-nth 1 (read-char$ channel state)))
(defthm <-of-len-of-channel-contents-of-mv-nth-1-of-read-char$-alt
  (implies (consp (cddr (assoc-equal channel (open-input-channels state))))
           (< (len (cddr (assoc-equal channel (open-input-channels (mv-nth 1 (read-char$ channel state))))))
              (len (cddr (assoc-equal channel (open-input-channels state))))))
  :hints (("Goal" :in-theory (enable read-char$ channel-contents))))
