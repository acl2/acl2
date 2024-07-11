; A lightweight book about the built-in function read-object.
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; (include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "channels"))
(local (include-book "iprint-oracle-updates"))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; So the rules in the book fire
(in-theory (disable mv-nth read-object))

(local (in-theory (enable consp-of-cdr)))

(local
 (defthmd assoc-equal-when-not-symbolp-and-open-channels-p
   (implies (and (not (symbolp channel))
                 (open-channels-p channels))
            (equal (assoc-equal channel channels)
                   nil))
   :hints (("Goal" :in-theory (enable open-channels-p ordered-symbol-alistp)))))

;; (local
;;  (defthm assoc-equal-of-open-input-channels-when-not-symbolp
;;    (implies (and (not (symbolp channel))
;;                  (state-p1 state))
;;             (equal (assoc-equal channel (open-input-channels state))
;;                    nil))
;;    :hints (("Goal" :in-theory (enable state-p1)))))

;; The eof flag is non-nil iff the channel contents are empty
(defthm mv-nth-0-of-read-object-iff
  (iff (mv-nth 0 (read-object channel state))
       (not (consp (cddr (assoc-equal channel (open-input-channels state))))))
  :hints (("Goal" :in-theory (enable read-object))))

(defthm state-p1-of-mv-nth-2-of-read-object
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (read-object channel state))))
  :hints (("Goal" :in-theory (enable read-object
                                     symbolp-when-assoc-equal-of-open-input-channels-and-state-p1
                                     assoc-equal-when-not-symbolp-and-open-channels-p))))

(defthm state-p-of-mv-nth-2-of-read-object
  (implies (state-p state)
           (state-p (mv-nth 2 (read-object channel state))))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm open-input-channels-of-mv-nth-2-of-read-object
  (equal (open-input-channels (mv-nth 2 (read-object channel state)))
         (if (consp (cddr (assoc-equal channel (open-input-channels state))))
             ;; more data to read:
             (add-pair channel
                       (cons (cadr (assoc-equal channel (open-input-channels state))) ;header
                             (cdddr (assoc-equal channel (open-input-channels state))) ;cdr of values
                             )
                       (open-input-channels state))
                    ;; no more data to read:
           (open-input-channels state)))
  :hints (("Goal" :in-theory (enable read-object))))

(defthm open-input-channel-p1-of-mv-nth-2-of-read-object
  (implies (open-input-channel-p1 channel typ state)
           (open-input-channel-p1 channel typ (mv-nth 2 (read-object channel2 state))))
  :hints (("Goal" :in-theory (enable read-object open-input-channel-p1))))

(defthm open-input-channel-p-of-mv-nth-2-of-read-object
  (implies (open-input-channel-p channel typ state)
           (open-input-channel-p channel typ (mv-nth 2 (read-object channel2 state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p))))

(defthm open-input-channel-any-p1-of-mv-nth-2-of-read-object
  (implies (open-input-channel-any-p1 channel state)
           (open-input-channel-any-p1 channel (mv-nth 2 (read-object channel2 state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1))))

(defthm open-input-channel-any-p-of-mv-nth-2-of-read-object
  (implies (open-input-channel-any-p channel state)
           (open-input-channel-any-p channel (mv-nth 2 (read-object channel2 state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p))))

;; (defthm <-of-len-of-channel-contents-of-mv-nth-2-of-read-object
;;   (implies (consp (channel-contents channel state))
;;            (< (len (channel-contents channel (mv-nth 2 (read-object channel state))))
;;               (len (channel-contents channel state))))
;;   :hints (("Goal" :in-theory (enable read-object channel-contents))))

;; this version has channel-contents inlined
(defthm <-of-len-of-channel-contents-of-mv-nth-2-of-read-object-alt
  (implies (consp (cddr (assoc-equal channel (open-input-channels state))))
           (< (len (cddr (assoc-equal channel (open-input-channels (mv-nth 2 (read-object channel state))))))
              (len (cddr (assoc-equal channel (open-input-channels state))))))
  :hints (("Goal" :in-theory (enable read-object))))
