; More rules about channels
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Combine these with channels.lisp

(defthm cadr-of-cadr-of-assoc-equal-of-open-input-channels-when-open-input-channel-p1
  (implies (open-input-channel-p1 channel typ state)
           (equal (cadr (cadr (assoc-equal channel (open-input-channels state))))
                  typ))
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))

;; TODO: Do we need these 3?:

(local
 (defthm cadr-of-cadr-of-assoc-equal-of-open-input-channels-when-open-input-channel-p
   (implies (open-input-channel-p channel typ state)
            (equal (cadr (cadr (assoc-equal channel (open-input-channels state))))
                   typ))
   :hints (("Goal" :in-theory (enable open-input-channel-p)))))


;move
(local
 (defthm open-input-channel-p1-of-update-open-input-channels-of-add-pair-same
  (equal (open-input-channel-p1 channel
                                typ
                                (update-open-input-channels (add-pair channel val (open-input-channels state))
                                                            state))
         (equal (cadr (car val))
                typ))
  :hints (("Goal" :in-theory (enable open-input-channel-p1)))))

;move
(local
 (defthm open-input-channel-p1-of-update-open-input-channels-of-add-pair-diff
  (implies (not (equal channel channel2))
           (equal (open-input-channel-p1 channel
                                         typ
                                         (update-open-input-channels (add-pair channel2 val channels)
                                                                     state))
                  (open-input-channel-p1 channel
                                         typ
                                         (update-open-input-channels channels
                                                                     state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p1)))))

;; Trying to introduce some abstractions to the channel machinery
(defund channel-header-type (header)
  (cadr header))

(defthm channel-header-type-of-cadr-of-assoc-equal-of-open-input-channels
  (implies (open-input-channel-p1 channel typ state)
           (equal (channel-header-type
                    (cadr (assoc-equal channel (open-input-channels state))))
                  typ))
  :hints (("Goal" :in-theory (enable open-input-channel-p1 channel-header-type))))

;move
(defthm open-input-channel-p1-of-update-open-input-channels-of-add-pair-both
  (equal (open-input-channel-p1 channel typ (update-open-input-channels (add-pair channel2 val channels) state))
         (if (equal channel channel2)
             (equal (channel-header-type (car val)) typ)
           (open-input-channel-p1 channel typ (update-open-input-channels channels state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p1 channel-header-type))))
