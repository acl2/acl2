; A lightweight book about the built-in function open-output-channel!
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "open-output-channel"))
(local (include-book "kestrel/utilities/w" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))

(in-theory (disable open-output-channel!
                    open-output-channel-p
                    open-output-channel-p1
                    mv-nth
                    state-p1))

;; Needed because we mention open-output-channel! in the theorems below.
(defttag file-io!)

(local (in-theory (disable w
                           update-global-table
                           update-file-clock
                           update-open-output-channels
                           get-global
                           put-global)))

(local (in-theory (enable not-member-equal-when-not-writable-file-listp1)))

;; We use TYPE and VAL here instead of TYP and VALUE to match what std does
(defthm open-output-channel-p1-of-put-global
  (equal (open-output-channel-p1 channel type (put-global key val state))
         (open-output-channel-p1 channel type state))
  :hints (("Goal" :in-theory (enable open-output-channel-p1))))

(defthm open-output-channel-p-of-put-global
 (equal (open-output-channel-p channel typ (put-global key value state))
        (open-output-channel-p channel typ state))
 :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm symbolp-of-mv-nth-0-of-open-output-channel!
  (symbolp (mv-nth 0 (open-output-channel! file-name typ state)))
  :hints (("Goal" :in-theory (enable open-output-channel!))))

(defthm open-output-channel-p1-after-open-output-channel!
  (implies (mv-nth 0 (open-output-channel! fname typ state)) ;no error
           (open-output-channel-p1 (mv-nth 0 (open-output-channel! fname typ state))
                                   typ
                                   (mv-nth 1 (open-output-channel! fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel!))))

(defthm open-output-channel-p-after-open-output-channel!
  (implies (mv-nth 0 (open-output-channel! fname typ state)) ;no error
           (open-output-channel-p (mv-nth 0 (open-output-channel! fname typ state))
                                  typ
                                  (mv-nth 1 (open-output-channel! fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

(defthm state-p1-of-open-output-channel!
  (implies (and (state-p1 state)
                (stringp fname)
                (member type *file-types*))
           (state-p1 (mv-nth 1 (open-output-channel! fname type state))))
  :hints (("Goal" :in-theory (enable open-output-channel!))))

(defthm state-p-of-open-output-channel!
  (implies (and (state-p1 state)
                (stringp fname)
                (member type *file-types*))
           (state-p (mv-nth 1 (open-output-channel! fname type state))))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm w-of-mv-nth-1-of-open-output-channel!
  (equal (w (mv-nth 1 (open-output-channel! file-name type state)))
         (w state))
  :hints (("Goal" :in-theory (enable open-output-channel!))))

(defthm not-equal-of-mv-nth-0-of-open-output-channel!-and-standard-co
  (implies (state-p state)
           (not (equal (mv-nth 0 (open-output-channel! file-name typ state))
                       *standard-co*)))
  :hints (("Goal" :in-theory (enable open-output-channel!))))
