; A lightweight book about the built-in function open-input-channel
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/intern-in-package-of-symbol" :dir :system))
(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/utilities/explode-atom" :dir :system))
(local (include-book "kestrel/utilities/explode-nonnegative-integer" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "channels"))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (disable len true-listp member-equal nth update-nth)))

(in-theory (disable open-input-channel
                    open-input-channel-p1
                    mv-nth ;so that the rules below fire
                    ))

;; The channel name, or nil.
(defthm symbolp-of-mv-nth-0-of-open-input-channel
  (symbolp (mv-nth 0 (open-input-channel file-name typ state)))
  :hints (("Goal" :in-theory (enable open-input-channel))))

(defthm state-p1-of-mv-nth-1-of-open-input-channel
  (implies (and (member-eq typ *file-types*)
                (stringp file-name)
                (state-p1 state))
           (state-p1 (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (e/d (open-input-channel
                                   state-p1
                                   channel-headerp)
                                  (add-pair
                                   all-boundp
                                   file-clock-p
                                   len
                                   make-input-channel
                                   natp
                                   open-channels-p
                                   read-files-p
                                   readable-files-p
                                   writeable-files-p
                                   written-files-p)))))

(defthm state-p-of-mv-nth-1-of-open-input-channel
  (implies (and (member-eq typ *file-types*)
                (stringp file-name)
                (state-p state))
           (state-p (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable state-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm open-input-channel-p1-after-open-input-channel
  (implies (mv-nth 0 (open-input-channel file-name typ state)) ;no error
           (open-input-channel-p1 (mv-nth 0 (open-input-channel file-name typ state))
                                  typ
                                  (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel open-input-channel-p1))))

(defthm open-input-channel-p-after-open-input-channel
  (implies (mv-nth 0 (open-input-channel file-name typ state)) ;no error
           (open-input-channel-p (mv-nth 0 (open-input-channel file-name typ state))
                                 typ
                                 (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p))))

(defthm open-input-channel-any-p1-after-open-input-channel
  (implies (and (mv-nth 0 (open-input-channel file-name typ state)) ;no error
                (member-equal typ *file-types*))
           (open-input-channel-any-p1 (mv-nth 0 (open-input-channel file-name typ state))
                                      (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1 member-equal))))

(defthm open-input-channel-any-p-after-open-input-channel
  (implies (and (mv-nth 0 (open-input-channel file-name typ state)) ;no error
                (member-equal typ *file-types*))
           (open-input-channel-any-p (mv-nth 0 (open-input-channel file-name typ state))
                                     (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (e/d (open-input-channel-any-p) (open-input-channel-any-p1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See the guard of close-input-channel
(defthm not-equal-standard-character-input-0-and-mv-nth-0-of-open-input-channel
  (implies (state-p state)
           (not (equal *standard-ci* (mv-nth 0 (open-input-channel file-name typ state)))))
  :hints (("Goal" :in-theory (enable ;state-p1
                              open-input-channel
                              equal-of-intern-in-package-of-symbol
                              explode-atom
                              equal-of-append))))

;; See the guard of close-input-channel
(defthm not-equal-standard-object-input-0-and-mv-nth-0-of-open-input-channel
  (implies (state-p state)
           (not (equal *standard-oi* (mv-nth 0 (open-input-channel file-name typ state)))))
  :hints (("Goal" :in-theory (enable ;state-p1
                              open-input-channel
                              equal-of-intern-in-package-of-symbol
                              explode-atom
                              equal-of-append))))

;; See the guard of close-input-channel
(defthm not-member-equal-of-mv-nth-0-of-open-input-channel
  (implies (state-p state)
           (not (member-equal (mv-nth 0 (open-input-channel file-name typ state))
                              '(acl2-input-channel::standard-character-input-0
                                acl2-input-channel::standard-object-input-0))))
  :hints (("Goal" :in-theory (enable member-equal))))
