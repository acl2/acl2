; A lightweight book about the built-in function open-output-channel
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/intern-in-package-of-symbol" :dir :system))
(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/utilities/explode-atom" :dir :system))
(local (include-book "kestrel/utilities/explode-nonnegative-integer" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/channels" :dir :system))
(local (include-book "kestrel/utilities/w" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(in-theory (disable open-output-channel
                    open-output-channel-p ;so that a rule below fires
                    open-output-channel-p1
                    mv-nth ;so that the rules below fire
                    ))

(local (in-theory (disable add-pair ordered-symbol-alistp)))

;move
(defthmd not-member-equal-when-not-writable-file-listp1
   (implies (and (not (writable-file-listp1 file))
                 (writeable-files-p writeable-files))
            (not (member-equal file writeable-files)))
   :hints (("Goal" :in-theory (enable writeable-files-p))))

(local (in-theory (enable not-member-equal-when-not-writable-file-listp1)))

(defthm symbolp-of-mv-nth-0-of-open-output-channel
  (symbolp (mv-nth 0 (open-output-channel file-name typ state)))
  :hints (("Goal" :in-theory (enable open-output-channel))))

(defthm open-output-channel-p1-after-open-output-channel
  (implies (mv-nth 0 (open-output-channel fname typ state)) ;no error
           (open-output-channel-p1 (mv-nth 0 (open-output-channel fname typ state))
                                   typ
                                   (mv-nth 1 (open-output-channel fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel open-output-channel-p1))))

(defthm open-output-channel-p-after-open-output-channel
  (implies (mv-nth 0 (open-output-channel fname typ state)) ;no error
           (open-output-channel-p (mv-nth 0 (open-output-channel fname typ state))
                                  typ
                                  (mv-nth 1 (open-output-channel fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))

;; See the guard of close-output-channel
;; todo: slow
(defthm not-equal-of-mv-nth-0-of-open-output-channel-and-standard-co
  (implies (state-p state)
           (not (equal (mv-nth 0 (open-output-channel file-name typ state))
                       *standard-co*)))
  :hints (("Goal" :in-theory (enable open-output-channel
                                     equal-of-intern-in-package-of-symbol
                                     explode-atom
                                     equal-of-append))))

(defthm w-of-mv-nth-1-of-open-output-channel
  (equal (w (mv-nth 1 (open-output-channel file-name type state)))
         (w state))
  :hints (("Goal" :in-theory (enable open-output-channel))))

(defthm state-p1-of-mv-nth-1-of-open-output-channel
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (open-output-channel file-name type state))))
  :hints (("Goal" :in-theory (enable open-output-channel
                                     not-member-equal-when-not-writable-file-listp1))))

(defthm state-p-of-mv-nth-1-of-open-output-channel
  (implies (state-p state)
           (state-p (mv-nth 1 (open-output-channel file-name type state))))
  :hints (("Goal" :in-theory (enable state-p))))
