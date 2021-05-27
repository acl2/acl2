; A lightweight book about the built-in function open-input-channel
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/channels" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (disable len true-listp member-equal nth update-nth)))

;dup
(local
 (defthm length-becomes-len ;todo: just don't use length in state-p1?
   (implies (not (stringp x))
            (equal (length x)
                   (len x)))))

(in-theory (disable open-input-channel
                    open-input-channel-p  ;so that a rule below fires
                    open-input-channel-p1
                    mv-nth ;so that the rules below fire
                    ))

(defthm symbolp-of-mv-nth-0-of-open-input-channel
  (symbolp (mv-nth 0 (open-input-channel file-name typ state)))
  :hints (("Goal" :in-theory (enable open-input-channel))))

(defthm open-input-channel-p1-after-open-input-channel
  (implies (mv-nth 0 (open-input-channel file-name typ state)) ;no error
           (open-input-channel-p1 (mv-nth 0 (open-input-channel file-name typ state))
                                  typ
                                  (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel open-input-channel-p1))))

(defthm open-input-channel-any-p1-after-open-input-channel
  (implies (and (mv-nth 0 (open-input-channel file-name typ state)) ;no error
                (member-equal typ '(:byte :character :object)))
           (open-input-channel-any-p1 (mv-nth 0 (open-input-channel file-name typ state))
                                      (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1 member-equal))))

(defthm open-input-channel-p-after-open-input-channel
  (implies (mv-nth 0 (open-input-channel file-name typ state)) ;no error
           (open-input-channel-p (mv-nth 0 (open-input-channel file-name typ state))
                                 typ
                                 (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p open-input-channel-p1 open-input-channel))))

(defthm state-p1-of-mv-nth-1-of-open-input-channel
  (implies (and ;; (mv-nth 0 (open-input-channel file-name typ state)) ;no error
                (member-eq typ '(:character :byte :object))
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
                                   length
                                   make-input-channel
                                   natp
                                   open-channels-p
                                   read-files-p
                                   readable-files-p
                                   writeable-files-p
                                   written-files-p)))))
