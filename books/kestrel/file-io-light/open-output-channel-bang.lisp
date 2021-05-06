; A lightweight book about the built-in function open-output-channel!
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable open-output-channel!
                    open-output-channel-p
                    open-output-channel-p1
                    mv-nth))

;; Needed because we mention open-output-channel! in the theorems below.
(defttag file-io!)

(defthm symbolp-of-mv-nth-0-of-open-output-channel!
  (symbolp (mv-nth 0 (open-output-channel! file-name typ state)))
  :hints (("Goal" :in-theory (enable open-output-channel!))))

(defthm open-output-channel-p-after-open-output-channel!
  (implies (mv-nth 0 (open-output-channel! fname typ state)) ;no error
           (open-output-channel-p (mv-nth 0 (open-output-channel! fname typ state))
                                  typ
                                  (mv-nth 1 (open-output-channel! fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel! open-output-channel-p open-output-channel open-output-channel-p1 open-output-channels
                                     put-global))))

(defthm open-output-channel-p1-after-open-output-channel!
  (implies (mv-nth 0 (open-output-channel! fname typ state)) ;no error
           (open-output-channel-p1 (mv-nth 0 (open-output-channel! fname typ state))
                                   typ
                                   (mv-nth 1 (open-output-channel! fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel! open-output-channel-p open-output-channel open-output-channel-p1 open-output-channels
                                     put-global))))

(local (include-book "std/io/base" :dir :system)) ;for reasoning support

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
