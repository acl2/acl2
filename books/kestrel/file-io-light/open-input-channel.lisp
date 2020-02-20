; A lightweight book about the built-in function open-input-channel
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable open-input-channel
                    open-input-channel-p  ;so that a rule below fires
                    open-input-channel-p1
                    mv-nth ;so that the rules below fire
                    ))

(defthm symbolp-of-mv-nth-0-of-open-input-channel
  (symbolp (mv-nth 0 (open-input-channel file-name typ state)))
  :hints (("Goal" :in-theory (enable open-input-channel))))

(defthm open-input-channel-p-after-open-input-channel
  (implies (mv-nth 0 (open-input-channel file-name typ state)) ;no error
           (open-input-channel-p (mv-nth 0 (open-input-channel file-name typ state))
                                 typ
                                 (mv-nth 1 (open-input-channel file-name typ state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p open-input-channel open-input-channel-p1))))
