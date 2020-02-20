; A lightweight book about the built-in function open-output-channel
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable open-output-channel
                    open-output-channel-p ;so that a rule below fires
                    open-output-channel-p1
                    mv-nth ;so that the rules below fire
                    ))

(defthm symbolp-of-mv-nth-0-of-open-output-channel
  (symbolp (mv-nth 0 (open-output-channel file-name typ state)))
  :hints (("Goal" :in-theory (enable open-output-channel))))

(defthm open-output-channel-p-after-open-output-channel
  (implies (mv-nth 0 (open-output-channel fname typ state)) ;no error
           (open-output-channel-p (mv-nth 0 (open-output-channel fname typ state))
                                  typ
                                  (mv-nth 1 (open-output-channel fname typ state))))
  :hints (("Goal" :in-theory (enable open-output-channel-p open-output-channel open-output-channel-p1 open-output-channels))))
