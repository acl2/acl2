; Rules about get-serialize-character tha require a ttag
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-serialize-character")

;; Needed because we mention open-output-channel! in the theorem below.
(defttag file-io!)

(local (in-theory (disable state-p1 open-output-channel put-global
                           open-output-channel!
                           open-output-channel-p1)))

(defthm get-serialize-character-of-mv-nth-1-of-open-output-channel!
  (equal (get-serialize-character (mv-nth 1 (open-output-channel! filename typ state)))
         (get-serialize-character state))
  :hints (("Goal" :in-theory (enable open-output-channel!))))
