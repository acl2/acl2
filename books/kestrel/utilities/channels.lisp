; A lightweight book about i/o channels
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm open-channel-listp-of-add-pair
  (implies (open-channel-listp l)
           (equal (open-channel-listp (add-pair key value l))
                  (open-channel1 value)))
  :hints (("Goal" :in-theory (disable open-input-channels))))
