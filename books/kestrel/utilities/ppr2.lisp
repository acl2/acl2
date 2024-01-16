; A lightweight book about the built-in function ppr2
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "system/fmt-support" :dir :system))

(defthm state-p1-of-ppr2
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (state-p1 (ppr2 x col channel state eviscp))))

(defthm state-p-of-ppr2
  (implies (and (fmt-state-p state)
                (open-output-channel-p channel :character state))
           (state-p (ppr2 x col channel state eviscp))))
