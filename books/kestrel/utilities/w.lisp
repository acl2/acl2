; A lightweight book about the built-in function W
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; W is the function that extracts the ACL2 logical world from the state

(in-theory (disable w))

(defthm plist-worldp-of-w
  (implies (state-p state)
           (plist-worldp (w state)))
  :hints (("Goal" :in-theory (enable w))))
