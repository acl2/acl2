; A lightweight book about the built-in function get-real-time.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "read-run-time"))

(in-theory (disable get-real-time))

(defthm rationalp-of-mv-nth-0-of-get-real-time
  (rationalp (mv-nth 0 (get-real-time state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable get-real-time))))

(defthm state-p-of-mv-nth-1-of-get-real-time
  (implies (state-p state)
           (state-p (mv-nth 1 (get-real-time state))))
  :hints (("Goal" :in-theory (enable get-real-time))))
