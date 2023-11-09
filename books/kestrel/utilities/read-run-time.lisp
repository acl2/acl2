; A lightweight book about the built-in function read-run-time.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm rationalp-of-mv-nth-0-of-read-run-time
  (rationalp (mv-nth 0 (read-run-time state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-run-time))))

(defthm state-p-of-mv-nth-1-of-read-run-time
  (implies (state-p state)
           (state-p (mv-nth 1 (read-run-time state))))
  :hints (("Goal" :in-theory (enable read-run-time))))
