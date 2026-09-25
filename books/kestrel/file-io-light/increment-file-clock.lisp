; A lightweight book about the built-in function increment-file-clock
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/state" :dir :system))

(in-theory (disable increment-file-clock))

(defthm state-p1-of-increment-file-clock
  (implies (state-p1 state)
           (state-p1 (increment-file-clock state)))
  :hints (("Goal" :in-theory (enable increment-file-clock file-clock-p))))

(defthm state-p-of-increment-file-clock
  (implies (state-p state)
           (state-p (increment-file-clock state)))
  :hints (("Goal" :in-theory (enable state-p))))
