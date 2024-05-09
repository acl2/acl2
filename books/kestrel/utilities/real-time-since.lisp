; Getting the time elapsed since some past time
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "get-real-time"))

(in-theory (disable mv-nth))

;; Returns (mv time-difference state) where time-difference is the difference
;; between now and PAST-TIME, which should be in the past.  Often, PAST-TIME
;; will be the result of a prior call to get-real-time.  PAST-TIME and the
;; returned time-difference are rational numbers of seconds.
(defund real-time-since (past-time state)
  (declare (xargs :guard (rationalp past-time)
                  :stobjs state))
  (let ((past-time (mbe :logic (rfix past-time) :exec past-time)))
    (mv-let (now state)
      (get-real-time state)
      (mv (- now past-time)
          state))))

(defthm rationalp-of-mv-nth-0-of-real-time-since
  (rationalp (mv-nth 0 (real-time-since past-time state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable real-time-since))))
