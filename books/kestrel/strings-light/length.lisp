; A lightweight book about the built-in function LENGTH applied to strings
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(local (include-book "kestrel/utilities/coerce" :dir :system))

(in-theory (disable length)) ;; Not sure if we want this

(defthmd <-of-0-and-length-when-stringp
  (implies (stringp x)
           (equal (< 0 (length x))
                  (not (equal x ""))))
  :hints (("Goal" :in-theory (enable length))))

;; may cause loops with the coerce rules if length is enabled
(defthmd equal-of-empty-string-when-stringp
  (implies (stringp x)
           (equal (equal x "")
                  (equal 0 (length x))))
  :hints (("Goal" :in-theory (enable length))))

(defthm not-equal-of-empty-string-forward-to-<-of-0-and-length
  (implies (and (not (equal x ""))
                (stringp x))
           (< 0 (length x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable length))))
