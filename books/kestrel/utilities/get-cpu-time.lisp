; A lightweight book about the built-in function get-cpu-time.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "state"))

(in-theory (disable get-cpu-time))

;move
(defthm state-p-of-update-acl2-oracle
  (implies (and (state-p state)
                (true-listp x))
           (state-p (update-acl2-oracle x state)))
  :hints (("Goal" :in-theory (enable state-p))))

;move
(defthm rationalp-of-mv-nth-0-of-read-run-time
  (rationalp (mv-nth 0 (read-run-time state)))
  :hints (("Goal" :in-theory (enable read-run-time))))

(defthm state-p-of-mv-nth-1-of-read-run-time
  (implies (state-p state)
           (state-p (mv-nth 1 (read-run-time state))))
  :hints (("Goal" :in-theory (enable read-run-time))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rationalp-of-mv-nth-0-of-get-cpu-time
  (rationalp (mv-nth 0 (get-cpu-time state)))
  :hints (("Goal" :in-theory (enable get-cpu-time))))

(defthm state-p-of-mv-nth-1-of-get-cpu-time
  (implies (state-p state)
           (state-p (mv-nth 1 (get-cpu-time state))))
  :hints (("Goal" :in-theory (enable get-cpu-time))))
