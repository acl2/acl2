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

(defthm w-of-update-open-output-channels
  (equal (w (update-open-output-channels x state))
         (w state))
  :hints (("Goal" :in-theory (enable w update-open-output-channels))))

(defthm w-of-update-written-files
  (equal (w (update-written-files x state))
         (w state))
  :hints (("Goal" :in-theory (enable w update-written-files))))

(defthm w-of-update-file-clock
  (equal (w (update-file-clock x state))
         (w state))
  :hints (("Goal" :in-theory (enable w update-file-clock))))

(defthm w-of-update-acl2-oracle
  (equal (w (update-acl2-oracle x state))
         (w state))
  :hints (("Goal" :in-theory (enable w update-acl2-oracle))))

(defthm w-of-put-global
  (implies (not (equal key 'current-acl2-world))
           (equal (w (put-global key value state))
                  (w state)))
  :hints (("Goal" :in-theory (enable w put-global get-global))))
