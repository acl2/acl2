; A lightweight book about the built-in function iprint-oracle-updates.
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is in the file-io-light library because iprint-oracle-updates is
;; called by read-object.

(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/read-acl2-oracle" :dir :system))
(local (include-book "channels"))

;(local (in-theory (disable mv-nth open-input-channels)))

(defthm open-input-channels-of-iprint-oracle-updates
  (equal (open-input-channels (iprint-oracle-updates state))
         (open-input-channels state))
  :hints (("Goal" :in-theory (e/d (iprint-oracle-updates)
                                  (;; for speed:
                                   nfix)))))

(defthm state-p1-of-iprint-oracle-updates
  (implies (state-p1 state)
           (state-p1 (iprint-oracle-updates state)))
  :hints (("Goal" :in-theory (e/d (iprint-oracle-updates)
                                  (;; for speed:
                                   array1p
                                   iprint-last-index*
                                   nfix)))))

(defthm state-p-of-iprint-oracle-updates
  (implies (state-p state)
           (state-p (iprint-oracle-updates state)))
  :hints (("Goal" :in-theory (e/d (iprint-oracle-updates)
                                  (;; for speed:
                                   array1p
                                   iprint-last-index*
                                   nfix)))))
