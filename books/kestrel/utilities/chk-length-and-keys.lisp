; A lightweight book about the built-in function chk-length-and-keys
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These forms are redudant except when doing a devel regression.  They seem
;; necessary, because this book supports verifying the guards of some system
;; functions, which means this book must certify with a "devel" copy of ACL2,
;; in which certain functions are in :program mode:
#+acl2-devel
(progn (verify-termination macro-args) ; and guards
       (verify-termination er-cmp-fn) ; and guards
       (verify-termination chk-length-and-keys)
       )

(defthm keyword-value-listp-when-not-mv-nth-0-of-chk-length-and-keys
  (implies (and (not (mv-nth 0 (chk-length-and-keys actuals form wrld)))
                (true-listp actuals))
           (keyword-value-listp actuals))
  :hints (("Goal" :in-theory (enable chk-length-and-keys keyword-value-listp))))
