; A lightweight book about the built-in function chk-length-and-keys
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm keyword-value-listp-when-not-mv-nth-0-of-chk-length-and-keys
  (implies (and (not (mv-nth 0 (chk-length-and-keys actuals form wrld)))
                (true-listp actuals))
           (keyword-value-listp actuals))
  :hints (("Goal" :in-theory (enable chk-length-and-keys keyword-value-listp))))
