; A lightweight book about the built-in function all-fnnnames1
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also community book kestrel/std/system/all-fnnames.lisp.

(in-theory (disable all-fnnames1))

;; Same as in kestrel/std/system
(defthm symbol-listp-of-all-fnnnames1
  (implies (and (symbol-listp acc)
                (if flg (pseudo-term-listp x) (pseudo-termp x)))
           (symbol-listp (all-fnnames1 flg x acc)))
  :hints (("Goal" :in-theory (enable all-fnnames1))))
