; A lightweight book about the built-in function flatten-ands-in-lit
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable flatten-ands-in-lit))

(defthm pseudo-term-listp-of-flatten-ands-in-lit
  (implies (pseudo-termp term)
           (pseudo-term-listp (flatten-ands-in-lit term)))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit))))
