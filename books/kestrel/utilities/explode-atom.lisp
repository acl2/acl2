; A lightweight book about the built-in function explode-atom
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "explode-nonnegative-integer"))

(defthm character-listp-of-explode-atom
  (character-listp (explode-atom x print-base))
  :hints (("Goal" :in-theory (enable explode-atom))))
