; A book about the built-in function msgp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable msgp))

(defthm msgp-of-cons
  (equal (msgp (cons str alist))
         (and (stringp str)
              (character-alistp alist)))
  :hints (("Goal" :in-theory (enable msgp))))
