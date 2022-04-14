; A lightweight book about the built-in function make-list-ac
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable make-list-ac))

(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc)))
  :hints (("Goal" :in-theory (enable make-list-ac))))
