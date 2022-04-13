; A lightweight book about the built-in function resize-list
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Resize list is used by stobjs that have resizable array fields.

(in-theory (disable resize-list))

;; param names match std
(defthm len-of-resize-list
  (equal (len (resize-list lst n default))
         (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))
