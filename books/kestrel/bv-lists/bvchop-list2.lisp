; BV Lists Library: More theorems about bvchop-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2012 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains rules that mix bvchop-list and other non-built-in functions.

(include-book "bvchop-list")
(include-book "../lists-light/repeat")

(defthm bvchop-list-of-0
  (equal (bvchop-list 0 lst)
         (repeat (len lst) 0))
  :hints (("Goal" :in-theory (enable bvchop-list))))
