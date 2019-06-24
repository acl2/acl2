; A tiny book that provides the theorem all-unsigned-byte-p-of-reverse-list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-unsigned-byte-p")
(include-book "../lists-light/reverse-list")

(defthm all-unsigned-byte-p-of-reverse-list
  (equal (all-unsigned-byte-p width (reverse-list x))
         (all-unsigned-byte-p width x))
  :hints (("Goal" :in-theory (enable reverse-list all-unsigned-byte-p))))
