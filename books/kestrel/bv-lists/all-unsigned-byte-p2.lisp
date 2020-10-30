; More theorems about all-unsigned-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book mixes all-unsigned-byte-p with other non-buit-in functions

(include-book "all-unsigned-byte-p")
(include-book "../lists-light/repeat")
(include-book "../lists-light/reverse-list-def")

(defthm all-unsigned-byte-p-of-repeat
  (equal (all-unsigned-byte-p width (repeat n x))
         (or (zp n)
             (unsigned-byte-p width x)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p repeat))))

(defthm all-unsigned-byte-p-of-reverse-list
  (equal (all-unsigned-byte-p width (reverse-list x))
         (all-unsigned-byte-p width x))
  :hints (("Goal" :in-theory (enable reverse-list all-unsigned-byte-p))))
