; A lightweight book the built-in function pseudo-term-list-listp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable pseudo-term-list-listp))

(defthm pseudo-term-listp-of-car-when-pseudo-term-list-listp
  (implies (pseudo-term-list-listp lists)
           (pseudo-term-listp (car lists)))
  :hints (("Goal" :in-theory (enable pseudo-term-list-listp))))
