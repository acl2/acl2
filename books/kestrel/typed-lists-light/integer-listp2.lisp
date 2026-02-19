; More theorems about integer-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Theorems that mix integer-listp with other non-built-in functions.

(include-book "integer-listp")
(include-book "kestrel/lists-light/repeat-def" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm integer-listp-of-firstn
  (implies (integer-listp lst)
           (integer-listp (firstn n lst)))
  :hints (("Goal" :in-theory (enable integer-listp firstn))))

(defthm integer-listp-of-subrange
  (implies (and (integer-listp x)
                (< end (len x))
                (natp start)
                (natp end))
           (integer-listp (subrange start end x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (integer-listp subrange take)
                           (;anti-subrange
                            )))))

(defthm integer-listp-of-reverse-list
  (implies (integer-listp x)
           (integer-listp (reverse-list x)))
  :hints (("Goal" :in-theory (enable reverse-list integer-listp))))

(defthm integer-listp-of-repeat-2
  (equal (integer-listp (repeat n x))
         (or (zp n)
             (integerp x)))
  :hints (("Goal" :in-theory (enable repeat))))
