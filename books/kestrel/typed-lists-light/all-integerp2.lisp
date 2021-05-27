; More theorems about all-integerp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Theorems that mix all-integerp with other non-built-in functions.

(include-book "all-integerp")
;(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defthm all-integerp-of-firstn
  (implies (all-integerp lst)
           (all-integerp (firstn n lst)))
  :hints (("Goal" :in-theory (enable all-integerp firstn))))

(defthm all-integerp-of-subrange
  (implies (and (all-integerp x)
                (< end (len x))
                (natp start)
                (natp end))
           (all-integerp (subrange start end x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (all-integerp subrange take)
                           (;anti-subrange
                            )))))

(defthm all-integerp-of-reverse-list
  (equal (all-integerp (reverse-list x))
         (all-integerp x))
  :hints (("Goal" :in-theory (enable reverse-list all-integerp))))
