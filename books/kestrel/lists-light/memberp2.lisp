; More theorems about memberp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book includes theorems that mention memberp and other non-built-in functions.

(include-book "memberp")
(include-book "reverse-list-def")
(include-book "subrange-def")
(include-book "perm") ; provides the defequiv
(local (include-book "take"))
(local (include-book "subrange"))

(defthm memberp-of-reverse-list
  (equal (memberp a (reverse-list lst))
         (memberp a lst))
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthm memberp-of-nth-and-subrange
  (implies (and (<= start n)
                (<= n end)
                (< end (len lst))
                (natp n)
                (natp end)
                (natp start)
                )
           (memberp (nth n lst) (subrange start end lst)))
  :hints (("Goal" :use (:instance NTH-OF-SUBRANGE (n (- n start)))
           :do-not-induct t
           :in-theory (disable NTH-OF-SUBRANGE))))

(defcong perm equal (memberp a x) 2
  :hints (("Goal" :use (:instance member-equal-when-perm-iff (y x-equiv)))))
