; Theorems about perm and other non-built-in functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "perm")
(include-book "reverse-list")
(include-book "memberp-def")
(local (include-book "memberp"))

(defthm perm-of-reverse-list
  (perm (reverse-list x)
        x)
  :hints (("Goal" :in-theory (enable reverse-list))))

(defthmd memberp-when-perm
  (implies (perm x y)
           (equal (memberp a x)
                  (memberp a y)))
  :hints (("Goal" :in-theory (enable perm))
          ("subgoal *1/2" :cases ((equal a (car x))))))

(defcong perm equal (memberp a x) 2
  :hints (("Goal" :use (:instance member-equal-when-perm-iff (y x-equiv)))))
