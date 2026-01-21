; Checking that a value is < all members of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(defund <-all (x y)
  (if (endp y)
      t
    (and (< x (first y))
         (<-all x (rest y)))))

(defthmd <-of-car-when-<-all
  (implies (and (<-all x y)
                (consp y))
           (< x (car y)))
  :hints (("Goal" :in-theory (enable <-all))))

(defthm <-all-of-append
  (equal (<-all a (append x y))
         (and (<-all a x)
              (<-all a y)))
  :hints (("Goal" :in-theory (enable <-all reverse-list))))

(defthm <-all-of-reverse-list
  (equal (<-all a (reverse-list x))
         (<-all a x))
  :hints (("Goal" :in-theory (enable <-all reverse-list))))

(defthm <-all-revappend
  (equal (<-all a (revappend x y))
         (and (<-all a x)
              (<-all a y)))
  :hints (("Goal" :in-theory (enable <-all revappend-becomes-append-of-reverse-list))))
