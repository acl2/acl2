; Checking that everything in a list is <= a bound
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sequences/defforall" :dir :system) ;reduce?
(local (include-book "kestrel/lists-light/revappend" :dir :system))

(defforall all-<= (x n) (<= x n) :fixed (n) :declares ((xargs :guard (and (rational-listp x) (rationalp n))))) ;why did (rationalp x) work as a guard?

(defthm all-<=-monotone
  (implies (and (all-<= items m)
                (<= m n))
           (all-<= items n))
  :hints (("Goal" :in-theory (enable all-<=))))

;restrict?
(defthmd <=-of-nth-when-all-<=
  (implies (and (all-<= items x)
                ;(consp items)
                (natp x)
                )
           (<= (nth n items) x))
  :hints (("Goal" :in-theory (e/d (all-<= nth) ()))))

(defthm <=-of-nth-when-all-<=-free
  (implies (and (all-<= items x2)
                (<= x2 x)
                ;(consp items)
                (natp x)
                )
           (<= (nth n items) x))
  :hints (("Goal" :in-theory (e/d (all-<= nth) ()))))

(defthm not-all-<=-when-<-and-member-equal
  (implies (and (< n free)
                (member-equal free x))
           (not (all-<= x n))))

;todo: have deffoall prove this one instead
(defthm all-<=-of-revappend-strong
  (equal (all-<= (revappend x1 x2) n)
         (and (all-<= x1 n)
              (all-<= x2 n)))
  :hints (("Goal" :in-theory (enable all-<=))))
