; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(include-book "arithmetic/top" :dir :system)
(include-book "unicode/nthcdr" :dir :system)

;; This whole file is a "bozo" that we should consider moving elsewhere.

(defthm negative-when-natp
  (implies (natp x) (equal (< x 0) nil)))

(defthm eqlablep-when-characterp
  (implies (characterp x) (eqlablep x)))

(defthm len-zero
  (equal (equal 0 (len x))
         (not (consp x))))

(defthm nth-of-len
  (equal (nth (len x) x)
         nil))

(defthm nth-when-bigger
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil))
  :hints(("Goal" :in-theory (enable nth))))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr a (nthcdr b x))
         (nthcdr (+ (nfix a) (nfix b)) x)))

(encapsulate
 ()
 (local (defthmd lemma1
          (implies (true-listp x)
                   (true-listp (nthcdr n x)))
          :hints(("Goal" :in-theory (enable nthcdr)))))

 (local (defthmd lemma2
          (implies (< (len x) (nfix n))
                   (true-listp (nthcdr n x)))
          :hints(("Goal" :in-theory (enable nthcdr)))))

 (local (defthmd lemma3
          (implies (and (not (true-listp x))
                        (not (< (len x) (nfix n))))
                   (not (true-listp (nthcdr n x))))
          :hints(("Goal" :in-theory (enable nthcdr)))))

 (defthm true-listp-of-nthcdr
   (equal (true-listp (nthcdr n x))
          (or (true-listp x)
              (< (len x) (nfix n))))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary (implies (true-listp x)
                                                          (true-listp (nthcdr n x)))))
   :hints(("Goal"
           :in-theory (disable nthcdr)
           :use ((:instance lemma1)
                 (:instance lemma2)
                 (:instance lemma3))))))
