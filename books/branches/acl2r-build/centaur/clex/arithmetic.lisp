; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/util/defrule" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "str/arithmetic" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(in-theory (disable nth
                    update-nth
                    ;; These can interfere with stobj stuff
                    nth-0-cons
                    nth-when-zp
                    nth-add1))

(local (in-theory (enable nthcdr len nth)))

(defrule nthcdr-of-len
  (implies (true-listp x)
           (equal (nthcdr (len x) x)
                  nil)))

(defrule nthcdr-of-len-free
  (implies (and (equal n (len x))
                (true-listp x))
           (equal (nthcdr n x)
                  nil)))

(defrule cdr-of-nthcdr
  (equal (cdr (nthcdr n x))
         (nthcdr (+ 1 (nfix n)) x)))

(defrule nth-when-index-too-big
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil)))

;; now part of std/lists
;; (defrule nth-of-nthcdr
;;   (equal (nth a (nthcdr b x))
;;          (nth (+ (nfix a) (nfix b)) x))
;;   :disable (acl2::nthcdr-of-cdr))

(defrule nthcdr-under-iff-when-true-listp
  (implies (true-listp x)
           (iff (nthcdr n x)
                (< (nfix n) (len x)))))

(defthm true-listp-when-character-listp
  (implies (character-listp x)
           (true-listp x)))

(defthm character-listp-of-nthcdr
  (implies (character-listp x)
           (character-listp (nthcdr n x)))
  :hints(("Goal" :in-theory (disable acl2::cdr-of-nthcdr))))

(defthm character-listp-of-take
  (implies (character-listp x)
           (equal (character-listp (take n x))
                  (<= (nfix n) (len x)))))
