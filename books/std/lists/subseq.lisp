; Lemmas about subseq functions
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "equiv")
(local (include-book "take"))
(local (include-book "nthcdr"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; BOZO, the built-in type prescription for subseq-list is lousy,
;;   (or (consp x) (equal x nil) (stringp x)),
;; so replace it with something more sensible:

(in-theory (disable (:type-prescription subseq-list)))

(defthm true-listp-subseq-list
  (true-listp (subseq-list x start end))
  :rule-classes :type-prescription)

(defthm len-of-subseq-list
  (equal (len (subseq-list x start end))
         (nfix (- end start))))

(defthm consp-of-subseq-list
  (equal (consp (subseq-list x start end))
         (posp (- end start))))

(defthm subseq-list-under-iff
  (iff (subseq-list x start end)
       (posp (- end start))))

(defthm subseq-list-of-list-fix
  (equal (subseq-list (list-fix x) start end)
         (subseq-list x start end)))

(defcong list-equiv equal (subseq-list x start end) 1)

(defthm subseq-list-starting-from-zero
  ;; BOZO.  It'd be nicer to prove this about (subseq-list x start n) whenever
  ;; (zp start).  Unfortunately SUBSEQ-LIST doesn't properly NFIX its START
  ;; argument.  Instead, in the logic, when START is a negative number, we end
  ;; up doing a longer TAKE, which is sort of appalling.
  (equal (subseq-list x 0 n)
         (take n x))
  :hints(("Goal" :in-theory (enable subseq-list))))

(defthm subseq-list-of-len
  ;; BOZO.  Similarly this rule needs a natp hyp and we can't just get away
  ;; from it using something like NFIX.  The problem is again that if N is,
  ;; say, a negative number, then we can do a larger take.
  (implies (natp n)
           (equal (subseq-list x n (len x))
                  (nthcdr n (list-fix x))))
  :hints(("Goal" :in-theory (enable take-redefinition))))

; We could strengthen the above rules by turning them into something like (take
; n (append x (repeat nil (- start)))) in the negative case, but that is
; probably nothing anyone would expect to see or should ever try to reason
; about.
