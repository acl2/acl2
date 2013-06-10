; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
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
(include-book "uniquep")

(defund remove-adjacent-duplicates (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (car x)))
        ((equal (car x) (cadr x))
         (remove-adjacent-duplicates (cdr x)))
        (t
         (cons (car x)
               (remove-adjacent-duplicates (cdr x))))))

(defthm true-listp-of-remove-adjacent-duplicates
  (true-listp (remove-adjacent-duplicates x))
  :rule-classes :type-prescription)

(defthm consp-of-remove-adjacent-duplicates
  (equal (consp (remove-adjacent-duplicates x))
         (consp x))
  :hints(("Goal" :in-theory (enable remove-adjacent-duplicates))))

(defthm remove-adjacent-duplicates-under-iff
  (iff (remove-adjacent-duplicates x)
       (consp x))
  :hints(("Goal" :in-theory (enable remove-adjacent-duplicates))))

(defthm member-equal-of-remove-adjacent-duplicates
  (iff (member-equal a (remove-adjacent-duplicates x))
       (member-equal a x))
  :hints(("Goal" :in-theory (enable remove-adjacent-duplicates))))

(defthm no-duplicatesp-equal-of-remove-adjacent-duplicates
  (implies (<<-ordered-p x)
           (no-duplicatesp-equal (remove-adjacent-duplicates x)))
  :hints(("Goal" :in-theory (enable remove-adjacent-duplicates
                                    <<-ordered-p))))

(defund remove-dups (x)
  (declare (xargs :guard (true-listp x)))
  (remove-adjacent-duplicates (<<-sort x)))

(defthm true-listp-of-remove-dups
  (equal (true-listp (remove-dups x))
         t)
  :hints(("Goal" :in-theory (enable remove-dups))))

(encapsulate
 ()
 (local (defthm member-equal-is-duplicity
          (iff (member-equal a x)
               (< 0 (duplicity a x)))))

 (defthm member-equal-of-<<-sort
   (iff (member-equal a (<<-sort x))
        (member-equal a x))))

(defthm member-equal-of-remove-dups
  (iff (member-equal a (remove-dups x))
       (member-equal a x))
  :hints(("Goal" :in-theory (enable remove-dups))))

(defthm no-duplicatesp-equal-of-remove-dups
  (no-duplicatesp-equal (remove-dups x))
  :hints(("Goal" :in-theory (enable remove-dups))))




#||

(include-book
  "remove-dups")

(include-book "misc/hons-help" :dir :system)

:q

(ccl::set-lisp-heap-gc-threshold (expt 2 34))

(defparameter *integers1*
  ;; A test vector of 10,000 integers with many duplicates
  (loop for j from 1 to 10
        nconc
        (loop for i from 1 to 1000 collect i)))

(defparameter *integers2*
  ;; A test vector of 10,000 integers with no duplicates
  (loop for i from 1 to 10000 collect i)))

;; 5.3 seconds, 1.5 GB allocated
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (remove-dups *integers1*)))
                     (declare (ignore result))
                     nil))))

;; 2.0 seconds, 117 MB allocated
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (hons-remove-duplicates *integers1*)))
                     (declare (ignore result))
                     nil))))

;; 0.49 seconds, 135 MB allocated
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 100
                   do
                   (let ((result (remove-dups *integers2*)))
                     (declare (ignore result))
                     nil))))


;; 1.1 seconds, 128 MB allocated
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 100
                   do
                   (let ((result (hons-remove-duplicates *integers2*)))
                     (declare (ignore result))
                     nil))))

||#