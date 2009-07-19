; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
;
; Contact: Jared Davis <jared@cs.utexas.edu>
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
(include-book "defsort")
(include-book "misc/total-order" :dir :system)



; UNIQUEP.
;
; Uniquep, introduced below, is provably equal to no-duplicatesp, but has
; different performance characteristics.
;
; It operates by sorting its argument and then scanning for adjacent duplicates.
; This is an O(n log n) instead of O(n^2) operation, and it will be particularly
; fast on long, duplicate-free lists.
;
; On the other hand, it uses much more memory than no-duplicatesp, and it does
; not stop early when a duplicate is detected.  So, on lists with lots of
; duplication, no-duplicatesp may be preferable.

(defsort :compare< <<
         :prefix <<)

(defund no-adjacent-duplicates-p (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         t)
        (t
         (and (not (equal (car x) (cadr x)))
              (no-adjacent-duplicates-p (cdr x))))))

(defun uniquep (x)
  (declare (xargs :guard (true-listp x)
                  :verify-guards nil))
  (mbe :logic (no-duplicatesp-equal x)
       :exec (no-adjacent-duplicates-p (<<-sort x))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (<<-ordered-p x)
                   (equal (no-adjacent-duplicates-p x)
                          (no-duplicatesp-equal x)))
          :hints(("Goal" :in-theory (enable no-duplicatesp-equal
                                            no-adjacent-duplicates-p
                                            <<-ordered-p)))))
 
 (verify-guards uniquep))



#|| 

Below is only performance-test stuff.  Tested on CCL on Lisp2.

:q

(ccl::set-lisp-heap-gc-threshold (expt 2 30))

(defparameter *integers1* 
  ;; A test vector of 10,000 integers with many duplicates
  (loop for j from 1 to 10
        nconc
        (loop for i from 1 to 1000 collect i)))

(defparameter *integers2* 
  ;; A test vector of 10,000 integers with no duplicates
  (loop for i from 1 to 10000 collect i)))


;; In certain cases, no-duplicatesp-equal is much faster because a duplicate is
;; found right away.  For instance, on *integers1*, which contains lots of
;; duplicates, we only have to scan a little to find a match.

;; 0.0 seconds, no allocation
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 1000
                   do 
                   (let ((result (no-duplicatesp-equal *integers1*)))
                     (declare (ignore result))
                     nil))))

;; 4.2 seconds, 1.5 GB allocated
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 1000
                   do 
                   (let ((result (uniquep *integers1*)))
                     (declare (ignore result))
                     nil))))



;; In other cases, uniquep is much faster because it is O(n log n) instead of
;; O(n^2).

;; 27.4 seconds, no allocation.
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 100
                   do 
                   (let ((result (no-duplicatesp-equal *integers2*)))
                     (declare (ignore result))
                     nil))))


;; 0.2 seconds, 120 MB allocated
(prog2$ (ccl::gc)
        (time (loop for i fixnum from 1 to 100
                   do 
                   (let ((result (uniquep *integers2*)))
                     (declare (ignore result))
                     nil))))


||#