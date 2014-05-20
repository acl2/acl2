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
(include-book "defsort")
(include-book "misc/total-order" :dir :system)

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

(defsection uniquep
  :parents (no-duplicatesp)
  :short "Sometimes better than @(see no-duplicatesp): first sorts the list and
then looks for adjacent duplicates."

  :long "<p>@(call uniquep) is provably equal to @('(no-duplicatesp x)'), but
has different performance characteristics.  It operates by sorting its argument
and then scanning for adjacent duplicates.</p>

<p>Since we use a mergesort, the complexity of @('uniquep') is @('O(n log n)').
By comparison, @('no-duplicatesp') is @('O(n^2)').</p>

<p>It is not always better to use @('uniquep') than @('no-duplicatesp'):</p>

<ul>

<li>It uses far more memory than @('no-duplicatesp') because it sorts the
list.</li>

<li>On a list with lots of duplicates, @('no-duplicatesp') may find a duplicate
very quickly and stop early, but @('uniquep') has to sort the whole list before
it looks for any duplicates.</li>

</ul>

<p>However, if your lists are sometimes long with few duplicates, @('uniquep')
is probably a much better function to use.</p>"

  (defun uniquep-exec (x)
    (declare (xargs :guard (true-listp x)
                    :verify-guards nil))
    (mbe :logic (no-duplicatesp x)
         :exec (no-adjacent-duplicates-p (<<-sort x))))

  (defmacro uniquep (x)
    ;; Based on the equality-variants documentation, I think this is what we
    ;; want to do so that we can prove theorems about uniquep and have them
    ;; apply to no-duplicatesp.
    ;; Note (Matt K.): Added :guardp nil on 5/19/2014 for let-mbe mod that
    ;; provides better guard-checking, to get the old let-mbe behavior.
    `(let-mbe ((x ,x))
              :guardp nil
              :logic (no-duplicatesp x)
              :exec (uniquep-exec x)))

  (local (defthm lemma
           (implies (<<-ordered-p x)
                    (equal (no-adjacent-duplicates-p x)
                           (no-duplicatesp x)))
           :hints(("Goal" :in-theory (enable no-duplicatesp
                                             no-adjacent-duplicates-p
                                             <<-ordered-p)))))

  (verify-guards uniquep-exec)

  (add-macro-alias uniquep no-duplicatesp-equal))


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