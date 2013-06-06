; Repeat function and lemmas
; Copyright (C) 2005-2013 by Jared Davis <jared@cs.utexas.edu>
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
;
; repeat.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "rev")
(local (include-book "take"))
(local (include-book "nthcdr"))
(local (include-book "arithmetic/top" :dir :system))

(defsection repeat
  :parents (std/lists make-list)
  :short "@(call repeat) creates a list of @('x')es with length @('n'); it
is a simpler alternative to @(see make-list)."

  (defund repeat (x n)
    (declare (xargs :guard (natp n)
                    :verify-guards nil))
    (mbe :logic (if (zp n)
                    nil
                  (cons x (repeat x (- n 1))))

; On CCL, a simple loop of (loop for i from 1 to 10000 do (repeat 6 10000))
; finished in 2.74 seconds when we use make-list, versus 3.69 seconds when
; we use make-list-ac.  So lets use make-list.

         :exec (make-list n :initial-element x)))

  (local (in-theory (enable repeat)))

  (defthm repeat-when-zp
    (implies (zp n)
             (equal (repeat a n)
                    nil)))

  (defthm |(repeat x 0)|
    (equal (repeat x 0)
           nil))

  (defthm repeat-under-iff
    (iff (repeat x n)
         (not (zp n))))

  (defthm consp-of-repeat
    (equal (consp (repeat a n))
           (not (zp n))))

  (defthm repeat-1
    (equal (repeat a 1)
           (list a)))

  (defthm take-when-atom
    (implies (atom x)
             (equal (take n x)
                    (repeat nil n))))

  (defthm len-of-repeat
    (equal (len (repeat x n))
           (nfix n)))

  (defthm repeat-of-nfix
    (equal (repeat x (nfix n))
           (repeat x n)))

  (defthm car-of-repeat-increment
    ;; Goofy rule that helps when recurring when repeat is involved.
    ;; BOZO there's a better rule than this in str/arithmetic, but it case-splits.
    (implies (natp n)
             (equal (car (repeat x (+ 1 n)))
                    x)))

  (defthm cdr-of-repeat-increment
    ;; Goofy rule that helps when recurring when repeat is involved.
    (implies (natp n)
             (equal (cdr (repeat x (+ 1 n)))
                    (repeat x n))))

  (defthm member-of-repeat
    (equal (member a (repeat b n))
           (if (equal a b)
               (repeat b n)
             nil)))

  (encapsulate
    ()
    (local (defun dec-dec-induct (k n)
             (if (zp k)
                 nil
               (if (zp n)
                   nil
                 (dec-dec-induct (- k 1) (- n 1))))))

    (defthm take-of-repeat
      (equal (take n (repeat a k))
             (if (<= (nfix n) (nfix k))
                 (repeat a n)
               (append (repeat a k)
                       (repeat nil (- (nfix n) (nfix k))))))
      :hints(("Goal" :induct (dec-dec-induct k n))))

    (defthm nthcdr-of-repeat
      (equal (nthcdr n (repeat a k))
             (if (<= (nfix n) (nfix k))
                 (repeat a (- (nfix k) (nfix n)))
               nil))
      :hints(("Goal" :induct (dec-dec-induct k n)))))



  (encapsulate
    ()
    (local (include-book "append"))

    (local (defun silly-repeat (x n acc)
             (if (zp n)
                 acc
               (cons x (silly-repeat x (- n 1) acc)))))

    (local (defthm lemma1
             (equal (make-list-ac n x acc)
                    (silly-repeat x n acc))))

    (local (defthm lemma2
             (equal (silly-repeat x n acc)
                    (append (repeat x n) acc))))

    (defthmd make-list-ac->repeat
      ;; BOZO we should probably just enable this.
      (equal (make-list-ac n x acc)
             (append (repeat x n)
                     acc)))

    (verify-guards repeat
      :hints(("Goal" :in-theory (enable make-list-ac->repeat)))))


  (defthm append-of-repeat-to-cons-of-same
    (equal (append (repeat a n) (cons a x))
           (cons a (append (repeat a n) x))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (equal (append (repeat a n) x) y)
                      (and (equal (repeat a n) (take n y))
                           (equal (nthcdr n y) x)))))

    (local (defthm l1
             (implies (not (<= (nfix n) (len y)))
                      (not (equal (append (repeat a n) x) y)))))

    (local (defthm l2
             (implies (and (<= n (len y))
                           (equal (repeat a n) (take n y))
                           (equal x (nthcdr n y)))
                      (equal (append (repeat a n) x) y))
             :hints(("Goal"
                     :in-theory (disable append-of-take-and-nthcdr)
                     :use ((:instance append-of-take-and-nthcdr
                                      (n n)
                                      (x y)))))))

    (defthm equal-of-append-repeat
      (implies (case-split (<= n (len y)))
               (equal (equal (append (repeat a n) x) y)
                      (and (equal (repeat a n) (take n y))
                           (equal x (nthcdr n y)))))
      :hints(("Goal"
              :use ((:instance l0)
                    (:instance l2))))))

  (defthm rev-of-repeat
    (equal (rev (repeat a n))
           (repeat a n))))
