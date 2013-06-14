; Take lemmas
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
; take.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "arithmetic/top" :dir :system))

(defun simpler-take-induction (n xs)
  ;; Not generally meant to be used; only meant for take-induction
  ;; and take-redefinition.
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take-induction (1- n) (cdr xs)))))


(in-theory (disable (:definition take)))

(defsection std/lists/take
  :parents (std/lists take)
  :short "Lemmas about @(see take) available in the @(see std/lists) library."

  :long "<p>ACL2's built-in definition of @('take') is not especially good for
reasoning since it is written in terms of the tail-recursive function
@('first-n-ac').  We provide a much nicer @(see definition) rule:</p>

  @(def take-redefinition)

<p>And we also set up an analogous @(see induction) rule.  We generally
recommend using @('take-redefinition') instead of @('(:definition take)').</p>"

  (encapsulate
    ()
    (local (in-theory (enable take)))

    (local (defthm equivalence-lemma
             (implies (true-listp acc)
                      (equal (first-n-ac n xs acc)
                             (revappend acc (simpler-take-induction n xs))))))

    (defthm take-redefinition
      (equal (take n x)
             (if (zp n)
                 nil
               (cons (car x)
                     (take (1- n) (cdr x)))))
      :rule-classes ((:definition :controller-alist ((TAKE T NIL))))))

  (defthm take-induction t
    :rule-classes ((:induction
                    :pattern (take n x)
                    :scheme (simpler-take-induction n x))))

  ;; The built-in type-prescription for take is awful:
  ;;
  ;; (OR (CONSP (TAKE N L))
  ;;            (EQUAL (TAKE N L) NIL)
  ;;            (STRINGP (TAKE N L)))
  ;;
  ;; So fix it...

  (in-theory (disable (:type-prescription take)))

  (defthm true-listp-of-take
    (true-listp (take n xs))
    :rule-classes :type-prescription)

  (defthm consp-of-take
    (equal (consp (take n xs))
           (not (zp n))))

  (defthm take-under-iff
    (iff (take n xs)
         (not (zp n))))

  (defthm len-of-take
    (equal (len (take n xs))
           (nfix n)))

  (defthm take-of-cons
    (equal (take n (cons a x))
           (if (zp n)
               nil
             (cons a (take (1- n) x)))))

  (defthm take-of-append
    (equal (take n (append x y))
           (if (< (nfix n) (len x))
               (take n x)
             (append x (take (- n (len x)) y))))
    :hints(("Goal" :induct (take n x))))

  (defthm take-of-zero
    (equal (take 0 x)
           nil))

  (defthm take-of-1
    (equal (take 1 x)
           (list (car x))))

  (defthm car-of-take
    (implies (<= 1 (nfix n))
             (equal (car (take n x))
                    (car x))))

  (defthm second-of-take
    (implies (<= 2 (nfix n))
             (equal (second (take n x))
                    (second x))))

  (defthm third-of-take
    (implies (<= 3 (nfix n))
             (equal (third (take n x))
                    (third x))))

  (defthm fourth-of-take
    (implies (<= 4 (nfix n))
             (equal (fourth (take n x))
                    (fourth x))))

  (defthm take-of-len-free
    (implies (equal len (len x))
             (equal (take len x)
                    (list-fix x))))

  (defthm take-of-len
    (equal (take (len x) x)
           (list-fix x)))

  (defthm subsetp-of-take
    (implies (<= (nfix n) (len x))
             (subsetp (take n x) x)))

  (defthm take-fewer-of-take-more
    ;; Note: see also repeat.lisp for related cases and a stronger rule that
    ;; case-splits.
    (implies (<= (nfix a) (nfix b))
             (equal (take a (take b x))
                    (take a x))))

  (defthm take-of-take-same
    ;; Note: see also repeat.lisp for related cases and a stronger rule that
    ;; case-splits.
    (equal (take a (take a x))
           (take a x))))


(defsection first-n
  :parents (std/lists take)
  :short "@(call first-n) is logically identical to @('(take n x)'), but its
guard does not require @('(true-listp x)')."

  (local (defun repeat (x n)
           (if (zp n)
               nil
             (cons x (repeat x (- n 1))))))

  (local (defthm l0
           (equal (append (repeat x n) (cons x y))
                  (cons x (append (repeat x n) y)))))

  (local (defthm l1
           (equal (make-list-ac n val acc)
                  (append (repeat val n) acc))
           :hints(("Goal"
                   :induct (make-list-ac n val acc)))))

  (local (defthm l2
           (implies (atom x)
                    (equal (take n x)
                           (make-list n)))))

  (defun first-n (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (take n x)
         :exec
         (cond ((zp n)
                nil)
               ((atom x)
                (make-list n))
               (t
                (cons (car x)
                      (first-n (- n 1) (cdr x))))))))
