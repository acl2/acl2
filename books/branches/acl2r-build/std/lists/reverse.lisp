; Reverse lemmas
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
; reverse.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "revappend"))
(local (include-book "str/coerce" :dir :system))

(defsection std/lists/reverse
  :parents (std/lists reverse)
  :short "Lemmas about @(see reverse) available in the @(see std/lists)
library."

  :long "<p>The built-in @(see reverse) function is overly complex because it
can operate on either lists or strings.  To reverse a list, it is generally
preferable to use @(see rev), which has a very simple definition.</p>

<p>We ordinarily expect @('reverse') to be enabled, in which case it
expands (in the list case) to @('(revappend x nil)'), which we generally expect
to be rewritten to @('(rev x)') due to the @('revappend-removal') theorem.</p>

<p>Because of this, we do not expect these lemmas to be very useful unless, for
some reason, you have disabled @('reverse') itself.</p>"

  (defthm stringp-of-reverse
    (equal (stringp (reverse x))
           (stringp x)))

  (defthm true-listp-of-reverse
    (equal (true-listp (reverse x))
           (not (stringp x))))

  ;; ACL2's built-in type-prescription rule is weaker than it should be:
  ;;
  ;; (OR (CONSP (REVERSE X))
  ;;     (EQUAL (REVERSE X) NIL)
  ;;     (STRINGP (REVERSE X)))
  ;;
  ;; So let's install a better one...

  (in-theory (disable (:type-prescription reverse)))

  (defthm reverse-type
    (or (stringp (reverse x))
        (true-listp (reverse x)))
    :rule-classes :type-prescription)

  (local (defthm len-zero
           (equal (equal 0 (len x))
                  (atom x))))

  (local
   (defsection revappend-lemma

     (local (defun ind (a b x y)
              (if (or (atom a)
                      (atom b))
                  (list a b x y)
                (ind (cdr a) (cdr b)
                     (cons (car a) x)
                     (cons (car b) y)))))

     (local (defthm l0
              (implies (and (equal (len a) (len b))
                            (equal (len x) (len y)))
                       (equal (equal (revappend a x)
                                     (revappend b y))
                              (and (equal (list-fix a) (list-fix b))
                                   (equal x y))))
              :hints(("Goal" :induct (ind a b x y)))))

     (local (defthm l1
              (implies (and (not (equal (len a) (len b)))
                            (equal (len x) (len y)))
                       (equal (equal (revappend a x)
                                     (revappend b y))
                              nil))
              :hints(("Goal"
                      :in-theory (disable len-of-revappend)
                      :use ((:instance len-of-revappend (x a) (y x))
                            (:instance len-of-revappend (x b) (y y)))))))

     (local (defthm l2
              (implies (not (equal (len a) (len b)))
                       (not (equal (list-fix a) (list-fix b))))
              :hints(("Goal"
                      :in-theory (disable len-of-list-fix)
                      :use ((:instance len-of-list-fix (x a))
                            (:instance len-of-list-fix (x b)))))))

     (defthm revappend-lemma
       (implies (equal (len x) (len y))
                (equal (equal (revappend a x)
                              (revappend b y))
                       (and (equal (list-fix a) (list-fix b))
                            (equal x y))))
       :hints(("Goal"
               :in-theory (disable l0 l1)
               :use ((:instance l0)
                     (:instance l1)))))))

  (defthm equal-of-reverses
    ;; And this is why we should never use "reverse."
    (equal (equal (reverse x) (reverse y))
           (if (or (stringp x) (stringp y))
               (and (stringp x)
                    (stringp y)
                    (equal x y))
             (equal (list-fix x) (list-fix y))))
    :hints(("Goal" :cases ((stringp x)
                           (stringp y))))))

