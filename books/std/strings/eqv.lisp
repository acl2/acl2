; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "STR")
(include-book "coerce")
(include-book "std/lists/equiv" :dir :system)
(include-book "std/lists/rev" :dir :system)
(local (include-book "arithmetic"))

(in-theory (disable char<))

(defsection char<-order-thms
  :parents (char<)
  :short "Basic ordering facts about @('char<')."

  (local (in-theory (enable char< char-fix)))

  (defthm char<-irreflexive
    (equal (char< x x)
           nil))

  (defthm char<-antisymmetric
    (implies (char< x y)
             (not (char< y x))))

  (defthm char<-transitive
    (implies (and (char< x y)
                  (char< y z))
             (char< x z)))

  (defthm char<-trichotomy-weak
    (implies (and (not (char< x y))
                  (not (char< y x)))
             (equal (chareqv x y)
                    t))
    :hints(("Goal" :in-theory (enable chareqv))))

  (defthm char<-trichotomy-strong
    (equal (char< x y)
           (and (not (chareqv x y))
                (not (char< y x))))
    :rule-classes ((:rewrite :loop-stopper ((x y))))))


(define charlisteqv ((x character-listp)
                     (y character-listp))
  :returns equivp
  :parents (equivalences)
  :short "Case-sensitive character-list equivalence test."

  :long "<p>@(call charlisteqv) determines if @('x') and @('y') are equivalent
when interpreted as character lists.  That is, @('x') and @('y') must have the
same length and their elements must be @(see chareqv) to one another.</p>

<p>See also @(see icharlisteqv) for a case-insensitive alternative.</p>"

  (if (consp x)
      (and (consp y)
           (chareqv (car x) (car y))
           (charlisteqv (cdr x) (cdr y)))
    (atom y))
  ///
  (defequiv charlisteqv)
  (defrefinement list-equiv charlisteqv
    :hints(("Goal" :in-theory (enable list-equiv))))

  (defcong charlisteqv chareqv     (car x)      1)
  (defcong charlisteqv charlisteqv (cdr x)      1)
  (defcong chareqv     charlisteqv (cons a x)   1)
  (defcong charlisteqv charlisteqv (cons a x)   2)
  (defcong charlisteqv equal       (len x)      1)
  (defcong charlisteqv charlisteqv (list-fix x) 1)
  (defcong charlisteqv chareqv     (nth n x)    2)
  (defcong charlisteqv charlisteqv (take n x)   2)
  (defcong charlisteqv charlisteqv (nthcdr n x) 2)
  (defcong charlisteqv charlisteqv (append x y) 1)
  (defcong charlisteqv charlisteqv (append x y) 2)
  (defcong charlisteqv charlisteqv (rev x)      1)
  (defcong charlisteqv charlisteqv (revappend x y) 2)
  (defcong charlisteqv charlisteqv (revappend x y) 1)

  (encapsulate
    ()
    (local (defun my-induct (x y)
             (if (atom x)
                 (list x y)
               (my-induct (cdr x) (cdr y)))))

    (defcong charlisteqv equal (make-character-list x) 1
      :hints(("Goal"
              :in-theory (enable chareqv)
              :induct (my-induct x x-equiv)))))

  (encapsulate
    ()
    (local (defun my-induct (x y)
             (if (atom x)
                 (list x y)
               (my-induct (cdr x) (cdr y)))))

    (local (defthm crock
             (equal (charlisteqv x y)
                    (equal (make-character-list x)
                           (make-character-list y)))
             :hints(("Goal"
                     :in-theory (enable chareqv)
                     :induct (my-induct x y)))))

    (defcong charlisteqv equal (implode x) 1
      :hints(("Goal"
              :in-theory (disable implode-of-make-character-list)
              :use ((:instance implode-of-make-character-list (x x))
                    (:instance implode-of-make-character-list (x x-equiv)))))))

  (defthm charlisteqv-when-not-consp-left
    (implies (not (consp x))
             (equal (charlisteqv x y)
                    (atom y))))

  (defthm charlisteqv-when-not-consp-right
    (implies (not (consp y))
             (equal (charlisteqv x y)
                    (atom x))))

  (defthm charlisteqv-of-cons-right
    (equal (charlisteqv x (cons a y))
           (and (consp x)
                (chareqv (car x) (double-rewrite a))
                (charlisteqv (cdr x) (double-rewrite y)))))

  (defthm charlisteqv-of-cons-left
    (equal (charlisteqv (cons a x) y)
           (and (consp y)
                (chareqv (double-rewrite a) (car y))
                (charlisteqv (double-rewrite x) (cdr y)))))

  (defthm charlisteqv-when-not-same-lens
    (implies (not (equal (len x) (len y)))
             (not (charlisteqv x y)))))


;; BOZO kind of misplaced
(defcong streqv equal (explode x) 1
  :hints(("Goal" :in-theory (enable streqv str-fix))))

