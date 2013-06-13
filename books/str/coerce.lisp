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
;
; Additional copyright notice for coerce.lisp:
;
; This file is adapted from the Unicode library, Copyright (C) 2005-2013 by
; Jared Davis, which was also released under the GPL.

(in-package "STR")
(include-book "make-character-list")


(defsection str/coerce
  :parents (coercion coerce)
  :short "Lemmas about @(see coerce) available in the @(see str) library."

  :long "<p>We typically do not want to ever reason about coerce.  Instead, we
rewrite it away into @(see explode) or @(see implode).</p>"

  (local (defthm coerce-string-lemma
           (implies (and (character-listp x)
                         (character-listp y)
                         (not (equal x y)))
                    (not (equal (coerce x 'string)
                                (coerce y 'string))))
           :hints(("Goal" :use ((:instance coerce-inverse-1 (x x))
                                (:instance coerce-inverse-1 (x y)))))))

  (defthm equal-of-coerce-strings
    (implies (and (character-listp x)
                  (character-listp y))
             (equal (equal (coerce x 'string)
                           (coerce y 'string))
                    (equal x y))))

  (local (defthm coerce-list-lemma
           (implies (and (stringp x)
                         (stringp y)
                         (not (equal x y)))
                    (not (equal (coerce x 'list)
                                (coerce y 'list))))
           :hints(("Goal" :use ((:instance coerce-inverse-2 (x x))
                                (:instance coerce-inverse-2 (x y)))))))

  (defthm equal-of-coerce-lists
    (implies (and (stringp x)
                  (stringp y))
             (equal (equal (coerce x 'list)
                           (coerce y 'list))
                    (equal x y))))

  (defthm character-listp-of-coerce-list
    (character-listp (coerce x 'list)))

  (defthm coerce-list-under-iff
    (iff (coerce string 'list)
         (and (stringp string)
              (not (equal "" string))))
    :hints(("Goal"
            :in-theory (disable equal-of-coerce-lists)
            :use ((:instance equal-of-coerce-lists
                             (x string)
                             (y ""))))))


  (defthm length-of-coerce
    ;; Wow, coerce is sort of awful in that (coerce "foo" 'string) returns ""
    ;; and (coerce '(1 2 3) 'list) returns nil.  This leads to a weird length
    ;; theorem.  We normally just leave length enabled, so this rule won't have
    ;; many uses.
    (equal (length (coerce x y))
           (cond ((equal y 'list)
                  (if (stringp x)
                      (length x)
                    0))
                 (t
                  (if (stringp x)
                      0
                    (len x)))))
    :hints(("Goal"
            :use ((:instance completion-of-coerce
                             (x x)
                             (y y))))))

  (defthm len-of-coerce-to-string
    (equal (len (coerce x 'string))
           0))

  (defthm coerce-inverse-1-better
    (equal (coerce (coerce x 'string) 'list)
           (if (stringp x)
               nil
             (make-character-list x)))
    :hints(("Goal"
            :use ((:instance acl2::completion-of-coerce
                             (acl2::x x)
                             (acl2::y 'string))))))

  (defthm coerce-inverse-2-better
    (equal (coerce (coerce x 'list) 'string)
           (if (stringp x)
               x
             "")))

  (in-theory (disable coerce-inverse-1 coerce-inverse-2))

  (defthm coerce-to-list-of-make-character-list
    (equal (coerce (make-character-list x) 'string)
           (coerce x 'string))
    :hints(("Goal"
            :use ((:instance acl2::completion-of-coerce
                             (acl2::x x)
                             (acl2::y 'string)))))))



(defsection explode
  :parents (coercion coerce)
  :short "Convert a string to a character list."

  :long "<p>@(call explode) is logically nothing more than @('(coerce x
'list)').</p>

<p>Even though @(see coerce) is built into ACL2, we prefer to use @('explode') as
our normal form.  We rewrite all uses of @('(coerce x 'list)') into
@('(str::explode x')') with the following rule:</p>

@(def coerce-to-list-removal)

<p>The basic rationale for this is that @('coerce')'s extra @(''list') argument
means we can't write, e.g., congruence relations about @('(coerce x 'list)'),
whereas this is no problem for @('(explode x)').</p>

<p>We do the same thing for @('(coerce x 'string)') &mdash; see @(see
pack).</p>

<p><b>BOZO</b> consider using misc/fast-coerce here.</p>"

  (definlined explode (x)
    (declare (type string x))
    (coerce x 'list))

  (in-theory (disable (:t explode)))
  (local (in-theory (enable explode)))

  (defthm true-listp-of-explode
    (true-listp (explode x))
    :rule-classes :type-prescription)

  (defthm character-listp-of-explode
    (character-listp (explode x)))

  (defthm explode-when-not-stringp
    (implies (not (stringp x))
             (equal (explode x)
                    nil)))

  (defthm equal-of-explodes
    (implies (and (stringp x)
                  (stringp y))
             (equal (equal (explode x)
                           (explode y))
                    (equal x y))))

  (defthm explode-under-iff
    (iff (explode string)
         (and (stringp string)
              (not (equal "" string)))))

  (local (defthm l0
           (implies (true-listp x)
                    (iff (consp x)
                         x))))

  (defthm consp-of-explode
    (equal (consp (explode string))
           (and (stringp string)
                (not (equal "" string)))))

  (defthm coerce-to-list-removal
    (equal (coerce x 'list)
           (explode x)))

  (local (in-theory (disable acl2::explode)))

  (theory-invariant (incompatible (:definition acl2::explode$inline)
                                  (:rewrite coerce-to-list-removal))))



(defsection implode
  :parents (coercion coerce)
  :short "Convert a character list into a string."

  :long "<p>@(call implode) is logically nothing more than @('(coerce x
'string)').</p>

<p>Even though @(see coerce) is built into ACL2, we prefer to use @('implode')
as our normal form.  We rewrite all uses of @('(coerce x 'string)') into
@('(str::implode x')') with the following rule:</p>

@(def coerce-to-string-removal)

<p>The basic rationale for this is that @('coerce')'s extra @(''string')
argument means we can't write, e.g., congruence relations about @('(coerce x
'string)'), whereas this is no problem for @('(implode x)').</p>

<p>We do the same thing for @('(coerce x 'list)') &mdash; see @(see
explode).</p>"

  (definlined implode (x)
    (declare (xargs :guard (character-listp x)))
    (coerce x 'string))

  (in-theory (disable (:t implode)))
  (local (in-theory (enable implode)))

  (defthm stringp-of-implode
    (stringp (implode x))
    :rule-classes :type-prescription)

  (defthm equal-of-implodes
    (implies (and (character-listp x)
                  (character-listp y))
             (equal (equal (implode x)
                           (implode y))
                    (equal x y))))

  (defthm implode-of-make-character-list
    (equal (implode (make-character-list x))
           (implode x)))

  (local (defthm l0
           (equal (equal (len x) 0)
                  (atom x))))

  (defthm equal-of-implode-with-empty-string
    (equal (equal "" (implode x))
           (atom x))
    :hints(("Goal"
            :in-theory (disable length-of-coerce)
            :use ((:instance length-of-coerce
                             (x x)
                             (y 'string))))))

  (defthm coerce-to-string-removal
    (equal (coerce x 'string)
           (implode x)))

  (local (in-theory (disable acl2::implode$inline)))

  (theory-invariant (incompatible (:definition acl2::implode$inline)
                                  (:rewrite coerce-to-string-removal))))



(defsection implode-explode-inversion
  :parents (implode explode)
  :short "Inversion theorems for @(see implode) and @(see explode)."

  (local (in-theory (e/d (implode explode)
                         (coerce-to-string-removal
                          coerce-to-list-removal))))

  (defthm explode-of-implode
    (equal (explode (implode x))
           (if (stringp x)
               nil
             (make-character-list x))))

  (defthm implode-of-explode
    (equal (implode (explode x))
           (if (stringp x)
               x
             ""))))

