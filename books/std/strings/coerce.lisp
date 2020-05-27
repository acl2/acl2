; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
;
; Additional Copyright Notice.
;
; This file is adapted from the Unicode library, Copyright (C) 2005-2013 by
; Kookamara LLC, which is also available under an MIT/X11 style license.

(in-package "STR")
(include-book "make-character-list")


(defsection std/strings/coerce
  :parents (coercion coerce)
  :short "Lemmas about @(see coerce) available in the @(see std/strings) library."

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

  ;; Redundant with built-in ACL2 rule character-listp-coerce
  ;; (defthm character-listp-of-coerce-list
  ;;   (character-listp (coerce x 'list)))

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



(define explode ((x :type string))
  :returns (chars character-listp)
  :parents (coercion coerce)
  :short "Convert a string to a character list."

  :long "<p>@(call explode) is logically nothing more than @('(coerce x
'list)').</p>

<p>Even though @(see coerce) is built into ACL2, we prefer to use @('explode') as
our normal form.  We rewrite all uses of @('(coerce x 'list)') into
@('(str::explode x)') with the following rule:</p>

@(def coerce-to-list-removal)

<p>The basic rationale for this is that @('coerce')'s extra @(''list') argument
means we can't write, e.g., congruence relations about @('(coerce x 'list)'),
whereas this is no problem for @('(explode x)').</p>

<p>We do the same thing for @('(coerce x 'string)') &mdash; see @(see
implode).</p>

<p><b>BOZO</b> consider using misc/fast-coerce here.</p>"
  :inline t
  (coerce x 'list)
  ///
  (in-theory (disable (:t explode)))
  (local (in-theory (enable explode)))

  (defthm true-listp-of-explode
    (true-listp (explode x))
    :rule-classes :type-prescription)

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
           (explode x))))

(theory-invariant (incompatible (:definition acl2::explode$inline)
                                (:rewrite coerce-to-list-removal)))



(define implode ((x character-listp))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (coercion coerce)
  :short "Convert a character list into a string."

  :long "<p>@(call implode) is logically nothing more than @('(coerce x
'string)').</p>

<p>Even though @(see coerce) is built into ACL2, we prefer to use @('implode')
as our normal form.  We rewrite all uses of @('(coerce x 'string)') into
@('(str::implode x)') with the following rule:</p>

@(def coerce-to-string-removal)

<p>The basic rationale for this is that @('coerce')'s extra @(''string')
argument means we can't write, e.g., congruence relations about @('(coerce x
'string)'), whereas this is no problem for @('(implode x)').</p>

<p>We do the same thing for @('(coerce x 'list)') &mdash; see @(see
explode).</p>"
  :inline t
  (coerce x 'string)
  ///
  (in-theory (disable (:t implode)))
  (local (in-theory (enable implode)))

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
           (implode x))))

(theory-invariant (incompatible (:definition acl2::implode$inline)
                                (:rewrite coerce-to-string-removal)))



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

