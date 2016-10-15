; Standard Utilities Library
; Copyright (C) 2008-2016 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "STD")
(include-book "xdoc/top" :dir :system)

(defsection prod-consp
  :parents (prod-cons)
  :short "Special recognizer for conses, except that to save space we require
          that (nil . nil) be represented just as nil."

  (defund prod-consp (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (or (car x) (cdr x))
             t)
      (not x)))

  (local (in-theory (enable prod-consp)))

  (defthm booleanp-of-prod-consp
    (booleanp (prod-consp x))
    :rule-classes :type-prescription)

  (defthm prod-consp-compound-recognizer
    (implies (prod-consp x)
             (or (consp x) (not x)))
    :rule-classes :compound-recognizer))


(defsection prod-cons
  :parents (defaggregate)
  :short "Special constructor for products that collapses (nil . nil) into nil."

  (defund-inline prod-cons (x y)
    (declare (xargs :guard t))
    (and (or x y)
         (cons x y)))

  (local (in-theory (enable prod-cons)))

  (defthm prod-consp-of-prod-cons
    (prod-consp (prod-cons x y))
    :rule-classes (:rewrite :type-prescription)
    :hints(("Goal" :in-theory (enable prod-consp))))

  (defthm car-of-prod-cons
    (equal (car (prod-cons x y)) x))

  (defthm cdr-of-prod-cons
    (equal (cdr (prod-cons x y)) y))

  (defthm prod-cons-of-car/cdr
    (implies (prod-consp x)
             (equal (prod-cons (car x) (cdr x))
                    x))
    :hints(("Goal" :in-theory (enable prod-consp))))

  (defthmd equal-of-prod-cons
    (implies (prod-consp x)
             (equal (equal x (prod-cons a b))
                    (and (equal (car x) a)
                         (equal (cdr x) b))))
    :hints(("Goal" :in-theory (enable prod-consp))))

  (defthm acl2-count-of-prod-cons
    (and (>= (acl2-count (prod-cons x y))
             (acl2-count x))
         (>= (acl2-count (prod-cons x y))
             (acl2-count y)))
    :rule-classes :linear)

  (defthm prod-cons-equal-cons
    (implies (or a b)
             (equal (equal (prod-cons a b) (cons c d))
                    (and (equal a c)
                         (equal b d))))
    :hints(("Goal" :in-theory (enable prod-cons))))

  (defthm prod-cons-when-either
    (implies (or a b)
             (and (prod-cons a b)
                  (consp (prod-cons a b))))
    :rule-classes ((:rewrite)
                   (:type-prescription :corollary
                    (implies (or a b)
                             (consp (prod-cons a b)))))
    :hints(("Goal" :in-theory (enable prod-cons))))

  (defthm prod-cons-not-consp-forward
    (implies (not (consp (prod-cons a b)))
             (and (not a) (not b)))
    :hints(("Goal" :in-theory (enable prod-cons)))
    :rule-classes ((:forward-chaining :trigger-terms ((prod-cons a b))))))


(defsection prod-cons-with-hint
  :parents (prod-cons)
  :short "Same as @(see prod-cons), but avoids reconsing like @(see cons-with-hint)."
  :long "<p>We leave this enabled and expect to reason about @(see prod-cons) instead.</p>"

  (defun-inline prod-cons-with-hint (x y hint)
    (declare (xargs :guard t))
    (mbe :logic (prod-cons x y)
         :exec  (and (or x y)
                     (cons-with-hint x y hint)))))


(defsection prod-car
  :parents (prod-cons)
  :short "Same as @(see car), but guarded with @(see prod-consp)."
  :long "<p>We leave this enabled and expect to reason about @(see car) instead.</p>"

  (defun-inline prod-car (x)
    (declare (xargs :guard (prod-consp x)))
    (car x)))


(defsection prod-cdr
  :parents (prod-cons)
  :short "Same as @(see cdr), but guarded with @(see prod-consp)."
  :long "<p>We leave this enabled and expect to reason about @(see car) instead.</p>"

  (defun-inline prod-cdr (x)
    (declare (xargs :guard (prod-consp x)))
    (cdr x)))


(defsection prod-hons
  :parents (prod-cons)
  :short "Same as @(see prod-cons) but uses @(see hons)."
  :long "<p>We leave this enabled and expect to reason about @(see prod-cons) instead.</p>"

  (local (in-theory (enable prod-cons)))

  (defun-inline prod-hons (x y)
    (declare (xargs :guard t))
    (mbe :logic (prod-cons x y)
         :exec (and (or x y)
                    (hons x y)))))
