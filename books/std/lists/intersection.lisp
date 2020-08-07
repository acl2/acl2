; Intersection$ Lemmas
; Copyright (C) 2013 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "list-defuns")
(include-book "xdoc/top" :dir :system)
(local (include-book "sets"))

(local (in-theory (enable intersection$ intersectp)))

(defsection std/lists/intersection$
  :parents (std/lists intersection$)
  :short "Lemmas about @(see intersection$) available in the @(see std/lists)
library."

  "<p>We'll take @(see intersectp) as the desired normal form for asking
  whether intersections are empty.</p>"

  (defthm intersection$-under-iff
    (iff (intersection$ x y)
         (intersectp x y)))

  (defthm consp-of-intersection$
    (equal (consp (intersection$ x y))
           (intersectp x y)))

  "<p>Basic atom/cons rules.</p>"

  (defthm intersection$-when-atom-left
    (implies (atom x)
             (equal (intersection$ x y)
                    nil)))

  (defthm intersection$-of-cons-left
    (equal (intersection$ (cons a x) y)
           (if (member a y)
               (cons a (intersection$ x y))
             (intersection$ x y))))

  (defthm intersection$-when-atom-right
    (implies (atom y)
             (equal (intersection$ x y)
                    nil)))

  "<p>We don't have a very nice rule for @(see cons) on the right if we're
  trying to maintain @('equal'), because we don't know where in @('x') the
  element occurs.  However, if we're only maintaining @(see set-equiv), then we
  can just put the element on the front and we get a perfectly nice rule:</p>"

  (defthm intersection$-of-cons-right-under-set-equiv
    (set-equiv (intersection$ x (cons a y))
               (if (member a x)
                   (cons a (intersection$ x y))
                 (intersection$ x y)))
    :hints(("Goal" :in-theory (enable set-equiv))))


  "<h5>Basic set reasoning</h5>"

  (defthm member-of-intersection$
    (iff (member a (intersection$ x y))
         (and (member a x)
              (member a y)))
    :rule-classes
    (:rewrite
     (:type-prescription
      :corollary
      (implies (not (member a x))
               (not (member a (intersection$ x y)))))
     (:type-prescription
      :corollary
      (implies (not (member a y))
               (not (member a (intersection$ x y)))))))

  (defthm subsetp-equal-of-intersection$-1
    (subsetp-equal (intersection$ x y) x))

  (defthm subsetp-equal-of-intersection$-2
    (subsetp-equal (intersection$ x y) y))

  (defthm subsetp-intersection-equal
    (iff (subsetp a (intersection-equal b c))
         (and (subsetp a b)
              (subsetp a c))))


  (defthm intersection$-commutes-under-set-equiv
    (set-equiv (intersection$ x y)
               (intersection$ y x))
    :hints(("Goal" :in-theory (enable set-equiv))))

  ;; These are redundant with sets.lisp
  (defcong set-equiv equal (intersection-equal x y) 2)
  (defcong set-equiv set-equiv (intersection-equal x y) 1)



  "<h5>Length bound</h5>

  <p>Here is a nice bounding theorem.  Note that there is no analogous rule for
  @('-right'), because, e.g., X could have multiple copies of some member in Y,
  and if so we end up reproducing them.  Consider for instance:</p>

    @({ (intersection$ '(a a a) '(a)) ==> '(a a a) })"

  (defthm len-of-intersection$-upper-bound
    (<= (len (intersection$ x y))
        (len x))
    :rule-classes ((:rewrite) (:linear))))
