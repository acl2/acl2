; Two Naturals Measure
; Copyright (C) 2005-2006 Kookamara LLC
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
;
; two-nats-measure.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

;; We could just include an arithmetic book, but this plus cancellation rule is
;; really all we need, so let's avoid the dependency.

(local (defthm equal-of-booleans-rewrite
         (implies (and (booleanp x) (booleanp y))
                  (iff (equal x y)
                       (iff x y)))))

(local (defthm plus-cancel-left
         (equal (< (+ x y) (+ x z))
                (< (fix y) (fix z)))))

(defsection two-nats-measure
  :parents (std/basic ordinals acl2-count)
  :short "An ordinal measure for admitting functions: lexicographic ordering of
  two natural numbers."

  :long "<p>@(call two-nats-measure) constructs an ordinal that can be used
  to prove that recursive functions terminate.  It essentially provides a
  lexicographic order where @('a') is more significant than @('b').  More
  precisely, its correctness is understood through the theorem:</p>

  @(thm o<-of-two-nats-measure)

  <p>This is often useful for admitting mutually recursive functions where
  one function inspects its argument and then immediately calls another.
  For instance, suppose you want to admit:</p>

  @({
      (mutual-recursion
        (defun f (x) ...)
        (defun g (x) (if (special-p x) (f x) ...)))
  })

  <p>Then since @('g') calls @('f') on the same argument, you can't just use
  @(see acl2-count), or for that matter any other measure that only considers
  the argument @('x')) to show that the call of @('(f x)') has made progress.
  However, it's easy to use @('two-nats-measure') to ``rank'' the functions
  so that @('f') is always considered smaller than @('g'):</p>

  @({
      (mutual-recursion

        (defun f (x)
          (declare (xargs :measure (two-nats-measure (acl2-count x) 0)))
          ...)

        (defun g (x)
          (declare (xargs :measure (two-nats-measure (acl2-count x) 1)))
          ...))
  })

  <p>More generally @('two-nats-measure') may be useful whenever you want to
  admit an algorithm that makes different kinds of progress.</p>

  <p>Example.  Suppose you have a pile of red socks and a pile of blue socks to
  put away.  Every time you put away a red sock, I add a bunch of blue socks to
  your pile, but when you put a blue sock away, I don't get to add any more
  socks.  You will eventually finish since the pile never gets any new red
  socks.  You can admit a function like this with @('(two-nats-measure num-red
  num-blue)').</p>

  <p>See also @(see nat-list-measure) for a generalization of this to a
  lexicographic ordering of a list of natural numbers (of any length instead of
  just two numbers).</p>"

  (defund two-nats-measure (a b)
    (declare (xargs :guard (and (natp a)
                                (natp b))))
    (make-ord 2
              (+ 1 (nfix a))
              (make-ord 1 (+ 1 (nfix b)) 0)))

  (in-theory (disable (:executable-counterpart two-nats-measure)))

  (defthm o-p-of-two-nats-measure
    (equal (o-p (two-nats-measure a b))
           t)
    :hints(("Goal" :in-theory (enable two-nats-measure))))

  (defthm o<-of-two-nats-measure
    (equal (o< (two-nats-measure a b)
               (two-nats-measure c d))
           (or (< (nfix a) (nfix c))
               (and (equal (nfix a) (nfix c))
                    (< (nfix b) (nfix d)))))
    :hints(("Goal" :in-theory (enable two-nats-measure)))))


(defsection nat-list-measure
  :parents (std/basic ordinals acl2-count)
  :short "An ordinal measure for admitting functions: lexicographic ordering of
  a list of natural numbers."

  :long "<p>@(call nat-list-measure) constructs an ordinal that can be used to
  prove that recursive functions terminate.  It essentially provides a
  lexicographic order of a list of naturals.  That is,</p>

  @({
        (o< (nat-list-measure (list a1 b1 c1))
            (nat-list-measure (list a2 b2 c2)))
  })

  <p>Will be true when either:</p>

  <ul>
  <li>@('a1 < a2'), or else</li>
  <li>@('a1 == a2') and @('b1 < b2'), or else</li>
  <li>@('a1 == a2') and @('b1 == b2') and @('c1 < c2').</li>
  </ul>

  <p>Typical usage is, e.g.,:</p>

  @({
       (defun f (a b c)
         (declare (xargs :measure (nat-list-measure (list a b c))))
         ...)
  })

  <p>See also the simpler (but more limited) @(see two-nats-measure) for some
  additional discussion on how such a measure might be useful.</p>

  <p>See also @(see nat-list-<) for a somewhat fancier alternative.</p>"

  (defund nat-list-measure (a)
    (declare (xargs :guard t
                    :verify-guards nil))
    (if (atom a)
        (nfix a)
      (make-ord (len a) (+ 1 (nfix (car a)))
                (nat-list-measure (cdr a)))))

  (in-theory (disable (:executable-counterpart nat-list-measure)))

  (defthm consp-nat-list-measure
    (equal (consp (nat-list-measure a))
           (consp a))
    :hints(("Goal" :in-theory (enable nat-list-measure))))

  (defthm atom-caar-nat-list-measure
    (equal (caar (nat-list-measure a))
           (and (consp a)
                (len a)))
    :hints(("Goal" :in-theory (enable nat-list-measure))))

  (defthm o-p-of-nat-list-measure
    (o-p (nat-list-measure a))
    :hints(("Goal" :in-theory (enable o-p nat-list-measure))))

  (defun cons-list-or-quotep (x)
    (if (atom x)
        (equal x nil)
      (case (car x)
        (quote t)
        (cons (and (eql (len x) 3)
                   (cons-list-or-quotep (third x)))))))

  (defthm o<-of-nat-list-measure
    (implies (syntaxp (and (cons-list-or-quotep a)
                           (cons-list-or-quotep b)))
             (equal (o< (nat-list-measure a)
                        (nat-list-measure b))
                    (or (< (len a) (len b))
                        (and (equal (len a) (len b))
                             (if (consp a)
                                 (or (< (nfix (car a)) (nfix (car b)))
                                     (and (equal (nfix (car a)) (nfix (car b)))
                                          (o< (nat-list-measure (cdr a))
                                              (nat-list-measure (cdr b)))))
                               (< (nfix a) (nfix b)))))))
    :hints(("Goal" :in-theory (enable nat-list-measure)))))


(defsection nat-list-<
  :parents (nat-list-measure well-founded-relation-rule)
  :short "An alternate well-founded-relation that allows lists of naturals to
  be used directly as measures."

  :long "<p>This is essentially syntactic sugar for @(see nat-list-measure).
  We introduce @('nat-list-<') as a @(see well-founded-relation-rule), so that
  instead of writing:</p>

  @({
      (defun f (a b c)
        (declare (xargs :measure (nat-list-measure (list a b c))))
        ...)
  })

  <p>You can instead write:</p>

  @({
      (defun f (a b c)
        (declare (xargs :measure (list a b c)
                        :well-founded-relation nat-list-<))
        ...)
  })

  <p>That's more verbose in this example, but in practice it can often end
  up being more concise.  In particular:</p>

  <ul>

  <li>You can use @(see set-well-founded-relation) to install @('nat-list-<')
  as your well-founded relation ahead of time.</li>

  <li>In a big @(see mutual-recursion), you only need to give the
  @(':well-founded-relation') to a single definition.</li>

  </ul>"

  (defund nat-list-< (a b)
    (o< (nat-list-measure a) (nat-list-measure b)))

  (local (in-theory (enable nat-list-<)))

  (defthm nat-list-wfr
    (and (o-p (nat-list-measure x))
         (implies (nat-list-< x y)
                  (o< (nat-list-measure x)
                      (nat-list-measure y))))
    :rule-classes :well-founded-relation)


  (defthm open-nat-list-<
    (implies (syntaxp (and (cons-list-or-quotep a)
                           (cons-list-or-quotep b)))
             (equal (nat-list-< a b)
                    (or (< (len a) (len b))
                        (and (equal (len a) (len b))
                             (if (consp a)
                                 (or (< (nfix (car a)) (nfix (car b)))
                                     (and (equal (nfix (car a)) (nfix (car b)))
                                          (nat-list-< (cdr a) (cdr b))))
                               (< (nfix a) (nfix b)))))))
    :hints (("Goal"
             :use o<-of-nat-list-measure
             :in-theory (disable o<-of-nat-list-measure))))

  (defthm natp-nat-list-<
    (implies (and (atom a) (atom b))
             (equal (nat-list-< a b)
                    (< (nfix a) (nfix b))))
    :hints (("Goal"
             :use o<-of-nat-list-measure
             :in-theory (disable o<-of-nat-list-measure)))))
