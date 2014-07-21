; Final-cdr function and lemmas
; Copyright (C) 2005-2013 Kookamara LLC
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
; final-cdr.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(local (include-book "nthcdr"))

(defsection final-cdr
  :parents (std/lists)
  :short "@(call final-cdr) returns the atom in the \"cdr-most branch\" of
@('x')."
  :long "<p>For example, @('(final-cdr '(a b c . d))') is @('d').</p>

<p>This function is related to @(see list-fix).  It is occasionally useful for
strengthening rewrite rules by removing hypotheses.</p>"

  (defund final-cdr (x)
    (declare (xargs :guard t))
    (if (atom x)
        x
      (final-cdr (cdr x))))

  (local (in-theory (enable final-cdr)))

  (defthm final-cdr-when-atom
    (implies (atom x)
             (equal (final-cdr x)
                    x)))

  (defthm final-cdr-of-cons
    (equal (final-cdr (cons a x))
           (final-cdr x)))

  (defthm final-cdr-when-true-listp
    (implies (true-listp x)
             (equal (final-cdr x)
                    nil)))

  (defthm equal-final-cdr-nil
    (equal (equal (final-cdr x) nil)
           (true-listp x)))

  (defthm equal-of-final-cdr-and-self
    (equal (equal x (final-cdr x))
           (atom x)))

  (defthm final-cdr-of-append
    (equal (final-cdr (append x y))
           (final-cdr y)))

  (defthm final-cdr-of-revappend
    (equal (final-cdr (revappend x y))
           (final-cdr y)))

  (defthm final-cdr-of-union-equal
    (equal (final-cdr (union-equal x y))
           (final-cdr y)))

  (defthm final-cdr-of-acons
    (equal (final-cdr (acons key val alist))
           (final-cdr alist)))

  (defthm final-cdr-of-hons-acons
    (equal (final-cdr (hons-acons key val alist))
           (final-cdr alist)))

  (defthm final-cdr-of-hons-shrink-alist
    (equal (final-cdr (hons-shrink-alist alist ans))
           (final-cdr ans)))

  (defthm final-cdr-of-add-to-set-equal
    (equal (final-cdr (add-to-set-equal a x))
           (final-cdr x)))

  (defthm final-cdr-of-last
    (equal (final-cdr (last x))
           (final-cdr x)))

  (defthm final-cdr-of-nthcdr
    (equal (final-cdr (nthcdr n x))
           (if (<= (nfix n) (len x))
               (final-cdr x)
             nil))))
