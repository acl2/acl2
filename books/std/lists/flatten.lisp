; Flatten function and lemmas
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
; flatten.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "equiv")

(defun binary-append-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic
       (append x y)
       :exec
       (if (consp x)
           (cons (car x)
                 (binary-append-without-guard (cdr x) y))
         y)))

(defmacro append-without-guard (x y &rest rst)
  (xxxjoin 'binary-append-without-guard (list* x y rst)))

(add-macro-alias append-without-guard binary-append-without-guard)

(defxdoc append-without-guard
  :parents (std/lists append)
  :short "Version of @(see append) that has a guard of @('t')"
  :long "See @(see std::strict-list-recognizers) for a discussion of whether
 requring lists to be @('nil')-terminated is right for you.")

(defsection flatten
  :parents (std/lists)
  :short "@(call flatten) appends together the elements of @('x')."
  :long "<p>Typically @('x') is a list of lists that you want to
merge together.  For example:</p>

@({
    (flatten '((a b c) (1 2 3) (x y z)))
      -->
    (a b c 1 2 3 x y z)
})

<p>This is a \"one-level\" flatten that does not necessarily produce
an @(see atom-listp).  For instance,</p>

@({
     (flatten '(((a . 1) (b . 2))
                ((x . 3) (y . 4)))
       -->
     ((a . 1) (b . 2) (x . 3) (y . 4))
})"

  (defund flatten (x)
    (declare (xargs :guard t))
    (if (consp x)
        (append-without-guard (car x)
                              (flatten (cdr x)))
      nil))

  (local (in-theory (enable flatten)))

  ;; The inferred type prescription isn't strong enough, it just says
  ;; (TS-UNION *TS-CONS* *TS-NIL*), so add a proper replacement.

  (in-theory (disable (:type-prescription flatten)))

  (defthm true-listp-of-flatten
    (true-listp (flatten x))
    :rule-classes :type-prescription)

  (defthm flatten-when-not-consp
    (implies (not (consp x))
             (equal (flatten x)
                    nil)))

  (defthm flatten-of-cons
    (equal (flatten (cons a x))
           (append a (flatten x))))

  (defthm flatten-of-list-fix
    (equal (flatten (list-fix x))
           (flatten x)))

  (defcong list-equiv equal (flatten x) 1
    :hints(("Goal"
            :in-theory (disable flatten-of-list-fix)
            :use ((:instance flatten-of-list-fix (x x))
                  (:instance flatten-of-list-fix (x x-equiv))))))

  (defthm flatten-of-append
    (equal (flatten (append x y))
           (append (flatten x)
                   (flatten y)))))
