; Flatten function and lemmas
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

  (defthm flattenp-of-append
    (equal (flatten (append x y))
           (append (flatten x)
                   (flatten y)))))
