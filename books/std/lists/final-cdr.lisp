; Final-cdr function and lemmas
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
