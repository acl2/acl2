; List-fix function and lemmas
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
; list-fix.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(local (include-book "arithmetic/top" :dir :system))

(defsection list-fix
  :parents (std/lists)
  :short "@(call list-fix) converts @('x') into a @(see true-listp) by, if
necessary, changing its @(see final-cdr) to @('nil')."

  :long "<p>Many functions that processes lists follows the <b>list-fix
convention</b>: whenever @('f') is given a some non-@('true-listp') @('a')
where it expected a list, it will act as though it had been given @('(list-fix
a)') instead.  As a few examples, logically,</p>

<ul>
<li>@('(endp x)') ignores the final @('cdr') of @('x'),</li>
<li>@('(len x)') ignores the final @('cdr') of @('x'),</li>
<li>@('(append x y)') ignores the final @('cdr') of @('x') (but not @('y'))</li>
<li>@('(member a x)') ignores the final @('cdr') of @('x'), etc.</li>
</ul>

<p>Having a @('list-fix') function is often useful when writing theorems about
how list-processing functions behave.  For example, it allows us to write
strong, hypothesis-free theorems such as:</p>

@({
    (equal (character-listp (append x y))
           (and (character-listp (list-fix x))
                (character-listp y)))
})

<p>Indeed, @('list-fix') is the basis for @(see list-equiv), an extremely
common @(see equivalence) relation.</p>"

  (defund list-fix (x)
    (declare (xargs :guard t))
    (if (consp x)
        (cons (car x)
              (list-fix (cdr x)))
      nil))

  (defthm list-fix-when-not-consp
    (implies (not (consp x))
             (equal (list-fix x)
                    nil))
    :hints(("Goal" :in-theory (enable list-fix))))

  (defthm list-fix-of-cons
    (equal (list-fix (cons a x))
           (cons a (list-fix x)))
    :hints(("Goal" :in-theory (enable list-fix))))

  (defthm car-of-list-fix
    (equal (car (list-fix x))
           (car x)))

  (defthm cdr-of-list-fix
    (equal (cdr (list-fix x))
           (list-fix (cdr x))))

  (defthm list-fix-when-len-zero
    (implies (equal (len x) 0)
             (equal (list-fix x)
                    nil)))

  (defthm true-listp-of-list-fix
    (true-listp (list-fix x)))

  (defthm len-of-list-fix
    (equal (len (list-fix x))
           (len x)))

  (defthm list-fix-when-true-listp
    (implies (true-listp x)
             (equal (list-fix x) x)))

  (defthm list-fix-under-iff
    (iff (list-fix x)
         (consp x))
    :hints(("Goal" :induct (len x))))

  (defthm consp-of-list-fix
    (equal (consp (list-fix x))
           (consp x))
    :hints(("Goal" :induct (len x))))

  (defthm last-of-list-fix
    (equal (last (list-fix x))
           (list-fix (last x))))

  (defthm equal-of-list-fix-and-self
    (equal (equal x (list-fix x))
           (true-listp x))))
