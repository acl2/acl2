; Reverse lemmas
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
; reverse.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(local (include-book "revappend"))
(local (include-book "coerce"))

(defsection std/lists/reverse
  :parents (std/lists reverse)
  :short "Lemmas about @(see reverse) available in the @(see std/lists)
library."

  :long "<p>The built-in @(see reverse) function is overly complex because it
can operate on either lists or strings.  To reverse a list, it is generally
preferable to use @(see rev), which has a very simple definition.</p>

<p>We ordinarily expect @('reverse') to be enabled, in which case it
expands (in the list case) to @('(revappend x nil)'), which we generally expect
to be rewritten to @('(rev x)') due to the @('revappend-removal') theorem.</p>

<p>Because of this, we do not expect these lemmas to be very useful unless, for
some reason, you have disabled @('reverse') itself.</p>"

  (defthm stringp-of-reverse
    (equal (stringp (reverse x))
           (stringp x)))

  (defthm true-listp-of-reverse
    (equal (true-listp (reverse x))
           (not (stringp x))))

  (defthm equal-of-reverses-when-strings
    (implies (and (stringp x)
                  (stringp y))
             (equal (equal (reverse x) (reverse y))
                    (equal x y))))

  (defthm equal-of-reverses-when-lists
    (implies (and (true-listp x)
                  (true-listp y))
             (equal (equal (reverse x) (reverse y))
                    (equal x y)))))

