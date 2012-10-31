; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "cat")
(local (include-book "arithmetic"))

(defsection prefix-lines
  :parents (str)
  :short "Add a prefix to every line in a string."
  :long "<p>@(call prefix-lines) builds a new string by adding @('prefix') to
the start of every line in the string @('x').  The start of @('x') is regarded
as the start of a line, and also gets the prefix.  For instance,</p>

@({
 (prefix-lines \"hello world
 goodbye world\" \"  ** \")
})

<p>Would create the following result:</p>

@({
 \"  ** hello world
   ** goodbye world\"
})

<p>This is sometimes useful for indenting blobs of text when you are trying to
pretty-print things.  The operation is fairly efficient: we cons everything
into a character list and then coerce it back into a string at the end.</p>"

  (defund prefix-lines-aux (n x xl acc prefix)
    (declare (xargs :guard (and (natp n)
                                (stringp x)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x))
                                (stringp prefix))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (let ((n  (lnfix n))
          (xl (lnfix xl)))
      (if (mbe :logic (zp (- xl n))
               :exec (int= n xl))
          acc
        (let* ((char (char x n))
               (acc  (cons char acc))
               (acc  (if (eql char #\Newline)
                         (str::revappend-chars prefix acc)
                       acc)))
          (prefix-lines-aux (+ 1 n) x xl acc prefix)))))

  (defund prefix-lines (x prefix)
    (declare (xargs :guard (and (stringp x)
                                (stringp prefix))
                    :verify-guards nil))
    (let* ((acc    (str::revappend-chars prefix nil))
           (rchars (prefix-lines-aux 0 x (length x) acc prefix))
           (rstr   (coerce rchars 'string)))
      (reverse rstr)))

  (local (in-theory (enable prefix-lines-aux prefix-lines)))

  (defthm character-listp-of-prefix-lines-aux
    (implies (and (natp n)
                  (stringp x)
                  (natp xl)
                  (<= n xl)
                  (= xl (length x))
                  (stringp rprefix)
                  (character-listp acc))
             (character-listp (prefix-lines-aux n x xl acc prefix)))
    :hints(("Goal" :induct (prefix-lines-aux n x xl acc prefix))))

  (verify-guards prefix-lines)

  (defthm stringp-of-prefix-lines
    (stringp (prefix-lines x prefix))
    :rule-classes :type-prescription))



