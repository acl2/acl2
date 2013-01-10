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
(include-book "strpos")
(local (include-book "arithmetic"))


(defsection substrp
  :parents (substrings)
  :short "Case-sensitive test for the existence of a substring."
  :long "<p>@(call substrp) determines if x ever occurs as a substring of y.
The test is case-sensitive.</p>

<p>See also @(see isubstrp) for a case-insensitive version, and @(see strpos)
or @(see strrpos) for alternatives that say where a match occurs.</p>"

  (definlined substrp (x y)
    (declare (type string x)
             (type string y))
    (if (strpos x y)
        t
      nil))

  (local (in-theory (enable substrp)))

  (defthm prefixp-when-substrp
    (implies (and (substrp x y)
                  (force (stringp x))
                  (force (stringp y)))
             (prefixp (coerce x 'list)
                      (nthcdr (strpos x y) (coerce y 'list)))))

  (defthm completeness-of-substrp
    (implies (and (prefixp (coerce x 'list)
                           (nthcdr m (coerce y 'list)))
                  (force (natp m))
                  (force (stringp x))
                  (force (stringp y)))
             (substrp x y))
    :hints(("Goal"
            :in-theory (disable completeness-of-strpos)
            :use ((:instance completeness-of-strpos))))))
