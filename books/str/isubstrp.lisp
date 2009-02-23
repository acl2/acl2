; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
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

(in-package "STR")
(include-book "istrpos")

(defund isubstrp (x y)

  ":Doc-Section Str
  Case-insensitively test for the existence of a substring~/

  ~c[(isubstrp x y)] determines if x ever occurs as a case-insensitive substring of y.~/

  ~l[substrp], and ~pl[istrpos]"
  
  (declare (type string x)
           (type string y))

  (if (istrpos x y)
      t
    nil))

(defthm iprefixp-when-isubstrp
  (implies (and (isubstrp x y)
                (force (stringp x))
                (force (stringp y)))
           (iprefixp (coerce x 'list)
                     (nthcdr (istrpos x y) (coerce y 'list))))
  :hints(("Goal" :in-theory (enable isubstrp))))

(defthm completeness-of-isubstrp
  (implies (and (iprefixp (coerce x 'list)
                          (nthcdr m (coerce y 'list)))
                (force (natp m))
                (force (stringp x))
                (force (stringp y)))
           (isubstrp x y))
  :hints(("Goal"
          :in-theory (e/d (isubstrp)
                          (completeness-of-istrpos))
          :use ((:instance completeness-of-istrpos)))))
