((:FILES "
.:
fix-cert.acl2
fix-cert.lisp
Makefile
moved
Readme.lsp
test1.acl2
test1b.acl2
test1bb.acl2
test1bb.lisp
test1b.lisp
test1bp.acl2
test1bp.lisp
test1.lisp
test1p.acl2
test1pb.acl2
test1pb.lisp
test1p.lisp
test1pp.acl2
test1pp.lisp
test2.acl2
test2.lisp
test-fix-cert0.acl2
test-fix-cert0.lisp
test-fix-cert1.acl2
test-fix-cert1.lisp
test-fix-cert2.acl2
test-fix-cert2.lisp
test-pkg1.lsp
test-pkg2.lsp

moved/:
README
test1bb.lisp
test1b.lisp
test1bp.lisp
test1.lisp
test1pb.lisp
test1p.lisp
test1pp.lisp
test2.lisp
"
)
 (:TITLE    "Fix-cert")
 (:AUTHOR/S "Peter C. Dillinger") ; With guidance & advice from Matt Kaufmann and Panagiotis Manolios
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "book contributions" "contributed books"
   "certification" "distribution" "path"
   )
 (:ABSTRACT
"After moving books from one place to another in a filesystem, use
this library to update the .cert files accordingly without costly
recertification.
")
 (:PERMISSION ; author/s permission for distribution and copying:
"Copyright (C) 2009 Peter C. Dillinger and Northeastern University

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301, USA."))

#|
This was developed as part of ACL2s: "The ACL2 Sedan."

fix-cert.lisp
    The book that offers the functionality for fixing .cert files.

The rest are just regression tests.

|#
