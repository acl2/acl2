((:FILES
"
.:
Makefile
Readme.lsp
acl2-customization.lisp
books
database.acl2
database.lisp
elim-dest.acl2
elim-dest.lisp
foundations.acl2
foundations.lisp
induct.acl2
induct.lisp
output-module.acl2
output-module.lisp
paco.acl2
paco.lisp
prove.acl2
prove.lisp
rewrite.acl2
rewrite.lisp
simplify.acl2
simplify.lisp
type-set.acl2
type-set.lisp
utilities.acl2
utilities.lisp

books:
proveall.lsp
")
 (:TITLE    "Paco")
 (:AUTHOR/S 
  "J Moore"
  )
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "theorem prover"
   "pedagogical"
   )
 (:ABSTRACT "Paco is a cut-down, simplified ACL2-like theorem prover for
pedagogical use.

Type ``make'' to certify all books in this directory.  Then to run paco, connect
to subdirectory books/ and execute (ld \"proveall.lsp\" :ld-pre-eval-print t).

"
)
 (:PERMISSION
  "Paco
 Copyright (C) 2008 by:
 J Moore <moore@cs.utexas.edu>

This program is free software; you can redistribute it and/or 
modify it under the terms of the GNU General Public License as 
published by the Free Software Foundation; either version 2 of 
the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, 
but WITHOUT ANY WARRANTY; without even the implied warranty of 
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
GNU General Public License for more details.

You should have received a copy of the GNU General Public 
License along with this program; if not, write to the Free 
Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
Boston, MA 02110-1301, USA."))
