; The Makefile has modified the default value of INHIBIT from Makefile-generic
; in order that we see warnings in the .out files.  We should see
; Double-rewrite warnings there that correspond exactly to comments about
; Double-rewrite (notice the upper-case D) in the .lisp files.

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
austel.lisp
greve1.lisp
greve2.lisp
greve3.lisp
mini-proveall-plus.lisp
mini-proveall.lisp
rhs1-iff.acl2
rhs1-iff.lisp
rhs1.acl2
rhs1.lisp
rhs2.acl2
rhs2.lisp
smith1.lisp
sumners1.lisp
warnings.acl2
warnings.lisp
")
 (:TITLE    "Double Rewriting for Equivalential Reasoning in ACL2")
 (:AUTHOR/S "Matt Kaufmann and J Moore") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "rewriting" "congruences" "equivalence relations" "double-rewrite")
 (:ABSTRACT "
This directory contains supporting materials to illustrate double-rewrite.  An
abstract of the corresponding ACL2 workshop submission is as follows:

Several users have had problems using equivalence-based rewriting in ACL2
because the ACL2 rewriter caches its results.  We describe this problem in some
detail, together with a solution implemented in ACL2 Version 2.9.4.  The
solution consists of a new primitive, double-rewrite}, together with
a new warning to suggest possible use of this primitive.")
  (:PERMISSION ; author/s permission for distribution and copying:
"Double-rewrite supporting materials
Copyright (C) 2006 Matt Kaufmann and J Moore

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
