; A simple example of a book directory
; Copyright (C) 2006  University of Texas at Austin

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
acl2.lisp
bdd.lisp
sat.lisp
")
 (:TITLE    "SAT-based Procedure for Finite State Machine---Examples")
 (:AUTHOR/S "Erik Reeber" "Warren A. Hunt, Jr.") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "acl2 workshop" "supporting materials" "SAT")
 (:ABSTRACT "
This paper contains a few examples that were mentioned
in our ACL2 workshop paper, including the associativity
of a ripple carry adder, that shifting by a large value
produces all zeros, that shifting is cumulative, and 
that a decimal counter maintains a decimal invariant.  In
acl2.lisp a couple of these examples are proven by Brute
force using the ACL2 simplifier---i.e. recursive calls are
unrolled and ifs are turned into case splits.  In bdd.lisp
these exampes are proven with the BDD system.  In sat.lisp
the models are given and the calls to the SAT system are
shown in block comments.  Since standard ACL2 doesn't include
our SAT extension we cannot include these events directly.")
  (:PERMISSION ; author/s permission for distribution and copying:
"Submission test
Copyright (C) 2006 Matt Kaufmann

This program is free software; you can redistribute it and/or modify
it under the terms of Version 2 of the GNU General Public License as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301, USA."))
