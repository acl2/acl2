; A simple example of a book directory
; Copyright (C) 2006  University of Texas at Austin

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
  "
.:
Makefile
Readme.lsp
bash.lisp
exdefs.lisp
gen.lisp
lemgen.lisp
refute.lisp
")
  (:TITLE    "Backtracking Prover")
   (:AUTHOR/S "J. Erickson") ; non-empty list of author strings
    (:KEYWORDS ; non-empty list of keywords, case-insensitive
        "book contributions" "contributed books" "induction" "generalization" "backtracking")
     (:ABSTRACT "Book for paper ``Backtracking and Induction in ACL2'', ACL2 Workshop 2007")
       (:PERMISSION ; author/s permission for distribution and copying:
	"Copyright (C) 2007 John Erickson

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

