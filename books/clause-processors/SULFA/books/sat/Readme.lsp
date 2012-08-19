
; A simple example of a book directory
; Copyright (C) 2006  University of Texas at Austin

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
local-clause-simp.lisp
check-output.lisp
convert-to-cnf.lisp
sat-setup.lisp
sat-package.acl2

")
 (:TITLE    "A SAT-Based Decision Procedure for SULFA")
 (:AUTHOR/S "Erik Reeber") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "SAT" "sat" "decision procedure" "SULFA")
 (:ABSTRACT "
This directory contains a book that uses external SAT solvers to
verify properties in the Subclass of Unrollable List Formulas
(SULFA).") 
  (:PERMISSION ; author/s permission for distribution and copying:
"Simple example 1
Copyright (C) 2006 Joe User and Aunt Acid

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
