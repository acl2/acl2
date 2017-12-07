
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
"
Copyright (C) 2006, Regents of the University of Texas
Written by Erik Reeber
License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
"))
