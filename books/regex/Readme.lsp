((:files
"
.:
Makefile
Readme.lsp
defset-encapsulates.lisp
defset-macros.lisp
equal-based-set.lisp
grep-command-line.lisp
input-list.lisp
make-acl2-grep.lsp
regex-chartrans.lisp
regex-defs.lisp
regex-exec.lisp
regex-fileio.lisp
regex-parse-brace.lisp
regex-parse-bracket.lisp
regex-parse.lisp
regex-tests.lisp
")
 (:TITLE "regex")
 (:AUTHOR/S
  "Sol Swords"
  )
 (:KEYWORDS
  "grep" "regex" "regular expression"
  )
 (:ABSTRACT "Contains a regular expression scanner implementation designed to
be similar to GNU Grep.  To run using a grep-like interface, include the book
grep-command-line and run the grep-exec function with command-line arguments
given as a list of strings.  Also see the file regex-tests.lisp to see how to
run regular expressions on strings in a more programmatic fashion.
")
 (:PERMISSION
  "
Copyright (C) 2008 by Sol Swords <sswords@cs.utexas.edu>.

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
