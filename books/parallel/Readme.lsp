((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
fibonacci.lisp
futures-st.lisp
futures-st-raw.lsp
matrix-multiplication-parallel.lisp
matrix-multiplication-serial.lisp
matrix-multiplication-setup.lisp
spec-mv-let.lisp
syntax-tests.lisp
stress-tests.lisp")
 (:TITLE    "Simple examples and tests of parallelism primitives")
 (:AUTHOR/S "David Rager")
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "parallelism" "parallel" "pand" "por" "plet" "pargs" "performance" "futures"
   "spec-mv-let")
 (:ABSTRACT "Generally speaking, these files illustrate and check the use of
parallelism primitives.

futures-st.lisp serves as a wrapper for the raw Lisp file for a single-threaded
futures library.  It isn't much use except as a model for the multi-threaded
futures library, which should be installed into the books library before the
next ACL2 release.

futures-st-raw.lsp defines the implementation for the single-threaded futures
library.  Include futures-st.lisp to use this library.
")
  (:PERMISSION ; author/s permission for distribution and copying:
"parallel
Copyright (C) 2008 University of Texas at Austin
for files not explicitly copyrighted otherwise

{futures-st}.lisp and {futures-st-raw}.lsp copyright (C) 2010 by David L. Rager
<ragerdl@cs.utexas.edu>.

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
