((:FILES "
.:
acl2-customization.lsp
Makefile
mv-proof.lisp
num-list-fns.lisp
num-list-thms.lisp
package.lsp
portcullis.lisp
random-state-basis1.lisp
random-state.lisp
Readme.lsp
rem-and-floor.lisp
splitnat.lisp
switchnat.lisp
defdata-regression.lsp
defdata-util.lisp
register-data-constructor
register-type
register-combinator
listof
alistof
record
map
enumerators-gen
tau-characterization
builtin-combinators
defdata-core.lisp
library-support.lisp
base.lisp
sig.lisp
top.lisp
"
)
 (:TITLE    "Data Definition Framework")
 (:AUTHOR/S "Harsh Raju Chamarthi, Peter C. Dillinger") ; With help from Matt Kaufmann and Panagiotis Manolios
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
  "types" "data definitions" "polymorphism"
  "enumerators" "predicates" "tau-system"
  )
 (:ABSTRACT
"
USAGE:
 (include-book \"defdata/top\" :dir :system :ttags :all)

There is some system-level documentation in defdata-core.lisp
")
 (:PERMISSION ; author/s permission for distribution and copying:
"Copyright (C) 2011 Harsh Raju Chamarthi, Peter C. Dillinger
                    and Northeastern University

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

   


These books were developed as part of ACL2s: "The ACL2 Sedan."

To certify books, do the foll at the shell prompt (in the current directory):
$ export ACL2=<path to your  saved_acl2>
$ make

Note: You need java to be installed on your machine and in PATH.
      acl2-lib.jar automatically generates .acl2 files.

Books:

top.lisp 
   top-level entry book which brings everything together


base.lisp
   Builds up the type metadata and type relationship data structures for base
   ACL2 theory


mv-proof.lisp
rem-and-floor.lisp
num-list-fns.lisp
num-list-thms.lisp
   Support books for enumerators-gen

splitnat.lisp
   Given a natural number seed s and another number n, it provides the
   function split-nat returns an n-tuple which is bijective to s.
   It is used to generate enumerators for product types.

switchnat.lisp
   Given a natural number seed s and another number n, it provides the
   function switch-nat returns an pair (c,s') which is bijective to s.
   This is used to generate enumerators for union types.

defdata-core.lisp 
   The previous books implement the data definition framework.
   In particular, it provides the defdata macro which the user can use
   to introduce 

library-support.lisp
   Some theorems for using misc/records book in our context.


random-state-basis1.lisp
   See below
random-state.lisp
   Provides pseudogeometric natural number distribution.

defdata-regression.lsp
   Examples, testcases 

defdata-util.lisp
   Some utility functions used across the books in this directory.


|#
