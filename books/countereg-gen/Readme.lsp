((:FILES "
.:
acl2s-lib.jar
acl2s-parameter.lisp
base.lisp
basis.lisp
certify-book.sh
data.lisp
graph.lisp
library-support.lisp
main.lisp
Makefile
mv-proof.lisp
num-list-fns.lisp
num-list-thms.lisp
pkg.lsp
random.lisp
random-state-basis1.lisp
random-state.lisp
Readme.lsp
rem-and-floor.lisp
scratchpad.lsp
simple-graph-array.lisp
splitnat.lisp
switchnat.lisp
testing-regression.lsp
top.lisp
type.lisp
unversioned-files-extra.txt
utilities.lisp
with-timeout.lisp
with-timeout-raw.lsp
"
)
 (:TITLE    "Counterexample Generation")
 (:AUTHOR/S "Harsh Raju Chamarthi, Peter C. Dillinger") ; With help from Matt Kaufmann and Panagiotis Manolios
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "book contributions" "contributed books"
   "testing" "counterexamples" "witnesses" "executable"
   "models" "random testing" "bounded-exhaustive testing"
   "theorem-proving" "dpll" "backtracking search"
   )
 (:ABSTRACT
"We provide support for counterexample generation and provide a
defdata framework which forms the basis for using 'testing' to find
counterexamples. 

We use simple and incremental search strategies in our quest to find
counterexamples.

At a high-level, the idea of 'simple search' is simple: Given any
conjecture, infer type information about free variables from the
hypotheses, generate/sample values of these types (value sampling can
be random, bounded exhaustive or mixed), instantiate all variables and
evaluate to get either T or NIL. The value assignment resulting in NIL
is a counterexample (other cases are witness and vacuous). The type
information is stored in ACL2 tables and is usually created using
'defdata' which automatically generates the value enumerator for that
type. All base types have been lifted to the defdata framework i.e we
manually defined all enumerators and subtype relationships among the
ground ACL2 types.

Theorem proving and domain-specific libraries often help in
substantially shrinking the space of free variables that we need to
search, improving our chances of finding a counterexample if one
exists. We do this by using override and backtrack hints to search for
counterexamples to all checkpoints of a conjecture under
thm/defthm/test?.

'incremental search' is a DPLL like algorithm that selects an
appropriate variable, assigns it, propagates this information using
ACL2 itself to obtain a partially concretized formula, which is then
tested using 'simple search'. If we ever hit the stopping
condition (usually 3 counterexamples and witnesses), we abort the
search. If not, we continue with the select, assign, propagate
loop. Of course if propagating a value assignment results in a
contradiction in the hypotheses (i.e inconsistency), we backtrack.

Instructions for usage are in top.lisp.

See the essay in main.lisp for high-level pseudocode of the test driver.
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
   top-level entry book with some customizations.

acl2s-parameter.lisp
   All ACL2s testing/counterexample-generation related configuration parameters
   are set here. It provides a macro to add a new parameter, producing
   getters setters and doc items.

base.lisp
   Builds up the type metadata and type relationship data structures for base
   ACL2 theory

basis.lisp
   defines macros for defining functions that ease guard verification
   (type-checking), and provide facilities for writing concise code. Note that
   this book is in progress and some features I would like to
   incorporate in the future are yet unimplemented. 

mv-proof.lisp
rem-and-floor.lisp
num-list-fns.lisp
num-list-thms.lisp
   Support books for defdata

splitnat.lisp
   Given a natural number seed s and another number n, it provides the
   function split-nat returns an n-tuple which is bijective to s.
   It is used to generate enumerators for product types.

switchnat.lisp
   Given a natural number seed s and another number n, it provides the
   function switch-nat returns an pair (c,s') which is bijective to s.
   This is used to generate enumerators for union types.

data.lisp 
   The previous books implement the data definition framework.
   In particular, it provides the defdata macro which the user can use
   to introduce 

graph.lisp
   Provides graph utility functions for DFS, SCC and transitive
   closure. Possibly buggy, will be replaces by simple-graph-array book.
 
library-support.lisp
   Some theorems for using misc/records book in our context.

main.lisp
   The top-level book which implements the main driver functions that
   orchestrate the testing+theorem-proving synergistic combination.
   It provides the test? macro and the test-checkpoint function which
   is used as an override-hint to search for counterexamples at all
   checkpoints. For more information on implementation look at the
   essay headed "Main Idea".

random-state-basis1.lisp
   See below
random-state.lisp
   Provides pseudogeometric natural number distribution.

testing-regression.lsp
   Examples, testcases and in general a book that you can refer to for
   quick application of counterexample generation.

simple-graph-array.lisp
   Simple implementation of DFS and SCC (and topological sort)

type.lisp 
   Provides functions to convert ACL2 type set into defdata types and
   also the meet operation over the subtype (lattice) defdata graph

utilities.lisp
   Some utility functions used across the books in this directory.

with-timeout.lisp
   Nested timeouts.


|#
