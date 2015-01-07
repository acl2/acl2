((:FILES "
.:
acl2-customization.lsp
package.lsp
portcullis.lisp
Makefile
Readme.lsp
basis.lisp
utilities.lisp
acl2s-parameter.lisp
with-timeout.lisp
with-timeout-raw.lsp
cert.acl2
certify-book.sh
type.lisp
cgen-search.lisp
build-enumcalls.lisp
elim.lisp
callback.lisp
prove-cgen.lisp
top.lisp
testing-regression.lsp
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

USAGE:
 (include-book \"cgen/top\" :dir :system :ttags :all)
 (acl2s-defaults :set testing-enabled t) ; default is :naive


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

EXAMPLES: See testing-regression.lsp

USAGE:
 (include-book "cgen/top" :dir :system :ttags :all)
 (acl2s-defaults :set testing-enabled t) ; default is :naive
   


These books were developed as part of ACL2s: "The ACL2 Sedan."

To certify books, at the shell prompt (in the current directory) do:
$ export ACL2=<path to your saved_acl2>
$ ../build/cert.pl top.lisp


Books:


acl2s-parameter.lisp
   All ACL2s testing/counterexample-generation related configuration parameters
   are set here. It provides a macro to add a new parameter, producing
   getters setters and doc items.


basis.lisp
   defines macros for defining functions that ease guard verification
   (type-checking), and provide facilities for writing concise code. Note that
   this book is in progress and some features I would like to
   incorporate in the future are yet unimplemented. 

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

cgen-search.lisp
   Main driver loop for cgen/testing.

callback.lisp
   Hook to call cgen/testing/search on checkpoint goals.
   Implemented using override-hints + backtrack hints.


build-enumcalls.lisp
   Code generation for calling enumerators for the current type alist.

cgen-prove.lisp
   Main cgen api function which calls prove with the appropriate cgen context/state.

top.lisp 
   top-level entry book which provides test? macro and some initialization and customizations.

|#
