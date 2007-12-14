((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
LICENSE
Makefile
README
Readme.lsp
books
c-files
doc
scripts
smt-examples

./books:
Makefile
bv-smt-solver
clause-processors
sat
sat-tests

./books/bv-smt-solver:
Makefile
bv-lib-definitions.acl2
bv-lib-definitions.lisp
bv-lib-lemmas.acl2
bv-lib-lemmas.lisp
bv-lib.acl2
bv-lib.lisp
redundancy-removal.acl2
redundancy-removal.lisp
smt.acl2
smt.lisp
translation.acl2
translation.lisp

./books/clause-processors:
Makefile
sat-clause-processor.acl2
sat-clause-processor.lisp
sym-str.lisp

./books/sat:
Makefile
Readme.lsp
cert.acl2
check-output.lisp
convert-to-cnf.lisp
local-clause-simp.lisp
neq-implication.lisp
recognizer.lisp
sat-package.acl2
sat-setup.lisp
sat.acl2
sat.lisp
sexpr-sat-solver-const.lisp
sulfa-dir-const.acl2
sulfa-dir-const.lisp.isf
user-entry-data-structure.lisp

./books/sat-tests:
Makefile
benchmark.acl2
benchmark.lisp
sudoku.acl2
sudoku.lisp
test-help.acl2
test-help.lisp
test-incremental.acl2
test-incremental.lisp
tutorial.acl2
tutorial.lisp

./c-files:
Makefile
minisat-output-formater.c
sat-input-formater.c
smt-prep.c
zchaff-output-formater.c

./doc:
sat-solver-interface.txt
tool-interface.txt

./scripts:
Makefile
make_results
sexpr-sat-solver.isf
sulfa-exec-smt.isf
sulfa-smt-saved-exec
sulfa-smt-saved-exec.isf
sulfa-smt.isf

./smt-examples:
smt-lib-crafted

./smt-examples/smt-lib-crafted:
bb.smt
bbb.smt
bit-counting.smt
bitops0.smt
bitops1.smt
bitops2.smt
bitops3.smt
bitops4.smt
bitops5.smt
bitops7.smt
bitvec0.smt
bitvec1.smt
bitvec2.smt
bitvec3.smt
bitvec4.smt
bitvec5.smt
bitvec6.smt
bitvec7.smt
bitvec8.smt
boolextract.smt
bv8.smt
bvlt.smt
")
 (:TITLE    "Tools for the Subclass of Unrollable List Formulas")
 (:AUTHOR/S "Erik Reeber" "Warren A. Hunt, Jr.")
 (:KEYWORDS
   "SULFA" "SAT" "SMT")
 (:ABSTRACT "
A SAT-based decision procedure for the Subclass of Unrollable List Formulas in
ACL2 (SULFA).  Our tool requires a special build process described in the
top-level README file.  See books/sat-tests/tutorial.lisp for an overview of
how to use the tool.
")
  (:PERMISSION ; author/s permission for distribution and copying:
"
SULFA -- Copyright (c) 2007, Erik Reeber and Warren A. Hunt, Jr.

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
Software), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"))
