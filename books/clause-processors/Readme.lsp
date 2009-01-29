((:FILES
"
.:
Makefile
Readme.lsp
basic-examples.acl2
basic-examples.lisp
bv-add-common.lisp
bv-add-tests.lisp
bv-add.lisp
equality.acl2
equality.lisp
generalize.acl2
generalize.lisp
join-thms.lisp
multi-env-trick.lisp
null-fail-hints.lisp
replace-impl.lisp
use-by-hint.lisp
")
 (:TITLE    "Clause processor examples")
 (:AUTHOR/S 
  "Jared Davis"
  "Matt Kaufmann"
  "Erik Reeber"
  "Sol Swords"
  )
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "clause processors"
   )
 (:ABSTRACT "This directory contains books that illustrates the use
of clause processors.  Also see :DOC clause-processors and the following
paper:

     M. Kaufmann, J S. Moore, S. Ray, and E. Reeber, \"Integrating
     External Deduction Tools with ACL2.\"  Proceedings of the 6th
     International Workshop on the Implementation of Logics (IWIL 2006)
     (C. Benzmueller, B. Fischer, and G. Sutcliffe, editors), CEUR
     Workshop Proceedings Vol. 212, Phnom Penh, Cambodia, pp. 7-26,
     November 2006, http://ceur-ws.org/Vol-212/.

Book basic-examples.lisp contains many examples of correct and incorrect
definitions and uses of trivial trusted and verified clause processors.

Books bv-add*.lisp illustrate the use of clause processors to implement a
decision procedure for bit vectors.

Book equality.lisp illustrates the use of clause processors to deal with
equality reasoning.

Book generalize.lisp provides a generalization clause processor.

Book join-thms.lisp automates the introduction of certain theorems about
evaluators that are useful for verifying clause processors.

Book multi-env-trick.lisp automates a trick for introducing clause
processors that allows each generated clause to be evaluated under multiple
binding alists in the correctness proof.

Book null-fail-hints.lisp introduces keyword hints :null, which does
nothing, and :fail, which causes the proof to fail.  These are probably not
as good as :no-op and :error, which are built into ACL2.

Book replace-impl.lisp introduces a clause processor that replaces a hyp
with something implied by that hyp.

Book use-by-hint introduces a computed hint to apply a particular :by hint
as signalled by a logically meaningless hyp placed in the clause, so that a
clause processor can produce clauses that are copies of statements of existing
theorems.
")
 (:PERMISSION
  "Clause processor examples
Copyright (C) 2007 by:
 Jared Davis <jared@cs.utexas.edu>       (equality.lisp)
 Matt Kaufmann <kaufmann@cs.utexas.edu>  (basic-examples.lisp)
 Erik Reeber <reeber@cs.utexas.edu>      (bv-add*.lisp)
 Sol Swords <sswords@cs.utexas.edu>      (generalize.lisp,
                                          multi-env-trick.lisp,
                                          use-by-hint.lisp)

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
