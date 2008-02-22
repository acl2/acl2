;; Readme.lsp file for the contribution books/proofstyles

(
 (:files 
 "
.:
Makefile
Readme.lsp
completeness
counterexamples
invclock
soundness

./completeness:
Makefile
assertions-partial.lisp
assertions-total.lisp
certify.lsp
clock-partial.lisp
clock-total.lisp
generic-partial.lisp
generic-total.lisp
stepwise-invariants-partial.lisp
stepwise-invariants-total.lisp

./counterexamples:
Makefile
README
certify.lsp
halt-flg.lisp
memory-clearing.lisp
realistic.lisp

proofstyles/invclock:
Makefile
Readme.lsp
c2i
certify.lsp
compose
i2c

proofstyles/invclock/c2i:
Makefile
c2i-partial.lisp
c2i-total.lisp
certify-c2i.lsp
clock-to-inv.lisp

proofstyles/invclock/compose:
Makefile
certify-compose.lsp
compose-c-c-partial.lisp
compose-c-c-total.lisp

proofstyles/invclock/i2c:
Makefile
certify-i2c.lsp
i2c-partial.lisp
i2c-total.lisp
inv-to-clock.lisp

./soundness:
Makefile
assertions-partial.lisp
assertions-total.lisp
certify.lsp
clock-partial.lisp
clock-total.lisp
stepwise-invariants-partial.lisp
stepwise-invariants-total.lisp

"
 )
 (:TITLE "Mechanical Proof of Soundness and Completeness of Three Proof Styles in ACL2")
 (:AUTHOR/S "Sandip Ray")
 (:Keywords "total correctness" 
            "partial correctness" 
            "inductive invariants"
            "assertions"
            "clock functions")
 (:ABSTRACT 
  
"We formalize three proof strategies used in the verification of
sequential programs in the logic of the ACL2 theorem prover.  The
strategies are (i) stepwise invariants, (ii) clock functions, and
(iii) inductive assertions.  We then mechanically prove that each
strategy is sound and complete.  By completeness, we mean that given
any proof of correctness of a sequential program, there is a proof of
correctness of the program in each o9f the three strategies")

 (:PERMISSION 

"Mechanical Proof of Soundness and Completeness of Three Proof Styles
in ACL2

Copyright (C) 2006 Sandip Ray and J Strother Moore

This program is free software; you can redistribute it and/ormodify it
under the terms of the GNU General Public Licenseas published by the
Free Software Foundation; either version 2 of the License, or (at your
option) any later version. This program is distributed in the hope
that it will be useful, but WITHOUT ANY WARRANTY; without even the
implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
PURPOSE.  See the GNU General Public License for more details.You
should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation,
Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA."))

Comments (Extension of Previous Work):

This set of books provides a generalization and extension of books in
the subdirectory invclock.  That subdirectory shows mechanical proofs
of inter-operability of two proof styles, stepwise invariants
(referred to as "inductive invariants" there) and clock functions.
This set of books shows much more general theorems, in particular that
the two proof styles above (and one other, namely inductive
assertions) are all sound and complete proof styles for sequential
program verification.  The inter-operability result now of course
follows trivially.

Additional Resource:

The following paper provides a high-level description of the insights
involved in the proof scripts here:

  S. Ray, W. A. Hunt, Jr., J. Matthews, and J S. Moore.  A Mechanical
  Analysis of Program Verification Strategies.  To Appear in Journal
  of Automated Reasoning. Springer.



