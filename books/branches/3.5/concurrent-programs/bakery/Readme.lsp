;; Readme.lsp file for the contribution books/concurrent-programs/bakery/

(
 (:files
 "
.:
Makefile
Readme.lsp
apply-total-order.lisp
certify.lsp
fairenv.lisp
final-theorems.lisp
initial-state.lisp
inv-persists.lisp
inv-sufficient.lisp
labels.lisp
lexicographic-pos.lisp
lexicographic.lisp
measures.lisp
pos-temp.lisp
programs.lisp
properties-of-sets.lisp
properties.lisp
records.lisp
stutter1-match.lisp
stutter2.lisp
variables.lisp
"
 )
 (:TITLE "A Verification  of the Bakery Algorithm")
 (:AUTHOR/S "Sandip Ray")
 (:Keywords "Trace Containment"
             "Mutual exclusion"
             "Stuttering"
             "Refinement proofs"
             "Simulation"
             "Bisimulation"
             "Concurrent Protocols"
             "Fairness")
 (:ABSTRACT

"This set of books shows how one can use stuttering trace containment with
fairness constraints to verify concurrent protocols.  We apply the method here
to prove the correctness of an implementation of the Bakery algorithm.  The
implementation is interesting in the sense that it depends critically on fair
selection of processes to ensure absence of deadlock.  We show how the
requisite notions can be formalized as generic theories and used in the proof
of refinements."  
)
 (:PERMISSION

"A Verification of the Bakery Algorithm
Copyright (C) 2006 Sandip Ray

Contains several key contributions by Rob Sumners, in particular a version of
the records book and a specific formalization of fairness.

This program is free software; you can redistribute it and/ormodify it under
the terms of the GNU General Public Licenseas published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc., 51
Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA."
))

This set of books shows how the notion of stuttering trace containment can be
used with a formalization of fairness effectively to verify concurrent
protocols via single-step theorems.  We consider an implementation of the
Bakery algorithm, which is a well-known mutual exclusion protocol from the
literature.  The implementation makes critical use of fairness assumptions to
ensure progress.  Fairness is formalized by encapsulating the appropriate
notion of fair environments in ACL2.  The result is a proof that the
implementation is a refinement up to fairness of a simple atomic mutex
protocol.

Background
----------

This work was done by the author in 2000 following up the ideas of Manolios,
Namjoshi and Sumners on well-founded bisimulations (WEBs).  The verification
was inspired by a WEB proof done by Sumners to verify a concurrent deque
implementation.  To follow up that work, this work investigates how fairness
constraints can be used together with refinement proofs and strives to
determine an effective, formal, and usable notion of fairness.  The notion we
develop here is a version of what is known in the literature as weak fairness.
We show how that notion is sufficient and useful for verifying the protocol.

History and Acknowledgements
----------------------------

This set of books represents the author's first non-trivial proof (and
research) project with ACL2.  The proof was first done in 2000-01 using ACL2
versions 2.5 and 2.6.  Rob Sumners helped significantly in this work, and
contributed a version of the records book together with an early version of
fairness.lisp.  The notion of fairness was then refined by Sumners and the
results reported in a paper in ACL2 2003.  The work also led to the
understanding of the essence and difficulty of invariant proofs for concurrent
programs, which eventually led to the investigation of the use of predicate
abstraction to automate the process.

In addition to the technical interest of using refinements with fairness, the
books should also be interesting just from the perspective of proof development
in ACL2 by new users.  The proof was embarked on when the author was a novice
ACL2 user, having done no more than some of the exercises in ACL2.  So the
implementors of ACL2 looking at how a novice works on a reasonably large proof
project might have an understanding of how to make ACL2 more palatable to such
users.  The proof scripts are provided essentially the way the author created
them on the first shot, with little extra massaging (other than a few things to
make the proofs work with the current version of ACL2).  [The reason for the
latter is of course the perpetual disinclination of the author to look at
successful proofs.]

The author is thankful to Rob Sumners for significant advice and help with
ACL2.

For questions and concerns about these books, contact sandip@cs.utexas.edu.