;TASPI 

((:FILES "
.:
Makefile
Readme.lsp
code
database
examples
proofs
read-write
sets-input
single-input
tree-distance
tree-generation
tree-score

./code:
Makefile
README
brlens
build
fringes
gen-helper
gen-trees
replete
sequences
tree-manip

./code/brlens:
Makefile
brlens.lisp
trees-with-brlens.lisp

./code/build:
Makefile
build-term-guards.lisp
build-term.lisp

./code/fringes:
Makefile
fringes-guards.lisp
fringes-props.lisp
fringes.lisp

./code/gen-helper:
Makefile
bdd-functions.lisp
extra.lisp
fast-lists.lisp
sets.lisp
top.lisp

./code/gen-trees:
Makefile
app-rev-lists.lisp
btrees-bdds-sets.lisp
btrees-bdds.lisp
btrees.lisp
sets-lists-trees.lisp
top.lisp
tree-predicates.lisp

./code/replete:
Makefile
replete-guards.lisp
replete-helper.lisp
replete.lisp

./code/sequences:
Makefile
align.lisp
p-inform.lisp
seqs.lisp

./code/tree-manip:
Makefile
insertion-based-sort.lisp
merge-based-sort.lisp
mv-root.lisp
quicksort.lisp
sort-help.lisp
top.lisp

./database:
Makefile
db-from-list.lisp
db.lisp
entry.lisp
filters.lisp
props.lisp

./examples:
examples.lisp
tr30-ta328.nwk
tr64-ta500-brlns.nwk

./proofs:
Makefile
fringes-taspi.acl2
fringes-taspi.lisp
omerge-good-order.acl2
omerge-good-order.lisp
sets.acl2
sets.lisp

./read-write:
newick.lisp
write-trees.lisp

./sets-input:
Makefile
consensus.lisp
greedy.lisp
mast.lisp
mct.lisp
multipolar-loose.lisp
top.lisp
tree-compat.lisp
tree-support-in-set.lisp

./single-input:
Makefile
taxa-based.lisp
tree-stats.lisp

./tree-distance:
Makefile
rf.lisp
symm-diff.lisp

./tree-generation:
Makefile
branch-and-bound
distance-based
heuristics
tree-gen-helper

./tree-generation/branch-and-bound:
Makefile
bandb.lisp

./tree-generation/distance-based:
Makefile
naive-quartet-method.lisp

./tree-generation/heuristics:
Makefile
do-search.lisp
spr.lisp
tbr.lisp

./tree-generation/tree-gen-helper:
Makefile
basics.lisp

./tree-score:
Makefile
ambig-score.lisp
circle-scoring.lisp
costs.lisp
efficient-pscores-help.lisp
efficient-pscores.lisp
fitch-scoring.lisp
min-length.lisp
opt-pairwise.lisp
pscores.lisp

"
)
 (:TITLE    "TASPI - Texas Analysis of Symbolic Phylogenetic Information")
 (:AUTHOR/S "S. Nelesen" "R. Boyer" "W. Hunt" ) 
 (:KEYWORDS "phylogenetics" "newick format" "tree compression" "consensus"
   )
 (:ABSTRACT
"This directory contains code relating to TASPI (Tree Analysis System for 
Phylogenetic Inference).  TASPI is specialized code for modeling collections
of phylogenetic trees and performing a few manipulations such as 
consensus analysis. Please note: TASPI relies on a version of ACL2 that 
includes HONS for its speed and memory requirement claims.

For further details, see: 

Serita Nelesen. Improved Methods for Phylogenetics. PhD Dissertation, 
The University of Texas at Austin, Dec 2009.

Warren A. Hunt Jr and Serita M. Nelesen. Phylogenetic Trees in ACL2. 
Proceedings of the 6th International Workshop on the ACL2 Theorem Prover 
and its Applications, Seattle, WA, August 15-16, 2006.

Robert S. Boyer, Warren A. Hunt Jr and Serita M. Nelesen. A Compressed 
Format for Collections of Phylogenetic Trees and Improved Consensus 
Performance. In Algorithms in Bioinformatics: 5th International 
Workshop, WABI 2005, number 3692 in Lecture Notes in Computer Science, 
pages 353-364, © Springer Berlin / Heidelberg, 2005.
")
 (:PERMISSION ; author/s permission for distribution and copying:
"TASPI
Copyright (C) 2011 S. Nelesen, R. Boyer and W. Hunt

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