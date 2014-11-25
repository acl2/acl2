; This file was initially generated automatically from legacy documentation
; strings.  See source files in this directory for copyright and license
; information.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc *dna-cssl*
  :parents (taspi)
  :short "The usual mapping for dna character states to their dna score-list."
  :long "")

(defxdoc *dna-matrix*
  :parents (taspi)
  :short "A dna transition cost matrix with all transitions having cost 1."
  :long "")

(defxdoc all-same-num-tips
  :parents (taspi)
  :short "Determines if all of the trees in the input have the same number of leaves."
  :long "<p>Arguments: (1) list - a list of trees</p>

 <p>Details: Does not matter if branch lengths are present or not.</p>")

(defxdoc bandb
  :parents (taspi)
  :short "Performs a breadth first branch and bound search for a maximum parsimony
tree for sequences"
  :long "<p>Arguments: (1) seq - a set of sequences (2) cssl-map - An alist
   mapping every character state to a list containing one element (either 0 or
   nil for infinity) for each unambiguous state (3) matrix - A mapping of
   unambiguous character states to transition costs.  (4) tia - a mapping of
   taxa names to integers</p>

 <p>Details: The taxa names in the tia should match those given as keys in
 seq.</p>")

(defxdoc bfringe
  :parents (taspi)
  :short "Returns the bdd based bipartition implied by the (sub)tree given."
  :long "<p>Arguments: (1) x - a tree (usually a subtree of some larger
    tree) (2) ta - a mapping of taxa-names their bdd based representation</p>

 <p>Details: Arguments can actually be more general.  Another way to think of
         this is that it returns the taxa names in the tree x, represented as a
         bdd.  Requires that the taxa names in the tree are keys in the ta
         argument.</p>")

(defxdoc bfringe-brlens
  :parents (taspi)
  :short "Returns the bdd based bipartition implied by the (sub)tree given."
  :long "<p>Arguments: (1) x - a tree (usually a subtree of some larger
    tree) (2) ta - a mapping of taxa-names their bdd based representation</p>

 <p>Details: Arguments can actually be more general.  Another way to think of
         this is that it returns the taxa names in the tree x, represented as a
         bdd.  May require that the taxa names in the tree are keys in the ta
         argument.</p>")

(defxdoc bfringe-frequencies
  :parents (taspi)
  :short "Returns a mapping of the bdd based bipartitions present in the input list
of trees to the number of times it appeared in the input."
  :long "<p>Arguments: (1) l - a list of trees (2) taxa-list - a list of
  taxa</p>

 <p>Details: Trees in input list should not have branch lengths.  Trees should
         all be ordered according to the taxa list given.</p>")

(defxdoc bfringe-frequencies-brlens
  :parents (taspi)
  :short "Returns a mapping of the bdd based bipartitions present in the input list
of trees to the number of times it appeared in the input."
  :long "<p>Arguments: (1) l - a list of trees (2) taxa-list - a list of
  taxa</p>

 <p>Details: Trees in input list may have branch lengths.  Trees should all be
         ordered according to the taxa list given.</p>")

(defxdoc branch-by-branch-proportion-support
  :parents (taspi)
  :short "Returns a listing of branches in the input tree and the proportion of trees
in the input set that support that branch"
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (3)
   taxa-list - a list of taxa names</p>

 <p>Details: All trees must have the taxa list given.  Bipartitions returned
          are bdd based.  Does not allow branch lengths (see
          branch-by-branch-proportion-support).</p>")

(defxdoc branch-by-branch-proportion-support-brlens
  :parents (taspi)
  :short "Returns a listing of branches in the input tree and the proportion of trees
in the input set with branch lengths that support that branch"
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (3)
   taxa-list - a list of taxa names</p>

 <p>Details: All trees must have the taxa list given.  Bipartitions returned
          are bdd based.  Allows branch lengths (see
          branch-by-branch-proportion).</p>")

(defxdoc branch-by-branch-tree-support
  :parents (taspi)
  :short "Returns a listing of branches in the input tree and the trees supporting
that branch from the input set"
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (3)
   taxa-list - a list of taxa names</p>

 <p>Details: All trees must have the taxa list given.  Bipartitions returned
          are bdd based.  Does not allow branch lengths (see
          branch-by-branch-tree-support-brlens).</p>")

(defxdoc branch-by-branch-tree-support-brlens
  :parents (taspi)
  :short "Returns a listing of branches in the input tree and the trees supporting
that branch from the input set"
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (3)
   taxa-list - a list of taxa names</p>

 <p>Details: All trees must have the taxa list given.  Bipartitions returned
          are bdd based.  Allows branch lengths (see
          branch-by-branch-tree-support) but the trees returned do not have
          branch lengths.</p>")

(defxdoc btree-to-fringe
  :parents (taspi)
  :short "Returns the list based version of the bdd based bipartition given."
  :long "<p>Arguments: (1) btree - a bdd based bipartition (2)
    full-taxa-list-tree - a binary tree based version of the taxa list</p>

 <p>Details: The btree given must have a depth less than that of the
          full-taxa-list-tree and the resulting bipartition will have the taxa
          given in the full-taxa-list-tree.</p>")

(defxdoc btrees-to-fringes
  :parents (taspi)
  :short "Returns the list based version of bdd based bipartitions given."
  :long "<p>Arguments: (1) fringe-list - a list of bdd based bipartitions (2)
    full-taxa-list-tree - a binary tree based version of the taxa list</p>

 <p>Details: The bdd based bipartitions must each have a depth less than that
          of the full-taxa-list-tree.  The resulting list based bipartitions
          will have the taxa given in the full-taxa-list-tree.</p>")

(defxdoc build-arbitrarytree
  :parents (taspi)
  :short "Returns a binary unrooted two-ladder tree with taxa names given reversed."
  :long "<p>Arguments: (1) taxa - a list of taxa names</p>")

(defxdoc build-arbitrarytree1
  :parents (taspi)
  :short "Returns a binary unrooted two-ladder tree with taxa names given."
  :long "<p>Arguments: (1) taxa - a list of taxa names</p>")

(defxdoc build-taxa-list-tree
  :parents (taspi)
  :short "Returns a mapping from each taxon in list to each taxon's bdd representation"
  :long "<p>Arguments: (1) taxa-list - a list of taxa</p>")

(defxdoc build-term-top
  :parents (taspi)
  :short "Returns the tree implied by the bipartitions given."
  :long "<p>Arguments: (1) bdd-fringes - a list of bdd based bipartitions (2)
 taxa-list - a list of taxa names</p>

 <p>Details: BDD based bipartitions should have been created using the
          taxa-list given.  Tree returned will be ordered according the order
          implied by the taxa list given. NOTE: Representation returned is
          rooted at the *longest* bipartition but could/should probably use
          mv-root when building an unrooted tree.</p>")

(defxdoc build-term-top-guard-t
  :parents (taspi)
  :short "Returns the tree implied by the bipartitions given."
  :long "<p>Arguments: (1) bdd-fringes - a list of bdd based bipartitions (2)
 taxa-list - a list of taxa names</p>

 <p>Details: BDD based bipartitions should have been created using the
          taxa-list given.  Tree returned will be ordered according the order
          implied by the taxa list given. Same computation as build-term-top,
          but well-formedness of input is explicitly checked.  NOTE:
          Representation returned is rooted at the *longest* bipartition but
          could/should probably use mv-root when building an unrooted
          tree.</p>")

(defxdoc build-unrooted-binary-tree
  :parents (taspi)
  :short "Returns a binary unrooted ladder tree with taxa names given."
  :long "<p>Arguments: (1) taxa - a list of taxa names</p>")

(defxdoc charstate-scorelist-map-p
  :parents (taspi)
  :short "Recognizes a well-formed mapping from possible character states to its
score list of length alpha-len."
  :long "<p>Arguments: (1) x - a potential character state scorelist (2)
    alpha-len - the required alphabet length (number of unambiguous
    characters)</p>")

(defxdoc compute-consensus
  :parents (taspi)
  :short "Computes the majority consensus of a set of trees"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names (3) percentage - an integer between 0 and 100</p>

 <p>Details: Trees given must match taxa list given and all have the same
          number of leaves.  Does not handle branch lengths (see
          compute-consensus-brlens). NOTE: Guards not yet verified.</p>")

(defxdoc compute-consensus-brlens
  :parents (taspi)
  :short "Computes the majority consensus of a set of trees with branch lengths"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names (3) percentage - an integer between 0 and 100</p>

 <p>Details: Trees given must match taxa list given and all have the same
          number of leaves.  Allows branch lengths (see also
          compute-consensus). Guards are not yet verified.</p>")

(defxdoc compute-frequencies
  :parents (taspi)
  :short "Returns a mapping of bdd based bipartitions to their frequencies in
list-of-trees."
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: Does not allow branch lengths on input trees.  Manages memory more
          explicitly than bfringe-frequencies.</p>")

(defxdoc compute-frequencies-brlens
  :parents (taspi)
  :short "Returns a mapping of bdd based bipartitions to their frequencies in
list-of-trees."
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: Allows branch lengths.  Manages memory more explicitly than
          bfringe-frequencies-brlens.</p>")

(defxdoc cost-matrixp-nstates
  :parents (taspi)
  :short "Recognizes a well-formed cost matrix with n states."
  :long "<p>Arguments: (1) x - a potential cost matrix (2) n - the number of
    unambiguous characters</p>")

(defxdoc count-tips
  :parents (taspi)
  :short "Returns the number of leaves in a tree."
  :long "<p>Arguments: (1) x - a tree</p>

 <p>Details: Does not matter if branch lengths are present or not.</p>")

(defxdoc degree-of-tree
  :parents (taspi)
  :short "Returns the degree of the input tree."
  :long "<p>Arguments: (1) rooted-flg - non-nil for a rooted tree, nil for an
   unrooted tree (2) x - a tree</p>")

(defxdoc depth-bandb
  :parents (taspi)
  :short "Performs a depth first branch and bound search for a maximum parsimony
tree for sequences"
  :long "<p>Arguments: (1) seq - a set of sequences (2) cssl-map - An alist
   mapping every character state to a list containing one element (either 0 or
   nil for infinity) for each unambiguous state (3) matrix - A mapping of
   unambiguous character states to transition costs.  (4) tia - a mapping of
   taxa names to integers</p>

 <p>Details: The taxa names in the tia should match those given as keys in
 seq.</p>")

(defxdoc diameter-brlens
  :parents (taspi)
  :short "Returns the diameter of the input tree using branch lengths given."
  :long "<p>Arguments: (1) x - a tree

 Details: Maximum path distance between any two taxa in tree.  See also
          diameter-no-brlens.</p>")

(defxdoc diameter-no-brlens
  :parents (taspi)
  :short "Returns the diameter of the input tree assuming unit branch lengths."
  :long "<p>Arguments: (1) x - a tree

 Details: Maximum path distance between any two taxa in tree.  See
          diameter-brlens.</p>")

(defxdoc find-closest-by-rf
  :parents (taspi)
  :short "Returns a tree from list closest according to rf rate to the given tree."
  :long "<p>Arguments: (1) tree - a tree (2) list - a list of trees (3) rooted1
   - a flag indicating rootedness of tree (4) rooted2 - a flag indicating
   rootedness of each tree in list</p>

 <p>Details: Trees input may have branch lengths but they will not be preserved
          in the tree returned.  A single tree is returned even if equally
          close trees exist in the input list.</p>")

(defxdoc first-taxon
  :parents (taspi)
  :short "Returns the taxon name first appearing in the tree representation."
  :long "<p>Arguments: (1) term - a tree</p>

 <p>Details: Does not matter if branch lengths are present or not.</p>")

(defxdoc frequency
  :parents (taspi)
  :short "Returns the number of times the list based fringe x occurs as implied by the
database given."
  :long "<p>Arguments: (1) x - a list based fringe (2) db - a mapping of
    subtrees to integers or parent lists (such as that produced by replete)

 Details: The database must have appropriate structure (but is produced as
          necessary by replete).  The underlying taxa list should be consistent
          between both the fringe and the database.</p>")

(defxdoc fringe-frequencies
  :parents (taspi)
  :short "Returns a mapping of the list based bipartitions present in the input list
of trees to the number of times it appeared in the input."
  :long "<p>Arguments: (1) l - a list of trees</p>

 <p>Details: Trees in input list should not have branch lengths.  Trees should
         all be ordered according to the same underlying taxa list.  See also
         fringe-frequencies-brlens.</p>")

(defxdoc fringe-frequencies-brlens
  :parents (taspi)
  :short "Returns a mapping of the list based bipartitions present in the input list
of trees to the number of times it appeared in the input."
  :long "<p>Arguments: (1) l - a list of trees</p>

 <p>Details: Trees in input list may have branch lengths.  Trees should all be
         ordered according to the same underlying taxa list.</p>")

(defxdoc get-all-fringes
  :parents (taspi)
  :short "Returns all bdd based bipartitions present in the trees input."
  :long "<p>Arguments: (1) trees - a list of trees (2) taxa-list - a list of
   taxa names</p>

 <p>Details: Trees should have taxa list given and no branch lengths.</p>")

(defxdoc get-analysis-id
  :parents (taspi)
  :short "Returns the analysis-id of a tree table entry."
  :long "")

(defxdoc get-analysis-ids
  :parents (taspi)
  :short "Returns analysis ids present in a tree table."
  :long "")

(defxdoc get-analysis-ids-with-author
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given author."
  :long "<p>Arguments: (1) author - a author name (2) analysis-tbl - an
  analysis table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-analysis-ids-with-data-type
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given data type."
  :long "<p>Arguments: (1) data-type - a data type name (2) analysis-tbl - an
   analysis table (3) tree-tbl - a tree table</p>")

(defxdoc get-analysis-ids-with-date
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given date."
  :long "<p>Arguments: (1) date - a date name (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-analysis-ids-with-method
  :parents (taspi)
  :short "Returns analysis ids from the analysis table that have the given method."
  :long "<p>Arguments: (1) method - a method name (2) analysis-tbl - an
  analysis table</p>")

(defxdoc get-analysis-ids-with-model
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given model."
  :long "<p>Arguments: (1) model - a model name (2) analysis-tbl - an analysis
  table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-analysis-ids-with-n-taxa
  :parents (taspi)
  :short "Returns analysis ids from the analysis table that have the given number
taxa."
  :long "<p>Arguments: (1) n - an integer (2) analysis-tbl - an analysis
  table</p>")

(defxdoc get-analysis-ids-with-taxa
  :parents (taspi)
  :short "Returns analysis ids from the analysis table that have the given set of
taxa."
  :long "<p>Arguments: (1) taxa - a list of taxa name (2) analysis-tbl - an
   analysis table</p>")

(defxdoc get-analysis-ids-with-taxon
  :parents (taspi)
  :short "Returns analysis ids from the analysis table whose entries have the given
taxon."
  :long "<p>Arguments: (1) taxon - a taxon name (2) analysis-tbl - an analysis
  table</p>")

(defxdoc get-analysis-ids-with-tool
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given tool."
  :long "<p>Arguments: (1) tool - a tool name (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-author
  :parents (taspi)
  :short "Returns the author of an analysis table entry."
  :long "")

(defxdoc get-brlens-flg
  :parents (taspi)
  :short "Returns the presence of branch lengths flag of a tree table entry."
  :long "")

(defxdoc get-containing-subtree-of-taxa
  :parents (taspi)
  :short "Returns subtree of tree containing each taxon in taxa."
  :long "<p>Arguments: (1) taxa - a list of taxa names (2) tree - a tree

 Details: Assumes a rooted tree with no branch lengths (see also
          get-containing-subtree-of-taxa-brlens).</p>")

(defxdoc get-containing-subtree-of-taxa-brlens
  :parents (taspi)
  :short "Returns subtree of tree containing each taxon in taxa."
  :long "<p>Arguments: (1) taxa - a list of taxa names (2) tree - a tree

 Details: Assumes a rooted tree.  Does not preserve branch lengths if
          present (see also get-containing-subtree-of-taxa).</p>")

(defxdoc get-data-type
  :parents (taspi)
  :short "Returns the data-type of an analysis table entry."
  :long "")

(defxdoc get-date
  :parents (taspi)
  :short "Returns the date of an analysis table entry."
  :long "")

(defxdoc get-entry-by-id
  :parents (taspi)
  :short "Returns entry in table indicated by given id."
  :long "<p>Arguments: (1) id - a primary id (2) tbl - a good study, analysis
   or tree table</p>")

(defxdoc get-id
  :parents (taspi)
  :short "Returns the primary key of a table entry."
  :long "")

(defxdoc get-ingroup
  :parents (taspi)
  :short "Returns the ingroup of an analysis table entry."
  :long "")

(defxdoc get-kernal-splits
  :parents (taspi)
  :short "Returns those bipartitions in bfringes-left compatible with the entire set"
  :long "<p>Arguments: (1) bfringes-left - a set of bdd based bipartitions (2)
   all-bfringes - a set of bdd based bipartitions</p>

 <p>Details: Arguments should have been created using the same taxa-list.
          First argument should always be a subset of second.</p>")

(defxdoc get-method
  :parents (taspi)
  :short "Returns the method of an analysis table entry."
  :long "")

(defxdoc get-ml
  :parents (taspi)
  :short "Returns the maximum likelihood score of a tree table entry."
  :long "")

(defxdoc get-model
  :parents (taspi)
  :short "Returns the model of an analysis table entry."
  :long "")

(defxdoc get-mp
  :parents (taspi)
  :short "Returns the maximum parsimony score of a tree table entry."
  :long "")

(defxdoc get-name
  :parents (taspi)
  :short "Returns the name of a table entry."
  :long "")

(defxdoc get-outgroup
  :parents (taspi)
  :short "Returns the outgroup of an analysis table entry."
  :long "")

(defxdoc get-rooted-flg
  :parents (taspi)
  :short "Returns the rootedness flag of a tree table entry."
  :long "")

(defxdoc get-sequences
  :parents (taspi)
  :short "Returns the sequences from a study table entry."
  :long "")

(defxdoc get-study-id
  :parents (taspi)
  :short "Returns the study-id of an analysis table entry."
  :long "")

(defxdoc get-study-ids
  :parents (taspi)
  :short "Returns study ids present in an analysis table."
  :long "")

(defxdoc get-taxa-from-index-taxon
  :parents (taspi)
  :short "Returns the list of taxa names from a mapping of integers to taxa names."
  :long "<p>Arguments: (1) x - a mapping of integers to taxa names.</p>")

(defxdoc get-taxa-from-sequences
  :parents (taspi)
  :short "Returns the taxa-list implied by a set of sequences"
  :long "<p>Arguments: (1) x - a valid set of sequences</p>")

(defxdoc get-taxa-from-taxon-index
  :parents (taspi)
  :short "Returns the taxa names from a mapping of taxa names to integers."
  :long "<p>Arguments: (1) x - a mapping of taxa names to integers.</p>")

(defxdoc get-taxa-list
  :parents (taspi)
  :short "Returns the taxa list of an analysis table entry."
  :long "")

(defxdoc get-tool
  :parents (taspi)
  :short "Returns the tool of an analysis table entry."
  :long "")

(defxdoc get-tree
  :parents (taspi)
  :short "Returns the tree of a tree table entry."
  :long "")

(defxdoc get-tree-ids-with-analysis-id
  :parents (taspi)
  :short "Returns tree ids from the tree table whose entries have the given
analysis-id."
  :long "<p>Arguments: (1) analysis-id - an id (2) tree-tbl - a tree
  table</p>")

(defxdoc get-tree-ids-with-analysis-ids
  :parents (taspi)
  :short "Returns tree ids from the tree table whose entries have one of the given
analysis-ids."
  :long "<p>Arguments: (1) analysis-ids - a list of ids (2) tree-tbl - a tree
  table</p>")

(defxdoc get-tree-ids-with-author
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given author."
  :long "<p>Arguments: (1) author - a author name (2) analysis-tbl - an
  analysis table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-data-type
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given data type."
  :long "<p>Arguments: (1) data-type - a data-type name (2) analysis-tbl - an
   analysis table (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-date
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given date."
  :long "<p>Arguments: (1) date - a date name (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-method
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given method."
  :long "<p>Arguments: (1) method - a method name (2) analysis-tbl - an
  analysis table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-model
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given model."
  :long "<p>Arguments: (1) model - a model name (2) analysis-tbl - an analysis
  table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-n-taxa
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given number taxa."
  :long "<p>Arguments: (1) n - an integer (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-taxa
  :parents (taspi)
  :short "Returns trees from the tree table that have the given set of
taxa."
  :long "<p>Arguments: (1) taxa - a list of taxa name (2) analysis-tbl - an
   analysis table (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-taxon
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given taxon."
  :long "<p>Arguments: (1) taxon - a taxon name (2) analysis-tbl - an analysis
  table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-ids-with-tool
  :parents (taspi)
  :short "Returns tree ids from the tree table that have the given tool."
  :long "<p>Arguments: (1) tool - a tool name (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-tree-type
  :parents (taspi)
  :short "Returns the tree type of a tree table entry."
  :long "")

(defxdoc get-trees-with-analysis-id
  :parents (taspi)
  :short "Returns trees from the tree table whose entries have the given
analysis-id."
  :long "<p>Arguments: (1) analysis-id - an id (2) tree-tbl - a tree
  table</p>")

(defxdoc get-trees-with-analysis-ids
  :parents (taspi)
  :short "Returns trees from the tree table whose entries have one of the given
analysis-ids."
  :long "<p>Arguments: (1) analysis-ids - a list of ids (2) tree-tbl - a tree
   table</p>")

(defxdoc get-trees-with-author
  :parents (taspi)
  :short "Returns trees from the tree table that have the given author."
  :long "<p>Arguments: (1) author - a author name (2) analysis-tbl - an
  analysis table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-data-type
  :parents (taspi)
  :short "Returns trees from the tree table that have the given data type."
  :long "<p>Arguments: (1) data-type - a data type name (2) analysis-tbl - an
   analysis table (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-date
  :parents (taspi)
  :short "Returns trees from the tree table that have the given date."
  :long "<p>Arguments: (1) date - a date name (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-method
  :parents (taspi)
  :short "Returns trees from the tree table that have the given method."
  :long "<p>Arguments: (1) method - a method name (2) analysis-tbl - an
  analysis table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-model
  :parents (taspi)
  :short "Returns trees from the tree table that have the given model."
  :long "<p>Arguments: (1) model - a model name (2) analysis-tbl - an analysis
  table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-n-taxa
  :parents (taspi)
  :short "Returns trees from the tree table that have the given number taxa."
  :long "<p>Arguments: (1) n - an integer (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-taxa
  :parents (taspi)
  :short "Returns trees from the tree table that have the given set of
taxa."
  :long "<p>Arguments: (1) taxa - a list of taxa name (2) analysis-tbl - an
   analysis table (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-taxon
  :parents (taspi)
  :short "Returns trees from the tree table that have the given taxon."
  :long "<p>Arguments: (1) taxon - a taxon name (2) analysis-tbl - an analysis
  table
   (3) tree-tbl - a tree table</p>")

(defxdoc get-trees-with-tool
  :parents (taspi)
  :short "Returns trees from the tree table that have the given tool."
  :long "<p>Arguments: (1) tool - a tool name (2) analysis-tbl - an analysis
   table (3) tree-tbl - a tree table</p>")

(defxdoc good-analysis-entry
  :parents (taspi)
  :short "Recognizes a well-formed analysis table entry."
  :long "")

(defxdoc good-analysis-table
  :parents (taspi)
  :short "Recognizes a well-formed analysis table."
  :long "")

(defxdoc good-author
  :parents (taspi)
  :short "Recognizes a well-formed author specification."
  :long "")

(defxdoc good-brlens-flg
  :parents (taspi)
  :short "Recognizes a well-formed flag indicating branch length presence."
  :long "")

(defxdoc good-data-type
  :parents (taspi)
  :short "Recognizes a well-formed data type specification."
  :long "")

(defxdoc good-date
  :parents (taspi)
  :short "Recognizes a well-formed date specification."
  :long "")

(defxdoc good-id
  :parents (taspi)
  :short "Recognizes a well-formed id."
  :long "")

(defxdoc good-ingroup
  :parents (taspi)
  :short "Recognizes a well-formed ingroup."
  :long "<p>Arguments: (1) group - potential ingroup (2) tl - a list of
  taxa</p>

 <p>Details: A good ingroup is a subset of the given taxa.</p>")

(defxdoc good-method
  :parents (taspi)
  :short "Recognizes a well-formed method specification."
  :long "")

(defxdoc good-ml
  :parents (taspi)
  :short "Recognizes a well-formed maximum likelihood score."
  :long "")

(defxdoc good-model
  :parents (taspi)
  :short "Recognizes a well-formed model specification."
  :long "")

(defxdoc good-mp
  :parents (taspi)
  :short "Recognizes a well-formed maximum parsimony score."
  :long "")

(defxdoc good-name
  :parents (taspi)
  :short "Recognizes a well-formed name specfication."
  :long "")

(defxdoc good-outgroup
  :parents (taspi)
  :short "Recognizes a well-formed outgroup."
  :long "<p>Arguments: (1) group - potential outgroup (2) tl - a list of
  taxa</p>

 <p>Details: A good outgroup is a subset of the given taxa.</p>")

(defxdoc good-rooted-flg
  :parents (taspi)
  :short "Recognizes a well-formed flag indicating rootedness."
  :long "")

(defxdoc good-study-entry
  :parents (taspi)
  :short "Recognizes a well-formed study table entry."
  :long "")

(defxdoc good-study-table
  :parents (taspi)
  :short "Recognizes a well-formed study table."
  :long "")

(defxdoc good-taxa-list
  :parents (taspi)
  :short "Recognizes a well formed list of taxa names."
  :long "<p>Arguments: (1) tl - a potential list of taxa names</p>")

(defxdoc good-tool
  :parents (taspi)
  :short "Recognizes a well-formed tool specification."
  :long "")

(defxdoc good-tree
  :parents (taspi)
  :short "Determines if a tree is well-formed."
  :long "<p>Arguments: (1) tree - a potential tree</p>

 <p>Details: Does not recognize trees with branch lengths.  Requires both treep
          and taspip.</p>")

(defxdoc good-tree-db
  :parents (taspi)
  :short "Recognizes a well formed and consistent set of tables."
  :long "<p>Arguments: (1) study-tbl - a potential study table (2) analysis-tbl
   - a potential analysis table (3) tree-tbl - a potential tree table</p>

 <p>Details: Checks that primary ids are unique, ids indexing into other tables
          reference existing entries, maximum likelihood scores have an
          associated model, and that any tree in the tree table has taxa names
          present in the taxa list in the associated analysis table.</p>")

(defxdoc good-tree-entry
  :parents (taspi)
  :short "Recognizes a well-formed tree table entry."
  :long "")

(defxdoc good-tree-table
  :parents (taspi)
  :short "Recognizes a well-formed tree table."
  :long "")

(defxdoc good-tree-tl
  :parents (taspi)
  :short "Determines if a tree matches a taxa list and is ordered accordingly."
  :long "<p>Arguments: (1) tree - a tree (2) tl - a taxa list</p>")

(defxdoc good-tree-type
  :parents (taspi)
  :short "Recognizes a well-formed tree type specification."
  :long "")

(defxdoc greedy
  :parents (taspi)
  :short "Computes the greedy consensus of a set of trees"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - list
    of taxa</p>

 <p>Details: List-of-trees must have the given taxa list.  The greedy consensus
          orders the bipartitions found by their frequencies and adds
          bipartitions to the consensus starting with the most frequent,
          skipping conflicting bipartitions, until no non-conflicting
          bipartition remains. Greedy consensus will be a refinement of the
          majority consensus.  Does not allow branch lengths (see
          greedy-brlens).</p>")

(defxdoc greedy-brlens
  :parents (taspi)
  :short "Computes the greedy consensus of a set of trees with branch lengths"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - list
    of taxa</p>

 <p>Details: List-of-trees must have the given taxa list.  The greedy consensus
          orders the bipartitions found by their frequencies and adds
          bipartitions to the consensus starting with the most frequent,
          skipping conflicting bipartitions, until no non-conflicting
          bipartition remains. Greedy consensus will be a refinement of the
          majority consensus.  Allow branch lengths (see greedy).</p>")

(defxdoc lca
  :parents (taspi)
  :short "Returns least common ancestor of taxa a and b in tree."
  :long "<p>Arguments: (1) a - a taxon name (2) b - a taxon name (3) tree - a
  tree

 Details: Returns empty tree if no common ancestor exists.</p>")

(defxdoc len-path-to-taxon
  :parents (taspi)
  :short "Returns path length from root to taxon indicated assuming unit lengths on
each branch."
  :long "<p>Arguments: (1) taxon - a taxon name (2) tree - a tree (3) acc -
  accumulator
   (initially 0)</p>")

(defxdoc len-path-to-taxon-brlens
  :parents (taspi)
  :short "Returns path length from root to taxon indicated using branch lengths given
in tree on each branch."
  :long "<p>Arguments: (1) taxon - a taxon name (2) tree - a tree with branch
  lengths
   (3) acc - accumulator (initially 0)</p>")

(defxdoc loose
  :parents (taspi)
  :short "Computes the loose consensus of a set of trees"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - list
    of taxa</p>

 <p>Details: List-of-trees must have the given taxa list.  The loose consensus
          contains those biparititions in the list of trees given that are
          compatible with every other bipartition present.  Does not allow
          branch lengths (see loose-brlens).</p>")

(defxdoc loose-brlens
  :parents (taspi)
  :short "Computes the loose consensus of a set of trees with branch lengths"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - list
   of taxa</p>

 <p>Details: List-of-trees must have the given taxa list.  The loose consensus
          contains those biparititions in the list of trees given that are
          compatible with every other bipartition present. Allows branch
          lenghts (see loose).</p>")

(defxdoc make-tia
  :parents (taspi)
  :short "Builds a mapping from taxa names to integers."
  :long "<p>Arguments: (1) x - a list of taxa names</p>

 <p>Details: Same as taxa-list-to-taxon-index, but shorter name.</p>")

(defxdoc mast
  :parents (taspi)
  :short "Computes the maximum agreement subtree of a set of trees"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: Returns a single maximum agreement tree even if there exists more
          than one.  Does not handle branch lengths (see mast-brlens).</p>")

(defxdoc mast-brlens
  :parents (taspi)
  :short "Computes the maximum agreement subtree of a set of trees with branch lengths"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: Returns a single maximum agreement tree even if there exists more
          than one.  Allows branch lengths (see mast).</p>")

(defxdoc mct
  :parents (taspi)
  :short "Computes the maximum compatibility tree of a set of trees"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: The trees given should have taxa list given and no branch lengths
          (see also mct-brlens).  Returns a single maximum compatibility tree
          even if there exists more than one.</p>")

(defxdoc mct-brlens
  :parents (taspi)
  :short "Computes the maximum compatibility tree of a set of trees with branch lengths"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: The trees given should have taxa list given and may or may not
          have branch lengths (see also mct).  Returns a single maximum
          compatibility tree even if there exists more than one.</p>")

(defxdoc monophyletic?
  :parents (taspi)
  :short "Determines if set of taxa is monophyletic in tree."
  :long "<p>Arguments: (1) taxa - a list of taxa names (2) tree - a tree

 Details: Assumes a rooted tree with no branch lengths (see also
          monophyletic?-brlens).</p>")

(defxdoc monophyletic?-brlens
  :parents (taspi)
  :short "Determines if set of taxa is monophyletic in tree."
  :long "<p>Arguments: (1) taxa - a list of taxa names (2) tree - a tree

 Details: Assumes a rooted tree.  Does not preserve branch lengths if
          present (see also monophyletic?-brlens).</p>")

(defxdoc multipolar
  :parents (taspi)
  :short "Returns the multipolar consensus of list-of-trees, using proportion alpha."
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) alpha - rational
    between 0 and 1 indicating ratio at which bipartitions are displayed (3)
    taxa-list - a list of taxa</p>

 <p>Details: List-of-trees must have the taxa list given. Uses a greedy
          coloring algorithm where vertex order is determined by the frequency
          of representative bipartition.  Does not handle branch lengths (see
          multipolar-brlens).</p>")

(defxdoc multipolar-brlens
  :parents (taspi)
  :short "Returns the multipolar consensus of list-of-trees, using proportion alpha."
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) alpha - rational
    between 0 and 1 indicating ratio at which bipartitions are displayed (3)
    taxa-list - a list of taxa</p>

 <p>Details: List-of-trees must have the taxa list given. Uses a greedy
          coloring algorithm where vertex order is determined by the frequency
          of representative bipartition.  Allows branch lengths (see also
          multipolar).</p>")

(defxdoc mv-root
  :parents (taspi)
  :short "Returns the structurally unchanged unrooted tree now with a representation
rooted at the node connecting the first taxon according to the mapping
given to the rest of the tree."
  :long "<p>Arguments: (1) x - an unrooted tree (2) tia - a mapping from each
   taxa name to an integer</p>

 <p>Details: Must be called on an unrooted tree in order to not change
          structure.  If the initial representation is ordered according to the
          mapping given, the resulting representation will be as well.  Taxa
          names in the tree must match up with the taxa names in the
          mapping.</p>")

(defxdoc mv-root-list
  :parents (taspi)
  :short "Returns the list of structurally unchanged unrooted trees now each with a
representation rooted at the node connecting the first taxon according to
the mapping given to the rest of the tree."
  :long "<p>Arguments: (1) list - a list of unrooted trees (2) tia - a mapping
   from each taxa name to an integer (3) ans - accumulator (initally nil)</p>

 <p>Details: Must be called on a list of unrooted trees in order to not change
          structure.  If each of the initial representations is ordered
          according to the mapping given, the resulting representations will be
          as well.  Taxa names in the trees must match up with the taxa names
          in the mapping.</p>")

(defxdoc mytips
  :parents (taspi)
  :short "Returns the taxa names from a tree."
  :long "<p>Arguments: (1) tree - a tree</p>

 <p>Details: Assumes branch lengths are not present and that no taxon has been
          assigned the name *nil*. See mytips-brlens.</p>")

(defxdoc mytips-brlens
  :parents (taspi)
  :short "Returns the taxa names from a tree with or without branch lengths."
  :long "<p>Arguments: (1) tree - a tree</p>

 <p>Details: Assumes that no taxon has been assigned the name *nil*.  See also
          mytips.</p>")

(defxdoc no-conflicts
  :parents (taspi)
  :short "Determines if bipartition x is consistent with each of those in list."
  :long "<p>Arguments: (1) x - a bipartition (2) list - a list of
  bipartitions</p>

 <p>Details: Set operations are used to determine if the bipartition x does not
          conflict with each of the bipartitions in list.  Bipartitions must be
          list based (as opposed to bdd-based) and the underlying taxa list
          must be preserved between x and each member of list.  The
          bipartitions are assumed to be ordered such that no bipartition x
          following y in list exists such that y is a subset of x and x=/y.
          See also q-no-conflicts (bdd based).</p>")

(defxdoc no-conflicts-list
  :parents (taspi)
  :short "Determines if the list of bipartitions x is consistent."
  :long "<p>Arguments: (1) list - a list of bipartitions</p>

 <p>Details: Set operations are used to determine if the list of bipartitions x
          do not conflict.  Bipartitions must be list based (as opposed to bdd
          based), and an underlying taxa list must be preserved between every
          pair of bipartitions in the list.  The bipartitions are assumed to be
          ordered such that no bipartition x following y in list exists such
          that y is a subset of x and x=/y.  See also q-no-conflicts-list (bdd
          based).</p>")

(defxdoc not-conflicting
  :parents (taspi)
  :short "Determines if the given tree does not conflict with any of the trees in the
set given."
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (2)
   taxa-list - a list of taxa names</p>

 <p>Details: Does not allow branch lengths (see also not-conflicting-brlens).
          Computation is only accurate if all trees are ordered according to
          the same taxa list, and the taxa names in each tree are exactly those
          given in the taxa list.</p>")

(defxdoc not-conflicting-brlens
  :parents (taspi)
  :short "Determines if the given tree does not conflict with any of the trees in the
set given."
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (2)
   taxa-list - a list of taxa names</p>

 <p>Details: Allows branch lengths (see also not-conflicting).  Branch lengths
          are not preserved in the trees returned.  Computation is only
          accurate if all trees are ordered according to the same taxa list,
          and the taxa names in each tree are exactly those given in the taxa
          list.</p>")

(defxdoc number-of-internal-nodes
  :parents (taspi)
  :short "Returns the number of internal nodes in the input tree."
  :long "<p>Arguments: (1) x - a tree

 Details: Assumes the tree representation is rooted at a node.  Does not handle
          branch lengths (see number-of-internal-nodes-brlens).</p>")

(defxdoc number-of-internal-nodes-brlens
  :parents (taspi)
  :short "Returns the number of internal nodes in the input tree."
  :long "<p>Arguments: (1) x - a tree

 Details: Assumes the tree representation is rooted at a node.  Allows branch
          lengths (see also number-of-internal-nodes).</p>")

(defxdoc number-of-p-informative-sites
  :parents (taspi)
  :short "Returns the number of sites that are parsimony informative"
  :long "<p>Arguments: (1) seqs - a set of sequences (2) missingGapChars - a
   list of characters indicating gaps or missing characters</p>

 <p>Details: Checks that sequences are valid before counting number of
          parsimony informative sites.</p>")

(defxdoc order-by-insertion
  :parents (taspi)
  :short "Returns the structurally unchanged input but with leaves ordered according
to the mapping given."
  :long "<p>Arguments: (1) x - a tree (2) taxon-index-alist - a mapping of taxa
    names to integers</p>

 <p>Details: The leaves in the tree must all be represented in the mapping
          given.  Ordering is achieved using an insertion sort algorithm.
          Consider also order-by-merge.</p>")

(defxdoc order-by-insertion-one-level
  :parents (taspi)
  :short "Returns the structurally unchanged input but with top-level subtrees
ordered according to the mapping given."
  :long "<p>Arguments: (1) x - a tree (3) taxon-index-alist - a mapping of taxa
    names to integers</p>

 <p>Details: The leaves in the tree must all be represented in the mapping
          given.  Ordering is achieved using an insertion sort algorithm.  The
          tree produced will only be fully ordered if each of the top-level
          trees are intially ordered.  Consider also
          order-by-merge-one-level.</p>")

(defxdoc order-by-merge
  :parents (taspi)
  :short "Returns the structurally unchanged input but with leaves ordered according
to the mapping given."
  :long "<p>Arguments: (1) x - a tree (2) taxon-index-alist - a mapping of taxa
    names to integers</p>

 <p>Details: The leaves in the tree must all be represented in the mapping
          given.  Ordering is achieved using a merge sort algorithm.  Consider
          also order-by-insertion.</p>")

(defxdoc order-by-merge-one-level
  :parents (taspi)
  :short "Returns the structurally unchanged input but with top-level subtrees
ordered according to the mapping given."
  :long "<p>Arguments: (1) x - a tree (3) taxon-index-alist - a mapping of taxa
    names to integers</p>

 <p>Details: The leaves in the tree must all be represented in the mapping
          given.  Ordering is achieved using a merge sort algorithm.  The tree
          produced will only be fully ordered if each of the top-level trees
          are intially ordered.  Consider also
          order-by-insertion-one-level.</p>")

(defxdoc order-each-by-insertion
  :parents (taspi)
  :short "Returns a list where each of the trees in the input list has been
structurally unchanged but now has leaves ordered according
to the mapping given."
  :long "<p>Arguments: (1) input-trees - a list of trees (2) taxon-index-alist
    - a mapping of taxa names to integers (3) length-taxon-index-alist - a
    number larger than any value in the mapping</p>

 <p>Details: The leaves in each of the trees must all be represented in the
          mapping given.  Ordering is achieved using an insertion sort
          algorithm. Consider also order-each-by-merge.</p>")

(defxdoc order-each-by-merge
  :parents (taspi)
  :short "Returns a list where each of the trees in the input list has been
structurally unchanged but now has leaves ordered according
to the mapping given."
  :long "<p>Arguments: (1) input-trees - a list of trees (2) taxon-index-alist
    - a mapping of taxa names to integers (3) length-taxon-index-alist - a
    number larger than any value in the mapping</p>

 <p>Details: The leaves in each of the trees must all be represented in the
          mapping given.  Ordering is achieved using a merge sort
          algorithm. Consider also order-each-by-insertion.</p>")

(defxdoc orderedp
  :parents (taspi)
  :short "Determines if the tree given is ordered according to the order given."
  :long "<p>Arguments: (1) flg - nil indicates a set of trees, non-nil
    indicates a single tree (2) x - a tree (3) order - a mapping from taxa
    names to integers</p>

 <p>Details: Taxa names in order must match those in the tree.  Branch lengths
          may or may not be present.</p>")

(defxdoc orderly-spr
  :parents (taspi)
  :short "Returns the spr (subtree prune regraft) neighbors of the input tree"
  :long "<p>Arguments: (1) x - a tree (2) tia - a mapping of taxa names to
  integers</p>

 <p>Details: The tree should have the taxa names in the tia.  The tree should
          be unrooted. NB: Does not handle branch lengths.</p>")

(defxdoc path-distance-brlens
  :parents (taspi)
  :short "Returns path distance between a and b in tree."
  :long "<p>Arguments: (1) a - a taxon name (2) b - a taxon name (3) tree - a
   tree with branch lengths

 Details: Requires tree representation to be rooted at a node.</p>")

(defxdoc path-distance-no-brlens
  :parents (taspi)
  :short "Returns path distance between a and b in tree assuming unit branch lengths."
  :long "<p>Arguments: (1) a - a taxon name (2) b - a taxon name (3) tree - a
  tree

 Details: Requires tree representation to be rooted at a node.</p>")

(defxdoc phylo-tbr
  :parents (taspi)
  :short "Returns the tbr (tree bisect reconnect) neighbors of the input tree"
  :long "<p>Arguments: (1) x - a tree (2) tia - a mapping of taxa names to
  integers</p>

 <p>Details: The tree should have the taxa names in the tia.  The tree should
          be unrooted.  Does not handle branch lengths.</p>")

(defxdoc project
  :parents (taspi)
  :short "Returns the tree on taxa in keep implied by x."
  :long "<p>Arguments: (1) flg - non-nil for a single tree, nil for a set of
   trees (2) keep - a list of taxa names (2) x - a tree

 Details: Does not matter if branch lengths are present or not, but resulting
          trees will not have branch lengths.</p>")

(defxdoc project-with-normalize
  :parents (taspi)
  :short "Returns the normalized tree on taxa in keep implied by x."
  :long "<p>Arguments: (1) rooted? - non-nil for a rooted tree, nil for an
   unrooted tree (2) keep - a list of taxa names (3) tree - a tree (4)
   taxa-list - a list of taxa names

 Details: Assumes tree does not have branch lengths.  Resulting tree will be
          ordered according to the taxa list given, and if the tree is
          unrooted, its representation will be rooted at the node at which the
          least taxon is connected to the rest of the tree.</p>")

(defxdoc proper-subtreep
  :parents (taspi)
  :short "Determines if the first argument is a proper subtree of the second."
  :long "<p>Arguments: (1) a - a tree (2) b - a tree</p>

 <p>Details: Requires both arguments to be ordered according to the same
         taxa-list.  Not a traditional form of subtree in that it does not take
         into account unrootedness. See u-proper-subtreep.</p>")

(defxdoc proportion-of-trees-supporting-branch
  :parents (taspi)
  :short "Returns proportion of trees from input set that support the input branch"
  :long "<p>Arguments: (1) branch - a bdd based bipartition (2) set - a list of
  trees
   (3) taxa-list - a list of taxa names</p>

 <p>Details: The branch must have been created using the same taxa list as
          given, and the trees must also have this same taxa list.  Does not
          allow branch lengths (see
          proportion-of-trees-supporting-branch-brlens).</p>")

(defxdoc proportion-of-trees-supporting-branch-brlens
  :parents (taspi)
  :short "Returns proportion of trees from input set with branch lengths
that support the input branch"
  :long "<p>Arguments: (1) branch - a bdd based bipartition (2) set - a list of
  trees
   (3) taxa-list - a list of taxa names</p>

 <p>Details: The branch must have been created using the same taxa list as
          given, and the trees must also have this same taxa list.  Allow
          branch lengths (see also
          proportion-of-trees-supporting-branch).</p>")

(defxdoc pscore-tree
  :parents (taspi)
  :short "Scores a tree under parsimony"
  :long "<p>Arguments: (1) tree - a single phylogenetic tree (2) sequences - a
   mapping of taxa to sequences (3) cssl-map - An alist mapping every character
   state, including ambiguous ones, to a list containing one element (either 0
   or nil for infinity) for each unambiguous state.  (4) matrix - A mapping of
   unambiguous character states to transition costs.

 Details: Does not handle branch lengths.</p>")

(defxdoc pscore-trees
  :parents (taspi)
  :short "Scores a list of trees under parsimony"
  :long "<p>Arguments: (1) trees - a list of phylogenetic trees (2) sequences -
    a mapping of taxa to sequences (3) cssl-map - An alist mapping every
    character state to a list containing one element (either 0 or nil for
    infinity) for each unambiguous state (4) matrix - A mapping of unambiguous
    character states to transition costs.</p>

 <p>Details: Does not handle branch lengths.</p>")

(defxdoc q-no-conflicts
  :parents (taspi)
  :short "Determines if bipartition x is consistent with each of those in list."
  :long "<p>Arguments: (1) x - a bipartition (2) list - a list of
  bipartitions</p>

 <p>Details: Set operations are used to determine if the bipartition x does not
          conflict with each of the bipartitions in list.  Bipartitions must be
          bdd based (as opposed to list based) and the underlying taxa list
          must be preserved between x and each member of list.  The
          bipartitions are assumed to be ordered such that no bipartition x
          following y in list exists such that y is a subset of x and x=/y.
          See also no-conflicts (list based).</p>")

(defxdoc q-no-conflicts-gen
  :parents (taspi)
  :short "Determines if bipartition x is consistent with each of those in list."
  :long "<p>Arguments: (1) x - a bipartition (2) list - a list of
  bipartitions</p>

 <p>Details: Set operations are used to determine if the bipartition x does not
          conflict with each of the bipartitions in list.  Bipartitions must be
          bdd based (as opposed to list based) and the underlying taxa list
          must be preserved between x and each member of list.  Assumes no
          ordering of bipartitions in list.  See also q-no-conflicts.</p>")

(defxdoc q-no-conflicts-list
  :parents (taspi)
  :short "Determines if the list of bipartitions list is consistent."
  :long "<p>Arguments: (1) list - a list of bipartitions</p>

 <p>Details: Set operations are used to determine if the list of bipartitions
          do not conflict.  Bipartitions must be list based (as opposed to bdd
          based), and an underlying taxa list must be preserved between every
          pair of bipartitions in the list. The bipartitions are assumed to be
          ordered such that no bipartition x following y in list exists such
          that y is a subset of x and x=/y.  See also no-conflicts-list (list
          based) and q-no-conflicts-list-gen.</p>")

(defxdoc q-no-conflicts-list-gen
  :parents (taspi)
  :short "Determines if the list of bipartitions list is consistent."
  :long "<p>Arguments: (1) list - a list of bipartitions</p>

 <p>Details: Set operations are used to determine if the list of bipartitions
          do not conflict.  Bipartitions must be list based (as opposed to bdd
          based), and an underlying taxa list must be preserved between every
          pair of bipartitions in the list. No ordering on the bipartitions is
          assumed.  See also q-no-conflicts-list.</p>")

(defxdoc remove-brlens
  :parents (taspi)
  :short "Returns the structurally unchanged tree now with no branch lengths."
  :long "<p>Arguments: (1) a - a tree</p>

 <p>Details: If no branch lengths are initially present, no change results.
          Not all branches are required to have a length.</p>")

(defxdoc remove-brlens-list
  :parents (taspi)
  :short "Returns the structurally unchanged list of trees now with no branch lengths."
  :long "<p>Arguments: (1) a - a list of trees</p>

 <p>Details: If no branch lengths are initially present, no change results.
          List can contain trees both with and without brlens.</p>")

(defxdoc replete-trees-list-brlens
  :parents (taspi)
  :short "Returns a replete mapping of trees and subtrees in the input list to either
the number of times the tree occurs or to a list of each subtrees immediate
parents."
  :long "<p>Arguments: (1) l - a list of trees no member of which is a proper
    subtree of another</p>

 <p>Details: The trees should all be ordered according to the same taxa list.
          Branch lengths are allowed, but not preserved (see
          replete-trees-list-top).</p>")

(defxdoc replete-trees-list-top
  :parents (taspi)
  :short "Returns a replete mapping of trees and subtrees in the input list to either
the number of times the tree occurs or to a list of each subtrees immediate
parents."
  :long "<p>Arguments: (1) l - a list of trees no member of which is a proper
    subtree of another</p>

 <p>Details: The trees should all be ordered according to the same taxa list.
          Branch lengths are not allowed (see replete-trees-list-brlens).</p>")

(defxdoc rf
  :parents (taspi)
  :short "Returns the RF rate, false negative rate and false positive rate between the
two trees input."
  :long "<p>Arguments: (1) tree1 - a tree (2) taxa-list1 - a list of taxa
   names (3) rooted1 - a flag indicating rootedness (4) tree2 - a tree (5)
   taxa-list2 - a list of taxa names (6) rooted2 - a flag indicating
   rootedness</p>

 <p>Details: Trees input should not have branch lengths (see rf-brlens).</p>")

(defxdoc rf-brlens
  :parents (taspi)
  :short "Returns the RF rate, false negative rate and false positive rate between the
two trees input."
  :long "<p>Arguments: (1) tree1 - a tree (2) taxa-list1 - a list of taxa
   names (3) rooted1 - a flag indicating rootedness (4) tree2 - a tree (5)
   taxa-list2 - a list of taxa names (6) rooted2 - a flag indicating
   rootedness</p>

 <p>Details: Trees input may have branch lengths (see rf).</p>")

(defxdoc root-to-monophyletic?
  :parents (taspi)
  :short "Determines if it is possible to root tree such that taxa is monophyletic
in tree."
  :long "<p>Arguments: (1) taxa - a list of taxa names (2) tree - an unrooted
  tree

 Details: Assumes an unrooted tree with no branch lengths (see also
          root-to-monophyletic?-brlens). Does not return monophyletic structure
          if present.</p>")

(defxdoc root-to-monophyletic?-brlens
  :parents (taspi)
  :short "Determines if it is possible to root tree such that taxa is monophyletic
in tree."
  :long "<p>Arguments: (1) taxa - a list of taxa names (2) tree - an unrooted
  tree

 Details: Assumes an unrooted tree.  Does not preserve structure (see also
          root-to-monophyletic?).</p>")

(defxdoc sort-bdd-fringes
  :parents (taspi)
  :short "Returns the given list of bdd based bipartitions sorted by length of implied
list based bipartitions."
  :long "<p>Arguments: (1) bdd-fringes - a list of bdd based bipartitions (2)
    full-taxa-list-tree - a binary tree based version of the taxa list (3)
    taxon-index-alist - a mapping of taxa names to integers</p>

 <p>Details: Depth of each of the bdd based bipartitions must be less than that
         of the full-taxa-list-tree.  The taxa names in the full-taxa-list-tree
         must match those present as keys in the taxon-index-alist.</p>")

(defxdoc spr-search
  :parents (taspi)
  :short "Searches for the maximum parsimony trees using spr rearrangements."
  :long "<p>Arguments: (1) seqs - a set of sequences (2) num-rearrangements - a
   limit to the number of rearrangements to try (3) cssl-map - An alist mapping
   every character state to a list containing one element (either 0 or nil for
   infinity) for each unambiguous state (4) matrix - A mapping of unambiguous
   character states to transition costs.</p>

 <p>Details: Builds a few starting trees, starts from best of these and keeps
          best trees found at each iteration to search from next.</p>")

(defxdoc subtreep
  :parents (taspi)
  :short "Determines if the first argument is a subtree of the second."
  :long "<p>Arguments: (1) a - a tree (2) b - a tree</p>

 <p>Details: Requires both arguments to be ordered according to the same
         taxa-list.  Not a traditional form of subtree in that it does not take
         into account unrootedness. See u-subtreep.</p>")

(defxdoc subtrees-implying
  :parents (taspi)
  :short "Returns bipartitions that refine a tree *below* the branch given."
  :long "<p>Arguments: (1) branch - a bdd based bipartition (2) l - a list of
    bdd based bipartitions</p>

 <p>Details: All bipartitions must be based on the same taxa list.  *Below* is
 defined in terms of the rooting given by taxa list.</p>")

(defxdoc subtrees-not-implying
  :parents (taspi)
  :short "Returns bipartitions that are not *below* the branch given."
  :long "<p>Arguments: (1) branch - a bdd based bipartition (2) l - a list of
    bdd based bipartitions</p>

 <p>Details: All bipartitions must be based on the same taxa list.  *Below* is
 defined in terms of the rooting given by taxa list.</p>")

(defxdoc symm-diff
  :parents (taspi)
  :short "Returns the symmetric difference, number of false negatives and number of
false positives between the two trees input."
  :long "<p>Arguments: (1) tree1 - a tree (2) taxa-list1 - a list of taxa
   names (3) rooted1 - a flag indicating rootedness (4) tree2 - a tree (5)
   taxa-list2 - a list of taxa names (6) rooted2 - a flag indicating
   rootedness</p>

 <p>Details: Trees input should not have branch lengths (see
 symm-diff-brlens).</p>")

(defxdoc symm-diff-brlens
  :parents (taspi)
  :short "Returns the symmetric difference, number of false negatives and number of
false positives between the two trees input."
  :long "<p>Arguments: (1) tree1 - a tree (2) taxa-list1 - a list of taxa
   names (3) rooted1 - a flag indicating rootedness (4) tree2 - a tree (5)
   taxa-list2 - a list of taxa names (6) rooted2 - a flag indicating
   rootedness</p>

 <p>Details: Trees input may have branch lengths (see also symm-diff).</p>")

(defxdoc taspi
  :parents (taspi)
  :short "Documentation for TASPI."
  :long "<p>Tree Analysis System for Phylogenetic Inquiry</p>

 <p>A suite a functions for working with trees.</p>")

(defxdoc taspip
  :parents (taspi)
  :short "Recognizes well formed trees with no branch lengths
while allowing singletons."
  :long "<p>Arguments: (1) flg - nil indicating a set of trees, non-nil
    indicating a single tree (2) x - a potential tree</p>

 <p>Details: Well formed tips are defined as in tip-p, branch lengths are not
          permitted but singletons are allowed (see taspip-brlens).</p>")

(defxdoc taxa-list-to-index-taxon
  :parents (taspi)
  :short "Creates a mapping of unique integers to members of taxa-list."
  :long "<p>Arguments: (1) taxa-list - a list of taxa names</p>")

(defxdoc taxa-list-to-taxon-index
  :parents (taspi)
  :short "Creates a mapping from each member of taxa-list to a unique integer."
  :long "<p>Arguments: (1) taxa-list - a list of taxa names</p>")

(defxdoc tbr-search
  :parents (taspi)
  :short "Searches for the maximum parsimony trees using tbr rearrangements."
  :long "<p>Arguments: (1) seqs - a set of sequences (2) num-rearrangements - a
   limit to the number of rearrangements to try (3) cssl-map - An alist mapping
   every character state to a list containing one element (either 0 or nil for
   infinity) for each unambiguous state (4) matrix - A mapping of unambiguous
   character states to transition costs.</p>

 <p>Details: Builds a few starting trees, starts from best of these and keeps
          best trees found at each iteration to search from next.</p>")

(defxdoc term-to-bfringes
  :parents (taspi)
  :short "Returns the bdd based list of bipartitions for the input tree."
  :long "<p>Arguments: (1) term - a tree (2) taxa-list - a list of taxa</p>

 <p>Details: Taxa names in the given tree must be a subset of those present in
          the taxa-list given.  Tree input should not have branch
          lengths.</p>")

(defxdoc term-to-bfringes-brlens
  :parents (taspi)
  :short "Returns the bdd based list of bipartitions for the input tree."
  :long "<p>Arguments: (1) term - a tree (2) taxa-list - a list of taxa</p>

 <p>Details: Taxa names in the given tree must be a subset of those present in
          the taxa-list given.  Tree input may have branch lengths.</p>")

(defxdoc tip-p
  :parents (taspi)
  :short "Recognizes whether or not input is a valid taxa name."
  :long "<p>Arguments: (1) x - a possible taxa name</p>

 <p>Details: Does not allow branch lengths (see tip-p-brlen).</p>")

(defxdoc tip-p-brlen
  :parents (taspi)
  :short "Recognizes whether or not input is a valid leaf."
  :long "<p>Arguments: (1) x - a possible leaf</p>

 <p>Details: Does allow branch lengths (see also tip-p).</p>")

(defxdoc tip-p-num-brlen
  :parents (taspi)
  :short "Recognizes whether or not input is a leaf with a numeric branch length."
  :long "<p>Arguments: (1) x - a possible leaf</p>

 <p>Details: Requires a branch length in order to return true.  See also
 tip-p.</p>")

(defxdoc tree-compatibility
  :parents (taspi)
  :short "Determines if a set of trees is compatible"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: Does not allow branch lengths (see tree-compatibility-brlens).
          Does a pairwise check of compatibility between all bipartitions in
          the given list of trees. NOTE: Guards are not yet verified.</p>")

(defxdoc tree-compatibility-brlens
  :parents (taspi)
  :short "Determines if a set of trees with branch lengths is compatible"
  :long "<p>Arguments: (1) list-of-trees - a list of trees (2) taxa-list - a
   list of taxa names</p>

 <p>Details: Allows branch lengths (see also tree-compatibility).  Does a
          pairwise check of compatibility between all bipartitions in the given
          list of trees. NOTE: Guards are not yet verified.</p>")

(defxdoc tree-depth
  :parents (taspi)
  :short "Returns the depth of the input tree representation."
  :long "<p>Arguments: (1) x - a tree

 Details: Does not handle branch lengths.  See tree-depth-brlens.</p>")

(defxdoc tree-depth-brlens
  :parents (taspi)
  :short "Returns the depth of the input tree representation."
  :long "<p>Arguments: (1) x - a tree

 Details: Allows branch lengths.  See also tree-depth.</p>")

(defxdoc tree-listp
  :parents (taspi)
  :short "Recognizes a list of well formed trees with no branch lengths
and no singletons."
  :long "<p>Arguments: (1) list - a list of potential trees</p>

 <p>Details: Well formed tips are defined as in tip-p, branch lengths are not
          permitted (see tree-listp-brlens).</p>")

(defxdoc tree-listp-brlens
  :parents (taspi)
  :short "Recognizes a list of well formed trees with no singletons."
  :long "<p>Arguments: (1) list - a list of potential trees</p>

 <p>Details: Well formed tips are defined as in tip-p, branch lengths are
          permitted (see also tree-listp).</p>")

(defxdoc tree-listp-num-brlens
  :parents (taspi)
  :short "Recognizes a list of well formed trees with numeric branch lengths
and no singletons."
  :long "<p>Arguments: (1) list - a list of potential trees</p>

 <p>Details: Well formed tips are defined as in tip-p-num-brlen.  See also
          tree-listp.</p>")

(defxdoc tree-matches-sequences
  :parents (taspi)
  :short "Determines if a tree is made up of taxa for which sequences are available"
  :long "<p>Arguments: (1) flg - non-nil for a single tree, nil for a set of
    trees (2) x - a tree (3) sequences - a set of sequences</p>

 <p>Details: Does not care if x is a valid tree, but sequences must be
          well-formed.</p>")

(defxdoc treep
  :parents (taspi)
  :short "Recognizes well formed trees with no branch lengths and no singletons."
  :long "<p>Arguments: (1) x - a potential tree</p>

 <p>Details: Well formed tips are defined as in tip-p, branch lengths are not
          permitted (see treep-brlens).</p>")

(defxdoc treep-brlens
  :parents (taspi)
  :short "Recognizes well formed trees with no singletons."
  :long "<p>Arguments: (1) x - a potential tree</p>

 <p>Details: Well formed tips are defined as in tip-p, branch lengths are
          permitted (see also treep).</p>")

(defxdoc treep-num-brlens
  :parents (taspi)
  :short "Recognizes well formed trees with numeric branch lengths
and no singletons."
  :long "<p>Arguments: (1) x - a potential tree</p>

 <p>Details: Well formed tips are defined as in tip-p-num-brlen.  See also
          treep.</p>")

(defxdoc trees-supporting-all-branches
  :parents (taspi)
  :short "Returns trees from input set that support all branches in input tree"
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (2)
   taxa-list - a list of taxa names

 Details: Does not allow branch lengths
          (see trees-supporting-all-branches-brlens).  Trees returned may be
          more resolved than the input tree, but not less.</p>")

(defxdoc trees-supporting-all-branches-brlens
  :parents (taspi)
  :short "Returns trees from input set that support all branches in input tree
while allowing branch lengths"
  :long "<p>Arguments: (1) tree - a tree (2) set - a list of trees (2)
   taxa-list - a list of taxa names

 Details: Allows branch lengths (see trees-supporting-all-branches).  Trees
          returned may be more resolved than the input tree, but not less.
          Branch lengths are not preserved in trees returned.</p>")

(defxdoc trees-supporting-x-proportion-of-branches-in-tree
  :parents (taspi)
  :short "Returns trees from input set that support x proportion of branches in input tree"
  :long "<p>Arguments: (1) x - a rational number indicating support level (2)
   tree - a tree (3) set - a list of trees (4) taxa-list - a list of taxa
   names</p>

 <p>Details: Does not allow branch lengths (see
          trees-supporting-x-proportion-of-branches-in-tree-brlens).  All trees
          involved should have the taxa list given.</p>")

(defxdoc trees-supporting-x-proportion-of-branches-in-tree-brlens
  :parents (taspi)
  :short "Returns trees from input set that support x proportion of branches in input
tree while allowing branch lengths"
  :long "<p>Arguments: (1) x - a rational number indicating support level (2)
   tree - a tree (3) set - a list of trees (4) taxa-list - a list of taxa
   names</p>

 <p>Details: Does not allow branch lengths (see
          trees-supporting-x-proportion-of-branches-in-tree-brlens).  All trees
          involved should have the taxa list given. Trees returned do not
          preserve branch lengths.</p>")

(defxdoc valid-sequences
  :parents (taspi)
  :short "Recognizes a set of sequences as structurally well-formed"
  :long "<p>Arguments: (1) x - a set of potential sequences</p>")

(defxdoc valid-sequences-same-length
  :parents (taspi)
  :short "Recognizes a set of sequences as structurally well-formed and of equal length"
  :long "<p>Arguments: (1) x - a set of potential sequences</p>")
