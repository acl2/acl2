# Makefile for certifying workshop/2006 books.

##############################

# Supporting materials for books already distributed (confirmed by Jared):

# Jared Davis.
# Memories: Array-like Records for ACL2.
# See: books/data-structures/memories/

# Jared Davis.
# Reasoning about ACL2 File Input.
# See: books/unicode/

##############################

# Supporting materials that authors have said will be forthcoming:

# Ruben Gamboa and John Cowles.
# Implementing a Cost-Aware Evaluator for ACL2 Expressions.

##############################

# There are no supporting materials for the following contributions.

# David Hardin, Eric Smith, and William Young.
# A Robust Machine Code Proof Framework for Highly Secure Applications.

# Erik Reeber and Jun Sawada.
# Combining ACL2 and an Automated Verification Tool to Verify a Multiplier.

# Robert S. Boyer and Warren A. Hunt, Jr.
# Function Memoization and Unique Object Representation for ACL2 Functions.

# Warren A. Hunt, Jr. and Serita M. Nelesen.
# Phylogenetic Trees in ACL2.

# Dale Vaillancourt, Rex Page, and Matthias Felleisen.
# ACL2 in DrScheme.

##############################

# Note: rager/support/ uses parallelism constructs

##############################

DIRS =  cowles-gamboa-euclid/Euclid/fld-u-poly \
	cowles-gamboa-euclid/Euclid \
	gordon-hunt-kaufmann-reynolds/support \
	greve/nary \
	hunt-reeber/support \
	kaufmann-moore/support \
	pike-shields-matthews/core_verifier \
	rager/support \
	ray/tail \
	schmaltz-borrione/GeNoC-support \
	swords-cook/lcsoundness

include ../../Makefile-psubdirs

# Because cowles-gamboa-euclid/Euclid/ed6a.cert depends on
# cowles-gamboa-euclid/Euclid/fld-u-poly/fuquot-rem.cert, we add this dependency:
cowles-gamboa-euclid/Euclid: cowles-gamboa-euclid/Euclid/fld-u-poly

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
