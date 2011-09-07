# Makefile for certifying workshop/2011 books.

##############################

# Supporting materials included for:

# John Cowles and Ruben Gamboa
# Verifying Sierpinski and Riesel Numbers in ACL2

# Peter Reid and Ruben Gamboa
# Implementing an Automatic Differentiator in ACL2
# [Note: ACL2(r) only; see README file.]

# Sol Swords and Jared Davis
# Bit-Blasting ACL2 Theorems
# [Note: No certifiable book is there.]

# Freek Verbeek and Julien Schmaltz
# Formal verification of a deadlock detection algorithm

##############################

DIRS =  cowles-gamboa-sierpinski/support \
	verbeek-schmaltz/sources

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
