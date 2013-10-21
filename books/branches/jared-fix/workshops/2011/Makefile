# Makefile for certifying workshop/2011 books.

##############################

### Supporting materials included for:

# John Cowles and Ruben Gamboa
# Verifying Sierpinski and Riesel Numbers in ACL2

# Mike Dahlin, Ryan Johnson, Robert Krug, Michael Mccoyd and Bill
# Young.
# Toward the Verification of a Simple Hypervisor
# NOTE that `make' will skip certification of
# MinVisor/setup-nested-page-tables.lisp, which took over an hour and 38
# minutes on an "Intel(R) Xeon(R) CPU E31280 @ 3.50GHz", a very fast
# machine as of November, 2011.

# Peter Reid and Ruben Gamboa
# Implementing an Automatic Differentiator in ACL2
# [Note: ACL2(r) only; see README file.]

# Sol Swords and Jared Davis
# Bit-Blasting ACL2 Theorems
# [Note: No certifiable book is there.]

# Freek Verbeek and Julien Schmaltz
# Formal verification of a deadlock detection algorithm

### Not contributing supporting materials:

# Matt Kaufmann and J Moore. 
# How Can I Do That with ACL2?  Recent Enhancements to ACL2

# Harsh Raju Chamarthi, Peter C. Dillinger, Matt Kaufmann and
# Panagiotis Manolios.
# Integrating Testing and Interactive Theorem Proving

# Peter-Michael Seidel. 
# Formal Verification of an Iterative Low-Power X86 Floating-Point
# Multiplier with Redundant Feedback

##############################

DIRS =  cowles-gamboa-sierpinski/support \
	krug-et-al/support \
	verbeek-schmaltz/sources

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
