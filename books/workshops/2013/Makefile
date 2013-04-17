# Makefile for certifying workshop/2013 books

##############################

########## Supporting materials included for: ##########

# Shilpi Goel, Warren Hunt and Matt Kaufmann
# Abstract Stobjs and Their Application to ISA Modeling

########## Waiting for possible supporting materials: ##########

# Bernard van Gastel and Julien Schmaltz
# A formalisation of xMAS

# Freek Verbeek and Julien Schmaltz
# Verification of Building Blocks for Asynchronous Circuits

# Sebastiaan Joosten, Bernard van Gastel and Julien Schmaltz
# A Macro for Reusing Abstract Functions and Theorems

# Konrad Slind and David Greve
# A Step-Indexing Approach to Partial Functions

# Lucas Helms and Ruben Gamboa
# An Interpreter for Quantum Circuits

# David Hardin and Samuel Hardin
# ACL2 Meets the GPU: Formalizing a CUDA-based Parallelizable
# All-Pairs Shortest Path Algorithm in ACL2

# Jared Davis and Sol Swords
# Verified AIG Algorithms in ACL2

# Jared Davis
# Embedding ACL2 Models in End-User Applications

# Caleb Eggensperger
# Proof Pad: A Modern Development Environment for ACL2

########## Not contributing supporting materials: ##########

# Matt Kaufmann and J Moore
# Enhancements to ACL2 in Versions 5.0, 6.0, and 6.1

##############################

DIRS =  goel-hunt-kaufmann/support \

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
