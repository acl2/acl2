# Makefile for certifying workshop/2009 books.

##############################

# Supporting materials included for:

# John Cowles and Ruben Gamboa
# \triangle = \square

# Hanbing Liu
# Proving A Specific Type Of Inequality Theorems in ACL2: a bind-free experience report

# Matt Kaufmann, Jacob Kornerup, Mark Reitblatt
# Formal Verification of LabVIEW Programs Using the ACL2 Theorem Prover
# kaufmann-kornerup-reitblatt/

# Laurence Pierre, Renauld Clavel, and Regis Leveugle
# ACL2 for the Verification of Fault-Tolerance Properties: First Results  

# Fares Fraij and Steve Roach
# Proof of Transitive Closure Property of Directed Acyclic Graphs

# Rob Sumners
# User Control and Direction of a More Efficient Simplifier in ACL2

# Tom van der Broek and Julien Schmaltz
# A Generic Implementation Model for the Formal Verification of Networks-on-Chips
# vandenbroek-schmaltz/

# Freek Verbeek and Julien Schmaltz
# Formal Validation of Deadlock Prevention in Networks-on-Chips
# verbeek-schmaltz/

##############################

# Supporting materials not yet received:

# Robert Boyer and Warren Hunt
# Symbolic Simulation in ACL2

# Ryan Ralston
# ACL2-Certified AVL Trees

# David Hardin and Samuel Hardin
# Efficient, Formally Verifiable Data Structures using ACL2
#   Single-Threaded Objects for High-Assurance Systems

# David Greve
# Automated Reasoning With Quantified Formulae

# David Greve
# Assuming Termination

##############################

# Supporting materials are elsewhere (see README files):

# J Moore
# Automatically Computing Functional Instantiations

# Ruben Gamboa and John Cowles
# Inverse Functions in ACL2(r)

# David Rager
# An Executable Model for Security Protocol JFKr

##############################

# There are no supporting materials for the following contributions.

# Antonio Garcia-Dominguez, Francisco Palomo-Lozano and Inmaculada Medina-Bulo
# Hypertext Navigation of ACL2 Proofs with XMLEye

# Matt Kaufmann
# Abbreviated Output for Input in ACL2

# Carl Eastland and Matthias Felleisen
# Automatically Verified GUI Programs
# [part of Dracula]

# Carl Eastland 
# DoubleCheck Your Theorems
# [part of Dracula]

# Rex Page
# Computational Logic in the Undergraduate Curriculum

##############################

DIRS =  cowles-gamboa-triangle-square/triangle=square-materials \
	fraij-roach/support \
	kaufmann-kornerup-reitblatt/support \
	liu/support \
	pierre-clavel-leveugle/Fault-tolerance \
	sumners/support \
	vandenbroek-schmaltz/GeNieroC \
	verbeek-schmaltz/verbeek

include ../../Makefile-psubdirs

tar: clean
	@for dir in $(DIRS) ; \
	do \
	tar cvf $$dir.tar $$dir ; \
	done
