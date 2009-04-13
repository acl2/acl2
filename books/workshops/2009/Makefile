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

# J Moore
# Automatically Computing Functional Instantiations

# Robert Boyer and Warren Hunt
# Symbolic Simulation in ACL2

# Rex Page
# Computational Logic in the Undergraduate Curriculum

# Carl Eastland and Matthias Felleisen
# Automatically Verified GUI Programs

# Carl Eastland 
# DoubleCheck Your Theorems

# Ryan Ralston
# ACL2-Certified AVL Trees

# Fares Fares and Steve Roach
# Proof of Transitive Closure Property of Directed Acyclic Graphs

# David Hardin and Samuel Hardin
# Efficient, Formally Verifiable Data Structures using ACL2
#   Single-Threaded Objects for High-Assurance Systems

# David Rager
# An Executable Model for Security Protocol JFKr

# David Greve
# Automated Reasoning With Quantified Formulae

# David Greve
# Assuming Termination

##############################

# Supporting materials for books already distributed:

# None at this point.

##############################

# Supporting materials not yet certifiable:

# None at this point.

##############################

# Supporting materials that are not meant for ACL2 processing.

# None at this point.

##############################

# There are no supporting materials for the following contributions.

# Antonio Garcia-Dominguez, Francisco Palomo-Lozano and Inmaculada Medina-Bulo
# Hypertext Navigation of ACL2 Proofs with XMLEye

# Matt Kaufmann
# Abbreviated Output for Input in ACL2

# Ruben Gamboa and John Cowles
# Inverse Functions in ACL2(r)
# [See README in directory gamboa-cowles-inverses/.]

##############################

DIRS =  cowles-gamboa-triangle-square \
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
