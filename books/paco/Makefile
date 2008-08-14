# How To Rebuild Paco

# make tags   - rebuild the tags table

# make        - rebuild the entire system

# make clean  - delete all .cert, .o, .out, etc files

# General Strategy of the Paco Makefile

# To grasp how this process is structured, consider two successive
# files in the source sequence, e.g., utilities and foundations,
# or type-set and rewrite.  Let x1 be the earlier file and x2 be
# its successor file.  Then corresponding to x2.lisp is x2.acl2
# containing three lines:

#  (ld "acl2-customization.lisp") ; adds the :paco keyword command
#  (set-verify-guards-eagerness 0)
#  (include-book "x1")
#  (certify-book "x2" 2)

# So that to certify x2 we include x1 in the portculis.  That brings in
# all the previous files and the definition of the the "PACO" package.
# The first file, "utilities" has a slightly different .acl2 file,
# namely,

#  (ld "acl2-customization.lisp") ; adds the :paco keyword command
#  (defpkg "PACO" ...)
#  (set-verify-guards-eagerness 0)
#  (certify-book "utilities" 3)

include ../Makefile-generic


# BOOKS_LISP = (patsubst %, %.lisp, $(BOOKS))

tags:
	 etags $(BOOKS_LISP)

-include Makefile-deps
