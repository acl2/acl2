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

BOOKS = utilities \
        output-module \
        foundations \
        type-set \
        rewrite \
        simplify \
        elim-dest \
        induct \
        prove \
        database \
        paco

BOOKS_LISP = (patsubst %, %.lisp, $(BOOKS))

tags:
	 etags ${BOOKS_LISP}

# Put dependencies (from `make -s dependencies, or other sources) below

utilities.cert: utilities.lisp
# utilities.cert: $(ACL2_SYSTEM_BOOKS)/ihs/ihs-lemmas.cert
utilities.cert: utilities.acl2

output-module.cert: output-module.lisp
output-module.cert: output-module.acl2
output-module.cert: utilities.cert

foundations.cert: foundations.lisp
foundations.cert: foundations.acl2
foundations.cert: output-module.cert

type-set.cert: type-set.lisp
# type-set.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert
# type-set.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
type-set.cert: type-set.acl2
type-set.cert: foundations.cert

rewrite.cert: rewrite.lisp
rewrite.cert: rewrite.acl2
rewrite.cert: type-set.cert

simplify.cert: simplify.lisp
simplify.cert: simplify.acl2
simplify.cert: rewrite.cert

elim-dest.cert: elim-dest.lisp
elim-dest.cert: elim-dest.acl2
elim-dest.cert: simplify.cert

induct.cert: induct.lisp
induct.cert: induct.acl2
induct.cert: elim-dest.cert

prove.cert: prove.lisp
prove.cert: prove.acl2
prove.cert: induct.cert

database.cert: database.lisp
database.cert: database.acl2
database.cert: prove.cert

paco.cert: paco.lisp
paco.cert: utilities.cert
paco.cert: foundations.cert
paco.cert: type-set.cert
paco.cert: rewrite.cert
paco.cert: simplify.cert
paco.cert: induct.cert
paco.cert: prove.cert
paco.cert: database.cert
paco.cert: paco.acl2
paco.cert: database.cert
