# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# These books are obtained from certify.lisp.  The file bis.lisp is a
# bisimulation book that was provided by Rob Sumners and is referenced in the
# paper.
BOOKS = total-order apply-total-order records sets ltl conjunction bisimilarity \
	circuit-bisim circuits cone-of-influence reductions impl-hack concrete-ltl 

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

total-order.cert: total-order.lisp

apply-total-order.cert: apply-total-order.lisp
apply-total-order.cert: total-order.cert

records.cert: records.lisp
records.cert: apply-total-order.cert

sets.cert: sets.lisp
sets.cert: records.cert

ltl.cert: ltl.lisp
ltl.cert: sets.cert
ltl.cert: ../../../../arithmetic-2/meta/top.cert

conjunction.cert: conjunction.lisp
conjunction.cert: ltl.cert

bisimilarity.cert: bisimilarity.lisp
bisimilarity.cert: ltl.cert
bisimilarity.cert: ../../../../arithmetic-2/meta/top.cert

circuit-bisim.cert: circuit-bisim.lisp
circuit-bisim.cert: ltl.cert
circuit-bisim.cert: bisimilarity.cert

circuits.cert: circuits.lisp
circuits.cert: circuit-bisim.cert

cone-of-influence.cert: cone-of-influence.lisp
cone-of-influence.cert: circuits.cert
cone-of-influence.cert: ../../../../arithmetic-2/meta/top.cert

reductions.cert: reductions.lisp
reductions.cert: conjunction.cert
reductions.cert: cone-of-influence.cert

impl-hack.cert: impl-hack.lisp
impl-hack.cert: reductions.cert
impl-hack.cert: impl-hack.acl2

concrete-ltl.cert: concrete-ltl.lisp
concrete-ltl.cert: ltl.cert
concrete-ltl.cert: ../../../../ordinals/e0-ordinal.cert
