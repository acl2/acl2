# Instructions:

# Before starting, see "Dependencies" below.

# In the shell, execute
# make
# to certify all books.
# To clean up (removing files *.cert, *.o, *.fasl, etc.), in the shell execute
# make clean

top1:
	@echo "Using ACL2=$(ACL2)"
	@$(MAKE) top

top: success.txt

success.txt: mesi.cert crit.cert invp.lisp
	@echo "Making `pwd`/success.txt on `date`"
	@rm -f success.txt workxxx
	@date > run.date
	@echo '(value :q)' > workxxx
	@echo '(acl2::lp)' >> workxxx
	@echo '(acl2::ld "invp.lisp")' >> workxxx
	@echo '(value :q)' >> workxxx
	@echo '(acl2::good-bye)' >> workxxx
	@$(ACL2) < workxxx > run.log 2> run.err
	@rm -f workxxx TMP*
	@if [ ! -f success.txt ]; then \
	echo "**CERTIFICATION FAILED**"; \
	exit 1 ; \
	else \
	ls -al success.txt ; \
	fi

include ../../../../Makefile-generic

# Need to omit invp from BOOKS because targets like all-fas would try to
# include invp as a book:
BOOKS = basis crit mesi records sets total-order


clean: clean-more

clean-more:
	rm -f *.rpt
	rm -f success.txt
	rm -f run.date run.log run.err

# Dependencies:
# In the shell, execute
# make -s dependencies
# to obtain the result below.

basis.cert: basis.lisp

crit.cert: crit.lisp
crit.cert: basis.cert

# invp.cert: invp.lisp
# invp.cert: basis.cert
# invp.cert: crit.cert
# invp.cert: mesi.cert

mesi.cert: mesi.lisp
mesi.cert: basis.cert
mesi.cert: records.cert

records.cert: records.lisp
records.cert: sets.cert

sets.cert: sets.lisp
sets.cert: total-order.cert

total-order.cert: total-order.lisp
