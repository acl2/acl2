include ../Makefile-generic
-include Makefile-deps

all: $(BOOKS_CERT) bookdoc.dat

.PHONY: moreclean
moreclean:
	rm -rf manual
	rm -rf *.time
	rm -rf bookdoc.dat

clean: moreclean

# Goofy.  We don't want to actually list the dependencies of bookdoc.dat.  In
# principle, we should rebuild it any time any Lisp file in :dir :system is
# changed (and it should be smart enough to figure out which books have
# documentation on its own).  But this is hard.  I don't want to manually
# maintain a giant list of lisp files that bookdoc.dat depends on, and
# automatic dependency scanning is painful in GNU Make, so I don't want to deal
# with it.
#
# Practically speaking, it isn't really crucial that bookdoc.dat be rebuilt all
# the time.  Documentation really isn't updated that frequently, and even if
# the documentation in bookdoc.dat is out of date, the (maybe-import-bookdoc)
# command only adds topics that aren't already loaded, so the user won't see
# outdated documentation at runtime with :xdoc unless they're looking at a
# topic in a book that they haven't loaded.  I think it's reasonable to accept
# this.

bookdoc.dat: $(wildcard *.lsp) $(wildcard *.lisp)
	@$(ACL2) < bookdoc.lsp > bookdoc.out
	@ls -l bookdoc.dat

make-manual.cert: bookdoc.dat


