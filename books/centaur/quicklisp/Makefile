# Quicklisp setup for Centaur books
# Copyright (C) 2008-2012 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
#
# Original author: Jared Davis <jared@centtech.com>

STARTJOB ?= $(SHELL)
ACL2 ?= acl2

all: top.cert

quicklisp.lisp:
	curl -O http://beta.quicklisp.org/quicklisp.lisp

setup.lisp: quicklisp.lisp install.lsp
	$(STARTJOB) -c "$(ACL2) < install.lsp &> install.out"

clean:
	rm -rf setup.lisp quicklisp.lisp asdf.lisp cache dists local-projects \
	       tmp install.out quicklisp *.cert.out *.cert.time *.lx64fsl \
               Makefile-tmp *.cert

top.cert: setup.lisp
	cert.pl top.cert
