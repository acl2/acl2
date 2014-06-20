# ACL2 Sidekick
# Copyright (C) 2014 Kookamara LLC
#
# Contact:
#   Kookamara LLC
#   11410 Windermere Meadows, Austin TX, 78759, USA.
#   http://www.kookamara.com/
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
# Original author: Jared Davis <jared@kookamara.com>

.PHONY: all clean

all:

SHELL := $(shell which bash)
STARTJOB ?= $(SHELL)
ACL2 ?= acl2

$(info Scanning for dependencies...)
REBUILD_MAKEFILE_DEPS := $(shell \
  rm -f Makefile-deps Makefile-deps.out; \
  cert.pl --quiet \
          --static-makefile Makefile-deps \
          --cache Makefile-cache \
          top.cert \
          1>&2) ;\
  echo 'MFDEPS_DEBUG := $$(shell echo Reading book deps ' \
       'Makefile-deps created on' `date` '1>&2)' \
    >> Makefile-deps; \
  ls -l Makefile-deps)
#$(info $(REBUILD_MAKEFILE_DEPS))
$(info Done scanning.)

include Makefile-deps

all: top.cert sidekick

clean:
	clean.pl
	rm -f Makefile-deps Makefile-cache Makefile-tmp
	rm -f sidekick sidekick.ccl

sidekick: top.cert make-sidekick.lsp
	$(STARTJOB) -c "ACL2_CUSTOMIZATION=NONE $(ACL2) < make-sidekick.lsp &> sidekick.out"


