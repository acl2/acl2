# ACL2 Sidekick
# Copyright (C) 2014 Kookamara LLC
#
# Contact:
#
#   Kookamara LLC
#   11410 Windermere Meadows
#   Austin, TX 78759, USA
#   http://www.kookamara.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
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
	rm -f sidekick sidekick.ccl
	$(STARTJOB) -c "SIDEKICK_NO_AUTOLOAD=1 ACL2_CUSTOMIZATION=NONE $(ACL2) < make-sidekick.lsp &> sidekick.out"
	ls -lah sidekick


