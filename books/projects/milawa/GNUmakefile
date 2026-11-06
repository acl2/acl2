# GNUmakefile for the Milawa Sources directory.
#
# This builds and runs the standalone proof checker: the "core" images dumped
# from milawa.lsp, replayed against the proofs that the ACL2 build generated in
# Proofs/.  The ACL2 side -- which generates those proofs and the ACL2 images --
# has its own makefile in ACL2/.
#
#   make                       build base.<ext>, then check every level
#   make base                  just build the core image
#   make check                 replay the proofs (resumable: skips any level
#                              whose image already exists)
#   make check-level L=level9  redo a single level
#   make report                event timings and proof-size tables
#   make report-time           slowest events, from final-checks.log
#   make sizes                 per-level proof sizes (writes size_macros.tex)
#   make clean                 remove the core image, level images, and logs
#   make clean-proofs          remove the generated proofs
#
# Settings can be overridden on the command line or in the environment, e.g.
#
#   make LISP=sbcl EXT=my-tag
#
# CCL is the default builder: it needs no custom Lisp build, because its
# value/control stacks are sized at runtime (-Z/-S) and milawa.lsp sets them
# to 128 MB.  Any other Lisp that milawa.lsp can dump is a builder too --
# SBCL, CMUCL, CLISP, SCL, and Allegro CL -- and its milawa-<lisp> launcher
# runs the image it produced.

SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

# Host Lisp.  ACL2's own GNUmakefile uses the same variable name ("LISP = ccl"),
# so honour it rather than hard-coding an implementation.  The value also
# selects the builder recipe below and the milawa-<lisp> launcher that
# final-checks.sh runs, so it must be one of the names milawa.lsp supports:
# ccl, sbcl, cmucl, clisp, scl, or acl.
LISP ?= ccl
LISPNAME ?= $(notdir $(firstword $(LISP)))
CCL ?= $(LISP)
SBCL ?= $(LISP)
CMUCL ?= $(LISP)
CLISP ?= $(LISP)
SCL ?= $(LISP)
ACL ?= $(LISP)
# The executable names are not always the same as these keys (CMUCL's is often
# "lisp"), so override the variable, e.g. "make LISP=cmucl CMUCL=lisp".

# The tag that names the kernel images.  Nothing in Milawa computes this:
# milawa.lsp simply uses whatever IMAGE-EXTENSION is bound to before the load,
# and Jared's examples were free-form names like "ccl-linux64" / "sbcl-win32".
# Derive it from the environment instead, so it cannot claim the wrong platform
# (e.g. linux-aarch64, linux-x86_64, darwin-arm64).
PLATFORM ?= $(shell uname -s | tr 'A-Z' 'a-z')-$(shell uname -m)
EXT      ?= $(LISPNAME)-$(PLATFORM)
CCL_STACK ?= 128M
SBCL_DYNAMIC_SPACE ?= 32000
SBCL_CONTROL_STACK ?= 1024
CMUCL_DYNAMIC_SPACE ?= 2048
CLISP_MEMORY ?= 2048MB

LEVELS ?= utilities logic level2 level3 level4 level5 level6 level7 level8 \
          level9 level10 level11 user

BASE   := base.$(EXT)
IMAGES := $(addsuffix .$(EXT),$(LEVELS))
LOGS   := $(addsuffix .$(EXT).out,$(LEVELS)) final-checks.log

.PHONY: all base check check-level report report-time sizes clean clean-proofs help

all: check

base: $(BASE)

# milawa.lsp ends with (save-and-exit "base"), which names its output
# "base." + IMAGE-EXTENSION, so that variable has to be bound before the load.
ifeq ($(LISPNAME),ccl)
$(BASE): milawa.lsp
	$(CCL) -n -Z $(CCL_STACK) -S $(CCL_STACK) \
	       -e '(defparameter image-extension "$(EXT)")' \
	       -l milawa.lsp \
	       -e '(ccl:quit)'
	@test -f $@ || { echo "error: $@ was not produced" >&2; exit 1; }
else ifeq ($(LISPNAME),sbcl)
$(BASE): milawa.lsp
	$(SBCL) --dynamic-space-size $(SBCL_DYNAMIC_SPACE) \
	        --control-stack-size $(SBCL_CONTROL_STACK) \
	        --noinform --non-interactive \
	        --eval '(defconstant image-extension "$(EXT)")' \
	        --load milawa.lsp
	@test -f $@ || { echo "error: $@ was not produced" >&2; exit 1; }
else ifeq ($(LISPNAME),cmucl)
$(BASE): milawa.lsp
	$(CMUCL) -batch -dynamic-space-size $(CMUCL_DYNAMIC_SPACE) \
	         -eval '(defparameter image-extension "$(EXT)")' \
	         -load milawa.lsp
	@test -f $@ || { echo "error: $@ was not produced" >&2; exit 1; }
else ifeq ($(LISPNAME),clisp)
$(BASE): milawa.lsp
	ulimit -s 65535; \
	$(CLISP) -q -norc -m $(CLISP_MEMORY) \
	         -x '(defparameter image-extension "$(EXT)")' \
	         -i milawa.lsp
	@test -f $@ || { echo "error: $@ was not produced" >&2; exit 1; }
else ifeq ($(LISPNAME),scl)
$(BASE): milawa.lsp
	$(SCL) -batch \
	       -eval '(defparameter image-extension "$(EXT)")' \
	       -load milawa.lsp
	@test -f $@ || { echo "error: $@ was not produced" >&2; exit 1; }
else ifeq ($(LISPNAME),acl)
$(BASE): milawa.lsp
	ulimit -s 65535; \
	$(ACL) -batch \
	       -e '(defparameter image-extension "$(EXT)")' \
	       -l milawa.lsp
	@test -f $@ || { echo "error: $@ was not produced" >&2; exit 1; }
else
$(BASE): milawa.lsp
	@echo "error: no builder recipe for LISP=$(LISP)" >&2
	@echo "       milawa.lsp can dump images with ccl, sbcl, cmucl, clisp, scl, acl" >&2
	@exit 1
endif

check: $(BASE)
	./final-checks.sh $(LISPNAME) $(EXT) | tee final-checks.log
	@echo
	@echo "All levels checked.  Images written: $(BASE) $(IMAGES)"

# final-checks.sh skips levels whose image already exists, so redisplaying one
# level means dropping its image first.
check-level: $(BASE)
	@test -n "$(L)" || { echo "usage: make check-level L=<level>" >&2; exit 1; }
	rm -f $(L).$(EXT) $(L).$(EXT).out
	./final-checks.sh $(LISPNAME) $(EXT) | tee final-checks.log

report: report-time sizes

# Which events took longest, biggest first.  Reads the log that `make check`
# writes.  The whole ranking goes to report-time.txt; REPORT_N controls how
# many lines are echoed.  (Do not pipe the script into `head`: it writes far
# more than that, and SIGPIPE plus `pipefail` would fail the target.)
REPORT_N ?= 40
report-time:
	@test -f final-checks.log || { echo "run 'make check' first" >&2; exit 1; }
	./report-time.rb < final-checks.log > report-time.txt
	@echo "Slowest events (full ranking: report-time.txt)"
	@head -$(REPORT_N) report-time.txt

# Per-level event counts and proof sizes, in the LaTeX table format Jared used
# for the dissertation.  Also writes size_macros.tex in the current directory.
sizes:
	./summarize-sizes.rb

clean:
	rm -f $(BASE) $(IMAGES) $(LOGS)

clean-proofs:
	cd Proofs && ./clean-proofs.sh

help:
	@awk 'NR > 1 { if (/^[^#]/) exit; sub(/^# ?/, ""); print }' GNUmakefile
