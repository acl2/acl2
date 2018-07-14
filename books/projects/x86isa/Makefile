# X86ISA Library
#
# Note: The license below is based on the template at:
# http://opensource.org/licenses/BSD-3-Clause
#
# Copyright (C) 2015, Regents of the University of Texas
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# o Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
#
# o Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
#
# o Neither the name of the copyright holders nor the names of its
#   contributors may be used to endorse or promote products derived
#   from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# Original Author(s):
# Shilpi Goel         <shigoel@cs.utexas.edu>

# Usage:

# make JOBS=2 \
#      X86ISA_EXEC=t \
#      ACL2=<Path of the ACL2 image>

#======================================================================
.PHONY: all model tools write_exec_fn top execclean clean
#======================================================================

ifndef ACL2
 $(error Variable ACL2 is undefined.)
endif

BUILD_DIR := $(dir $(ACL2))books/build
CC ?= gcc
X86ISA_EXEC ?= t
JOBS ?= 2

#======================================================================

ifeq ($(X86ISA_EXEC), t)

PLATFORM = $(shell uname | tr a-z A-Z)

ifeq ($(findstring LINUX,$(PLATFORM)), LINUX)
 SYSCALL_LIB := machine/shared/libsyscallutils.so
 X86ISA_EXEC_CERTS = $(SYSCALL_LIB)
# PROOF_BOOKS += $(LINUX_BOOKS)
endif # ifeq ($(findstring LINUX,$(PLATFORM)), LINUX)

ifeq ($(findstring DARWIN,$(PLATFORM)), DARWIN)
 SYSCALL_LIB := machine/shared/libsyscallutils.dylib
 X86ISA_EXEC_CERTS = $(SYSCALL_LIB)
# PROOF_BOOKS += $(DARWIN_BOOKS)
endif # ifeq ($(findstring DARWIN,$(PLATFORM)), DARWIN)

# Note that X86ISA_EXEC_CERTS will be empty if we are on a machine
# other than Darwin or Linux. Currently, for FreeBSD machines, we do
# not have full execution support (i.e., SYSCALLS in programmer-level
# mode will not be simulated.)

X86ISA_FULL_EXEC_SUPPORT_EXISTS := $(wildcard machine/x86isa_full_exec_support.lisp)
X86_SYSCALLS_ACL2_EXISTS := $(wildcard machine/syscalls.acl2)

ifneq ($(X86ISA_EXEC_CERTS), )
ifneq ($(X86ISA_FULL_EXEC_SUPPORT_EXISTS), machine/x86isa_full_exec_support.lisp)
ifneq ($(X86_SYSCALLS_ACL2_EXISTS), machine/syscalls.acl2)
 X86ISA_EXEC_CERTS += write_exec_fn
endif # ifneq ($(X86_SYSCALLS_ACL2_EXISTS), machine/syscalls.acl2)
endif # ifneq ($(X86ISA_FULL_EXEC_SUPPORT_EXISTS), machine/x86isa_full_exec_support.lisp)
endif # ifneq ($(X86ISA_EXEC_CERTS), )
endif # ifeq ($(X86ISA_EXEC), t)

#======================================================================

all: $(X86ISA_EXEC_CERTS) top

model: $(X86ISA_EXEC_CERTS)
	@${info X86ISA_EXEC       := $(X86ISA_EXEC)}
	@${info X86ISA_EXEC_CERTS := $(X86ISA_EXEC_CERTS)}
	@${info Building the x86 ISA model...}
	$(BUILD_DIR)/cert.pl -j $(JOBS) machine/x86

tools: model
	@${info Building tools to enable concrete simulation of x86 programs...}
	$(BUILD_DIR)/cert.pl -j $(JOBS) tools/execution/top

write_exec_fn: # Here only when X86ISA_EXEC=t, X86ISA_EXEC_CERTS is not empty, and if generated files don't exist already	
	@${info Including the following C shared libraries: $(SYSCALL_LIB)}
	@echo ';; File contents generated during the make process:' > machine/x86isa_full_exec_support.lisp 
	@echo '(in-package "X86ISA")' >> machine/x86isa_full_exec_support.lisp
	@echo '(defun x86isa_syscall_exec_support () 42)' >> machine/x86isa_full_exec_support.lisp 
	@${info machine/x86isa_full_exec_support.lisp created to support X86ISA_EXEC=$(X86ISA_EXEC).} 
	@${info Do not add machine/x86isa_full_exec_support.lisp to the repository!} 
	@cp machine/cert.acl2 machine/syscalls.acl2
	@echo '(ld "x86isa_full_exec_support.lisp" :ld-missing-input-ok t)' >> machine/syscalls.acl2 
	@${info machine/syscalls.acl2 created to support X86ISA_EXEC=$(X86ISA_EXEC).} 
	@${info Do not add machine/syscalls.acl2 to the repository!} 
	@${info Remember to do 'make execclean' if you wish to build with X86ISA_EXEC=nil.} 
	@${info ----------------------------------------------------------------------} 

machine/shared/libsyscallutils.dylib: machine/shared/syscall-utils.c
	$(CC) -m64 -dynamiclib -Wall -o machine/shared/libsyscallutils.dylib \
	     machine/shared/syscall-utils.c

machine/shared/libsyscallutils.so: machine/shared/syscall-utils.c
	$(CC) -c -Wall -Werror -fpic -o machine/shared/syscall-utils.o \
				      machine/shared/syscall-utils.c
	$(CC) -shared -o machine/shared/libsyscallutils.so machine/shared/syscall-utils.o

top: $(X86ISA_EXEC_CERTS)
	@${info X86ISA_EXEC       := $(X86ISA_EXEC)}
	@${info X86ISA_EXEC_CERTS := $(X86ISA_EXEC_CERTS)}
	$(BUILD_DIR)/cert.pl -j $(JOBS) top

execclean:
	rm -f machine/syscalls.cert
	rm -f machine/x86-other-non-det.cert
	rm -f machine/x86isa_full_exec_support.*
	rm -f machine/syscalls.acl2
	rm -f $(SYSCALL_LIB)
	rm -rf machine/shared/*.o

clean:
	$(BUILD_DIR)/clean.pl
	rm -f machine/x86isa_full_exec_support.*
	rm -f machine/syscalls.acl2
	rm -f $(SYSCALL_LIB)
	rm -rf machine/shared/*.o

#======================================================================
