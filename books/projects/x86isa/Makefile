# Shilpi Goel

# Usage:

# make JOBS=2 \
#      X86ISA_EXEC=t \
#      ACL2=<Path of the ACL2 image>

#======================================================================
.PHONY: all write_exec_fn top execclean clean
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
 RDRAND_LIB := machine/shared/librdrand.so
 SYSCALL_LIB := machine/shared/libsyscallutils.so
# PROOF_BOOKS += $(LINUX_BOOKS)
endif # ifeq ($(findstring LINUX,$(PLATFORM)), LINUX)

ifeq ($(findstring DARWIN,$(PLATFORM)), DARWIN)
 RDRAND_LIB := machine/shared/librdrand.dylib
 SYSCALL_LIB := machine/shared/libsyscallutils.dylib
# PROOF_BOOKS += $(DARWIN_BOOKS)
endif # ifeq ($(findstring DARWIN,$(PLATFORM)), DARWIN)

X86ISA_EXEC_CERTS = $(RDRAND_LIB)
X86ISA_EXEC_CERTS += $(SYSCALL_LIB)

X86ISA_FULL_EXEC_SUPPORT_EXISTS := $(wildcard machine/x86isa_full_exec_support.lisp)
X86_SYSCALLS_ACL2_EXISTS := $(wildcard machine/x86-syscalls.acl2)

ifneq ($(X86ISA_FULL_EXEC_SUPPORT_EXISTS), machine/x86isa_full_exec_support.lisp)
ifneq ($(X86_SYSCALLS_ACL2_EXISTS), machine/x86-syscalls.acl2)
 X86ISA_EXEC_CERTS += write_exec_fn
endif # ifneq ($(X86_SYSCALLS_ACL2_EXISTS), machine/x86-syscalls.acl2)
endif # ifneq ($(X86ISA_FULL_EXEC_SUPPORT_EXISTS), machine/x86isa_full_exec_support.lisp)
endif # ifeq ($(X86ISA_EXEC), t)

#======================================================================

all: $(X86ISA_EXEC_CERTS) top

write_exec_fn: # Here only when X86ISA_EXEC=t and if generated files don't exist already	
	@$(CC) -g -c machine/shared/get_cpuid_v1_lix64.s -o machine/shared/get_cpuid_v1_lix64.o
	@$(CC) -o machine/shared/check-rdrand-support.o machine/shared/check-rdrand-support.c machine/shared/get_cpuid_v1_lix64.o
	@./machine/shared/check-rdrand-support.o > /dev/null ; \
	if [ $$? != 0 ] ; then \
	  echo 'Note: RDRAND instruction is supported on your machine.' ; \
	  echo 'Note: Including the following C shared libraries:' ; \
	  echo '      $(RDRAND_LIB) $(SYSCALL_LIB)' ; \
	  echo ';; File contents generated during the make process' > machine/x86isa_full_exec_support.lisp ; \
	  echo '(in-package "X86ISA")' >> machine/x86isa_full_exec_support.lisp ; \
	  echo '(defun x86isa_rdrand_exec_support () 42)' >> machine/x86isa_full_exec_support.lisp ; \
	  echo '(defun x86isa_syscall_exec_support () 42)' >> machine/x86isa_full_exec_support.lisp ; \
	else \
	  echo 'Note: RDRAND instruction is not supported on your machine.' ; \
	  echo 'Note: You will not be able to execute the RDRAND instruction on the X86ISA model.' ; \
	  echo 'Note: Including the following C shared libraries:' ; \
	  echo '      $(SYSCALL_LIB)' ; \
	  echo ';; File contents generated during the make process' > machine/x86isa_full_exec_support.lisp ; \
	  echo '(in-package "X86ISA")' >> machine/x86isa_full_exec_support.lisp ; \
	  echo '(defun x86isa_syscall_exec_support () 42)' >> machine/x86isa_full_exec_support.lisp ; \
	fi
	@${info machine/x86isa_full_exec_support.lisp created to support X86ISA_EXEC=$(X86ISA_EXEC).} 
	@${info Note: Please do not add machine/x86isa_full_exec_support.lisp to the repository!} 
	@cp machine/cert.acl2 machine/x86-syscalls.acl2 
	@echo '(ld "x86isa_full_exec_support.lisp" :ld-missing-input-ok t)' >> machine/x86-syscalls.acl2 
	@${info machine/x86-syscalls.acl2 created to support X86ISA_EXEC=$(X86ISA_EXEC).} 
	@${info Note: Please do not add machine/x86-syscalls.acl2 to the repository!} 
	@${info Remember to do 'make execclean' if you wish to build with X86ISA_EXEC=nil.} 
	@${info ----------------------------------------------------------------------} 	

machine/shared/librdrand.dylib: machine/shared/rdrand.c
	$(CC) -m64 -dynamiclib -Wall -o machine/shared/librdrand.dylib \
	     machine/shared/rdrand.c

machine/shared/librdrand.so: machine/shared/rdrand.c
	$(CC) -c -Wall -Werror -fpic -o machine/shared/rdrand.o \
				      machine/shared/rdrand.c
	$(CC) -shared -o machine/shared/librdrand.so machine/shared/rdrand.c

machine/shared/libsyscallutils.dylib: machine/shared/syscall-utils.c
	$(CC) -m64 -dynamiclib -Wall -o machine/shared/libsyscallutils.dylib \
	     machine/shared/syscall-utils.c

machine/shared/libsyscallutils.so: machine/shared/syscall-utils.c
	$(CC) -c -Wall -Werror -fpic -o machine/shared/syscall-utils.o \
				      machine/shared/syscall-utils.c
	$(CC) -shared -o machine/shared/libsyscallutils.so machine/shared/syscall-utils.o

top: $(X86ISA_EXEC_CERTS)
	@${info Note: X86ISA_EXEC is $(X86ISA_EXEC).}
	$(BUILD_DIR)/cert.pl -j $(JOBS) top

execclean:
	rm -f machine/x86-syscalls.cert
	rm -f machine/x86-other-non-det.cert
	rm -f machine/x86isa_full_exec_support.*
	rm -f machine/x86-syscalls.acl2
	rm -f $(RDRAND_LIB)
	rm -f $(SYSCALL_LIB)	
	rm -rf machine/shared/*.o

clean:
	$(BUILD_DIR)/clean.pl
	rm -f machine/x86isa_full_exec_support.*
	rm -f machine/x86-syscalls.acl2
	rm -f $(RDRAND_LIB)
	rm -f $(SYSCALL_LIB)
	rm -rf machine/shared/*.o

#======================================================================
