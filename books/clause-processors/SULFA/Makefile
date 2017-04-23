# Matt K. comment 4/22/2017: The following sort of "make" doesn't seem
# to work directly for me.  However, things work fine when using "make
# regression" in the main ACL2 directory.
# make ACL2_SYSTEM_BOOKS=/projects/acl2/v3-2-linux/books ACL2=/projects/acl2/v3-2-linux/allegro-saved_acl2

# Your Perl interpreter
PERL ?= perl

# Your SAT solver executable
SAT_SOLVER ?= ${PWD}/../../../aux/minisat2/${HOSTTYPE}/minisat/core/minisat

# Either "minisat" or "zchaff"
SAT_SOLVER_TYPE ?= minisat

#Or, for example:
#SAT_SOLVER = ${PWD}/../../../sat-solvers/zchaff/zchaff
#SAT_SOLVER_TYPE = zchaff

# Your C compiler
CC = gcc

ACL2_SYSTEM_BOOKS ?= $(shell cd ../.. ; pwd)

# I need a full path so that I can hardcode a call to
# ACL2 in our SULFA smt solver.
ACL2 ?= ${PWD}/${ACL2_SYSTEM_BOOKS}/../saved_acl2

# I want the defaults set in this makefile to carry over into
# subdirectories.
MAKE += PERL=${PERL} SAT_SOLVER=${SAT_SOLVER} SAT_SOLVER_TYPE=${SAT_SOLVER_TYPE} CC=${CC}

DIRS = scripts c-files books

all: check_sat_exec check_sat_type scripts/sulfa-smt

.PHONY: check_sat_type
check_sat_type:
	@if [ $(SAT_SOLVER_TYPE) != "minisat" -a \
              $(SAT_SOLVER_TYPE) != "zchaff" ]; then \
          echo "Illegal SAT_SOLVER_TYPE: '$(SAT_SOLVER_TYPE)'"; \
          exit 1; \
        fi

.PHONY: check_sat_exec
check_sat_exec:
	@if [ ! -f $(SAT_SOLVER) ] ; then \
	  echo "Unable to find sat solver file: '$(SAT_SOLVER)'" ; \
	  exit 1 ; \
	fi

scripts/sulfa-smt: subdirs scripts/interpret_sulfa_file

scripts/sulfa-smt:
	@${MAKE} sulfa-smt -C scripts

subdirs: scripts/interpret_sulfa_file

subdirs:
	@for dir in ${DIRS}; do \
       ${MAKE} -C $$dir; \
        done

.PHONY: subdirs

scripts/interpret_sulfa_file:
	@echo "#!${PERL}" > scripts/interpret_sulfa_file ; \
echo "" >> scripts/interpret_sulfa_file ; \
echo "# WARNING: DO NOT MODIFY THIS FILE DIRECTLY, IT'S GENERATED USING the top-level makefile!" >> scripts/interpret_sulfa_file ; \
echo "while ("'$$'"line = <>) {"  >> scripts/interpret_sulfa_file ; \
echo '$$'"line =~ s,%SULFA_DIR%,${CURDIR},;" >> scripts/interpret_sulfa_file ; \
echo '$$'"line =~ s,%PERL%,${PERL},;" >> scripts/interpret_sulfa_file ; \
echo '$$'"line =~ s,%ACL2%,${ACL2},;" >> scripts/interpret_sulfa_file ; \
echo '$$'"line =~ s,%SAT_SOLVER%,${SAT_SOLVER},;" >> scripts/interpret_sulfa_file ; \
echo '$$'"line =~ s,%SAT_SOLVER_TYPE%,${SAT_SOLVER_TYPE},;" >> scripts/interpret_sulfa_file ; \
echo "" >> scripts/interpret_sulfa_file ; \
echo '$$'"line =~ s/%CREATE_GENERATED_WARNING%/WARNING: DO NOT MODIFY THIS FILE DIRECTLY, IT'S GENERATED FROM ANOTHER FILE BY USING interpret_sulfa_file!/;" >> scripts/interpret_sulfa_file ; \
echo "print "'$$'"line;" >> scripts/interpret_sulfa_file ; \
echo "}" >> scripts/interpret_sulfa_file ; \
echo "" >> scripts/interpret_sulfa_file ; \
chmod ugo+rx-w scripts/interpret_sulfa_file

clean:
	rm -f \#*\# *~
	rm -f scripts/interpret_sulfa_file
	${MAKE} clean-subdirs

clean-subdirs:
	for dir in ${DIRS}; do \
        ${MAKE} clean -C $$dir; \
        done

.PHONY: clean-subdirs


