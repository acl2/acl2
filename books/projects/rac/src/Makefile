# Set g++ as default, unless the CC environment variable is already set.
ifeq ($(origin CXX),default)
CXX = g++
endif

# Preprocessor, compiler and liker flags. Those lines does not overwrite the
# environment variable, it only append more to them.
CPPFLAGS +=
CXXFLAGS += -Wall -Wextra -pedantic -std=c++17
LDFLAGS +=

OBJS += program/parser/ast/ast.o program/parser/ast/expressions.o
OBJS += program/parser/ast/functions.o program/parser/ast/statements.o
OBJS += program/parser/ast/types.o program/parser/utils/diagnostics.o
OBJS += program/parser/parser.o program/parser/lex.yy.o
OBJS += program/parser/parser.tab.o program/process/typing.o
OBJS += program/process/racconstraint.o program/process/forconstraints.o
OBJS += main.o program/astdumper.o program/program.o program/sexpressions.o

# By default, build and install everything.
all : install

install: release rac
	install -m 775 parse ${RAC}/bin
	install -m 775 rac ${RAC}/bin
	rm rac parse

# We should execute this rule every time, since it depends on some environment
# variables.
rac:
	printf "#!/bin/bash\n\nRAC=${RAC}\nACL2=${ACL2}" | cat - rac-skel > rac

# Configure the releaes (no debug log and highest optiomization level) and
# debug.
release: CPPFLAGS += -O3
release: parse

debug: CPPFLAGS += -DDEBUG
debug: CXXFLAGS += -O0 -g
debug: parse

# Compile and generate dependencies.
CPPFLAGS += -MT $@ -MMD -MP -MF $*.d

DEPFILES := $(SRCS:$*.cpp=$*.d)
$(DEPFILES):
include $(shell find $(DEPFILES) -name '*.d')

# Generate the version header.
version.h:
	sh -e generate_version.sh || sh -e generate_version.sh -default

# Run bison and flex.
# parser.tab is generated in first, we had version.h as dependency to force its
# generation before compiling the rest.
program/parser/parser.tab.cpp: program/parser/parser.yy version.h
	bison -d -v -o program/parser/parser.tab.cpp program/parser/parser.yy -Wall

program/parser/lex.yy.cpp: program/parser/parser.ll program/parser/parser.tab.cpp
	flex -o program/parser/lex.yy.cpp program/parser/parser.ll

# Build the binary.
parse: ${OBJS}
	${CXX} -o parse $(LDFLAGS) ${OBJS}

clean:
	rm -f ${OBJS} version.h program/parser/parser.tab.hpp
	rm -f program/parser/parser.tab.cpp program/parser/lex.yy.cpp
	rm -f -r parse.dSym

veryclean : clean
	rm -rf rac parse

.PHONY : all clean veryclean install rac release debug
