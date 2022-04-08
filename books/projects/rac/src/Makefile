CXX=g++
CXXFLAGS=-O3 -march=native

# Tricks to force to use a C++ compiler and bison and not a C compiler / Yacc
# (by default make consider that a *.c file is a C code and *.y is a Yacc
# # file).
CC=${CXX}
CFLAGS=${CXXFLAGS}
YACC=bison

OBJ=parser.tab.o lex.yy.o output.o main.o


all: ../bin/rac ../bin/parse

../bin/parse: ${OBJ}
	${CXX} ${CXXFLAGS} -o parse ${OBJ}
	install -m 775 parse ${RAC}/bin
	/bin/rm parse

parser.tab.c parser.tab.h: parser.y
	bison -d -v parser.y

lex.yy.c: parser.tab.h parser.l
	flex parser.l

../bin/rac: rac-skel
	printf "#!/bin/bash\n\nRAC=${RAC}\nACL2=${ACL2}" | cat - rac-skel > rac
	install -m 775 rac ${RAC}/bin
	/bin/rm rac

.PHONY: clean veryclean

clean:
	/bin/rm -f rac parser.tab.c parser.tab.h parser.output lex.yy.c parser.c
	/bin/rm -f ${OBJ}
	/bin/rm -f -r parse.dSym

veryclean: clean
	/bin/rm -f ../bin/rac ../bin/parse
