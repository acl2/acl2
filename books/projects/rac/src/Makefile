all : install

parse: parser.ll parser.yy parser.h expressions.cpp functions.cpp types.cpp output.cpp main.cpp
	bison -d -v -o parser.tab.cpp parser.yy
	flex -o lex.yy.cpp parser.ll
	g++ -Wall -Wextra -pedantic -std=c++17 -o3 -o parse functions.cpp expressions.cpp statements.cpp parser.tab.cpp lex.yy.cpp types.cpp output.cpp main.cpp

#We should execute this rule every time, since it depends on some environment
#variables.
rac:
	printf "#!/bin/bash\n\nRAC=${RAC}\nACL2=${ACL2}" | cat - rac-skel > rac

install: parse rac
	install -m 775 parse ${RAC}/bin
	install -m 775 rac ${RAC}/bin
	rm rac parse

clean:
	rm -f rac parser.tab.c parser.tab.h parser.output lex.yy.c parser.c
	rm -f -r parse.dSym

veryclean : clean
	rm -f rac parse

.PHONY : all clean veryclean install rac
