.PHONY: all clean veryclean

all: ../bin/rac ../bin/parse

../bin/parse: parser.l parser.y parser.h output.c main.c
	bison -d -v parser.y
	flex parser.l
	g++ -std=c++11 -g -o parse parser.tab.c lex.yy.c output.c main.c
	install -m 775 parse ${RAC}/bin
	/bin/rm parse

../bin/rac: rac-skel
	printf "#!/bin/bash\n\nRAC=${RAC}\nACL2=${ACL2}" | cat - rac-skel > rac
	install -m 775 rac ${RAC}/bin
	/bin/rm rac

clean:
	/bin/rm -f rac parser.tab.c parser.tab.h parser.output lex.yy.c parser.c
	/bin/rm -f -r parse.dSym

veryclean: clean
	/bin/rm -f ../bin/rac ../bin/parse
