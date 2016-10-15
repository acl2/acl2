
all: ../bin/masc ../bin/parse 

../bin/parse: parser.l parser.y parser.h output.c main.c
	bison -d -v parser.y
	flex parser.l
	g++ -g -o parse parser.tab.c lex.yy.c output.c main.c  -lfl
	install -m 775 parse ${MASC}/bin
	/bin/rm parse

../bin/masc: masc-skel
	echo -e "#!/bin/bash\n\nMASC=${MASC}\nACL2=${ACL2}" | cat - masc-skel > masc
	install -m 775 masc ${MASC}/bin
	/bin/rm masc

clean:
	/bin/rm -f masc parser.tab.c parser.tab.h parser.output lex.yy.c parser.c

veryclean: clean
	/bin/rm -f ../bin/masc ../bin/parse 
