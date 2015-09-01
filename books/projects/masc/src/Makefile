
all: ../bin/masc ../bin/parse 

../bin/parse: parser.l parser.y parser.h output.c main.c
	bison -d -v parser.y
	flex parser.l
	g++ -g -o ../bin/parse parser.tab.c lex.yy.c output.c main.c  -lfl

../bin/masc: masc-skel
	echo -e "#!/bin/bash\n\nMASC=${MASC}\nACL2=${ACL2}" | cat - masc-skel > masc
	install -m 755 masc ${MASC}/bin

clean:
	rm -f masc parser.tab.c parser.tab.h parser.output lex.yy.c parser.c

veryclean: clean
	rm -f ../bin/masc ../bin/parse 
