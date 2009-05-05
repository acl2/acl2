BIG_FILE = "/var/local/jared/hugefile"
SIZE_IN_KB = "300000"
CC = gcc -O2
CPP = g++ -O2
ACL2 = acl2

tests: test-timing-c test-timing-cpp test-timing-lisp

test-timing-c: timing-c
	time ./timing-c	${BIG_FILE} ${SIZE_IN_KB}
	time ./timing-c	${BIG_FILE} ${SIZE_IN_KB}
	time ./timing-c	${BIG_FILE} ${SIZE_IN_KB}
	time ./timing-c	${BIG_FILE} ${SIZE_IN_KB}

test-timing-cpp: timing-cpp
	time ./timing-cpp ${BIG_FILE} ${SIZE_IN_KB}
	time ./timing-cpp ${BIG_FILE} ${SIZE_IN_KB}
	time ./timing-cpp ${BIG_FILE} ${SIZE_IN_KB}
	time ./timing-cpp ${BIG_FILE} ${SIZE_IN_KB}

test-timing-lisp: timing.lisp tests.lisp
	echo "(defconst *SIZE* (* ${SIZE_IN_KB} 1024))" > .workxxx
	echo "(defconst *FILE* \"${BIG_FILE}\")" >> .workxxx
	echo "(ld \"timing.lisp\")" >> .workxxx
	echo ":comp t" >> .workxxx
	echo ":q" >> .workxxx
	echo "(load \"tests.lisp\")" >> .workxxx
	acl2 < .workxxx

programs: timing-c timing-cpp

timing-c: timing.c
	$(CC) timing.c -o timing-c

timing-cpp: timing.cpp
	$(CPP) timing.cpp -o timing-cpp

clean:
	rm -f TMP.* TMP1.* *~ timing-cpp timing-c .workxxx 

