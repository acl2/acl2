all: overkill

clean: 
	rm -f *.o overkill

overkill: overkill.cpp Manager.o Worker.o
	g++ -lpthread -Wall -O2 -s overkill.cpp Manager.o Worker.o -o overkill

Manager.o: Manager.cpp Manager.h
	g++ -c -Wall -O2 Manager.cpp

Worker.o: Worker.cpp Worker.h
	g++ -c -Wall -O2 Worker.cpp
