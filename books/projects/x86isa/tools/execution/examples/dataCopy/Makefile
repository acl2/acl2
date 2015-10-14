all:
	gcc -O1 -g -c core.c -o core.o
	gcc -o dataCopy.o dataCopy.c core.o

clean:
	rm -f *~
	rm -f *.o

run: all
	./dataCopy.o || /bin/true
