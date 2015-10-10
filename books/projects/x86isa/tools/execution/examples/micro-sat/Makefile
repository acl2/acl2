all:
	gcc micro-sat.c -o micro-sat.o

clean:
	rm -f *~
	rm -f *.o

run: all
	./micro-sat.o || /bin/true
