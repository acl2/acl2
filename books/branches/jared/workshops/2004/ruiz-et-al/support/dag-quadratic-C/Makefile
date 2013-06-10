OBJS = lists.o terms.o dags.o

.c.o:
	gcc -c $<

qdag: $(OBJS)
	gcc -o qdag $(OBJS)

lists.o: lists.c

terms.o: terms.c

dags.o: dags.c lists.h terms.h

clean:
	rm -f *.o qdag

