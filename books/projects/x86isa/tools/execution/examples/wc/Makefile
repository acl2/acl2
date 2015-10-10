all: wc-file.o wc-input.o

wc-file.o: 
	gcc -O2 wc-file.c -o wc-file.o

wc-input.o:
# Don't use O2 here. GCC generates weird assembly for that (some asm constraints are violated).
	gcc wc-input.c -o wc-input.o 

file-run: wc-file.o
	./wc-file.o || /bin/true # Takes file name as cmd line arg

input-run: wc-input.o
	./wc-input.o || /bin/true  # Takes input from cmd line arg; # serves as the EOF

clean:
	rm -f *~
	rm -f *.o
