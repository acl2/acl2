

all : snippets.lsp

snippets.lsp : asmtest
	./snippet_table.py lsp

asmtest:

SNIPPET_OBJS := $(patsubst %.nasm,%.o,$(wildcard snippets/*.nasm))


%.o : %.nasm
	nasm -f elf64 $<

%.o : %.c
	gcc -g -c $<

asmtest.o : asmtest.h snippets.h

asmtest: asmtest.o $(SNIPPET_OBJS)
	gcc -g $^ -o asmtest

snippets.h : snippets.txt
	./snippet_table.py h

.PHONY: clean
clean:
	rm -f snippets.lsp asmtest snippets.h asmtest.o $(SNIPPET_OBJS)
