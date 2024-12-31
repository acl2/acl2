

all : snippets.lsp

snippets.lsp : asmtest
	./snippet_table.py lsp

asmtest:

SNIPPET_OBJS := $(patsubst %.nasm,%.o,$(wildcard snippets/*.nasm))


snippets/%.o : snippets/%.nasm snippets/utils.mac
	cd snippets; nasm -f elf64 $*.nasm

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
