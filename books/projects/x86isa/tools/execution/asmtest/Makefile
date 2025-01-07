

all : snippets.lsp

snippets.lsp : asmtest
	./snippet_table.py lsp

asmtest:

SNIPPET_OBJS := $(patsubst %.nasm,%.o,$(wildcard snippets/*.nasm)) snippets/testgen.o


snippets/%.o : snippets/%.nasm snippets/utils.mac snippets/testgen.nasm
	cd snippets; nasm -f elf64 $*.nasm

%.o : %.c
	gcc -g -c $<

asmtest.o : asmtest.h snippets.h

asmtest: asmtest.o $(SNIPPET_OBJS)
	gcc -g $^ -o asmtest

snippets.h : snippets-combined.txt
	./snippet_table.py h

testgen/testgen:
	cd testgen && make testgen

snippets-generated.txt snippets/testgen.nasm: testgen/testgen
	./testgen/testgen -a snippets/testgen.nasm -t snippets-generated.txt

snippets-combined.txt: snippets-generated.txt
	echo "# Generated file -- do not edit" | cat - snippets.txt snippets-generated.txt > snippets-combined.txt

check-test: snippets.lsp
ifndef ACL2
	$(error Variable ACL2 is undefined.)
endif
	< check-test.lsp $(ACL2)

.PHONY: test
test: check-test snippets.txt asmtest snippets.lsp
	rm -rf inputs outputs results
	mkdir -p inputs outputs
	< snippets-combined.txt sed '/^#/d;/^$$/d' | ./run-tests.sh
	< snippets-combined.txt sed '/^#/d;/^$$/d' | ./get-results.sh

.PHONY: clean
clean:
	pushd testgen && make clean && popd
	rm -rf check-test check-test.lx86cl64 inputs outputs results snippets-generated.txt snippets-combined.txt snippets.lsp asmtest snippets.h asmtest.o $(SNIPPET_OBJS)
