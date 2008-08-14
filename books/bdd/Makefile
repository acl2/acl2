include ../Makefile-generic
-include Makefile-deps

BOOKS = $(patsubst %.lisp, %, $(wildcard *.lisp)) benchmarks

clean: clean-benchmarks

clean-benchmarks:
	rm -f benchmarks.lisp

benchmarks.lisp: cbf.cert