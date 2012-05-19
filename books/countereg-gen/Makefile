SHELL=/bin/bash
FILES=LICENSE $(wildcard *.lisp)
LIBPATH=acl2s-lib.jar

.PHONY: all clean
.SECONDARY:



all: graph.cert type.cert simple-graph-array.cert mv-proof.cert  rem-and-floor.cert basis.cert utilities.cert num-list-fns.cert num-list-thms.cert switchnat.cert data.cert splitnat.cert library-support.cert base.cert with-timeout.cert  random-state-basis1.cert random-state.cert acl2s-parameter.cert main.cert  top.cert
%.cert: %.lisp %.acl2
	./certify-book.sh "$<"

%.acl2: %.lisp
	java -cp "$(LIBPATH)" acl2s.lib.certify.MaybeExtractPreamble "$<"

top.cert: main.cert base.cert
main.cert: type.cert with-timeout.cert acl2s-parameter.cert
acl2s-parameter.cert: utilities.cert
random-state.cert: random-state-basis1.cert
random-state-basis1.cert: pkg.lsp
type.cert: utilities.cert graph.cert
base.cert: data.cert splitnat.cert switchnat.cert graph.cert library-support.cert 
data.cert: utilities.cert graph.cert splitnat.cert switchnat.cert pkg.lsp acl2s-parameter.cert
graph.cert: utilities.cert pkg.lsp
simple-graph-array.cert: utilities.cert
utilities.cert: basis.cert pkg.lsp
basis.cert: pkg.lsp
splitnat.cert:  num-list-thms.cert rem-and-floor.cert 
switchnat.cert:  num-list-thms.cert rem-and-floor.cert  mv-proof.cert
num-list-fns.cert: pkg.lsp
num-list-thms.cert: num-list-fns.cert
mv-proof.cert: pkg.lsp
rem-and-floor.cert: pkg.lsp

#does thhis even work??
TAGS: 
	etags *.lisp

clean:
	rm -rf *.{o,cert,acl2,out,fasl,lx64fsl,lx32fsl,wx64fsl,wx32fsl} *expansion.lsp TAGS
