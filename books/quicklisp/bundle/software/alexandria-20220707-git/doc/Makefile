.PHONY: clean html pdf include clean-include clean-crap info doc

doc: pdf html info clean-crap

clean-include:
	rm -rf include

clean-crap:
	rm -f *.aux *.cp *.fn *.fns *.ky *.log *.pg *.toc *.tp *.tps *.vr

clean: clean-include
	rm -f  *.pdf *.html *.info

include:
	sbcl --no-userinit --eval '(require :asdf)' \
	--eval '(let ((asdf:*central-registry* (list "../"))) (require :alexandria))' \
	--eval '(with-compilation-unit () (load "docstrings.lisp"))' \
	--eval '(sb-texinfo:generate-includes "include/" (list :alexandria-1 :alexandria-2) :base-package :alexandria)' \
	--eval '(quit)'

pdf: include
	texi2pdf alexandria.texinfo

html: include
	makeinfo --html --no-split alexandria.texinfo

info: include
	makeinfo alexandria.texinfo

publish:
	rsync -va alexandria.pdf alexandria.html common-lisp.net:/project/alexandria/public_html/draft/
