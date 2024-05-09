# -*- Mode: Makefile; tab-width: 4; indent-tabs-mode: t -*-

all: docs

docs:
	sh gendocs.sh -o manual --html "--css-include=style.css" local-time "The local-time Manual"

clean:
	find . \( -name "*.info" -o -name "*.it" -o -name "*.aux" -o -name "*.cp" -o -name "*.fn" -o -name "*.fns" -o -name "*.ky" -o -name "*.log" -o -name "*.pg" -o -name "*.toc" -o -name "*.tp" -o -name "*.vr" -o -name "*.dvi" -o -name "*.cps" -o -name "*.vrs" \) -exec rm {} \;
	rm -rf manual

upload-docs:
	rsync -av --delete -e ssh manual common-lisp.net:/project/local-time/public_html/
#	scp -r manual spec common-lisp.net:/project/local-time/public_html/

# vim: ft=make ts=4 noet
