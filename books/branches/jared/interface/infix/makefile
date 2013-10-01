
# ACL2 Version 1.9

# Copyright (C) 1989-96 Computational Logic, Inc. (CLI).  All rights reserved.

# Use of this software constitutes agreement with the terms of the
# license agreement, found in the file LICENSE.

#  Example invocations (see README):

#   make             ; Recompile what's needed. 
#   make example     ; Create and print example forms in MODE.
#   make events      ; Create and print example events in MODE.
#   make clean       ; Cleanup everything but .o files and TAG table.
#   make tags        ; Create TAG table.
#   make full        ; Clean, compile, create TAGS, and print example in MODE.

LISP =  acl2
DIR =   /acl2/interface/infix
SAVED = ${DIR}/Save
# TEST =  ${DIR}/test
TEST =  ${DIR}/books
# MODE =  "scribe"
MODE =  "latex"
LPR = lpr
DVI = dvips

sources = infix.lisp scribe-init.lisp latex-init.lisp

# 'make' without a target uses the first one, e.g.

compile: ${sources}
	rm -f workxxx
	echo ':q' > workxxx
	echo '(in-package "user")' >> workxxx
	echo '(when (find-package "sloop") (use-package "sloop"))' >> workxxx
	echo '(compile-file "infix.lisp")' >> workxxx
	echo '(load "infix")' >> workxxx
	echo '(compile-file "scribe-init.lisp")' >> workxxx
	echo '(compile-file "latex-init.lisp")' >> workxxx
	${LISP} < workxxx
	rm -f workxxx

full:   clean tags example events

tags:   ${sources}
	etags *.lisp

example: 
	rm -f workxxx 
	echo ':q' > workxxx
	echo '(in-package "user")' >> workxxx
	echo '(when (find-package "sloop") (use-package "sloop"))' >> workxxx
	echo '(load "infix")' >> workxxx
	echo '(print-examples ${MODE})' >> workxxx
	${LISP} < workxxx
	if [ ${MODE} = "scribe" ] ; then \
	  scribe infix-examples.mss ; scribe infix-examples.mss ; ${LPR} infix-examples.ps;\
	else \
	  rm -f infix-examples.aux ; latex infix-examples ; ${DVI} -o infix-examples.ps infix-examples ; \
	fi

events: #clean-doc
	rm -f workxxx
	echo ':q' > workxxx
	echo '(in-package "user")' >> workxxx
	echo '(when (find-package "sloop") (use-package "sloop"))' >> workxxx
	echo '(load "infix")' >> workxxx
	echo '(infix-file "sample.lisp" :mode "${MODE}")' >> workxxx
	${LISP} < workxxx
	if [ ${MODE} = "scribe" ] ; then \
	  scribe sample.mss ; else \
	  latex sample && latex sample && ${DVI} -o sample.ps sample ; \
	fi

clean-all:  clean
	rm -f *.o TAGS

clean: clean-doc
	rm -f *~* *#* workxxx *.o *.tex *.nqtex TAGS *.dvi *.ps *.err *.aux *.log *.idx

clean-doc:
	rm -f ${DIR}/*.otl ${DIR}/*.err ${DIR}/*.ps ${DIR}/*.aux
	rm -f ${DIR}/*.dvi ${DIR}/*.aux ${DIR}/*.log ${DIR}/*.idx ${DIR}/.log 
