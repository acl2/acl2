export ACL2?=~/acl2
export RAC?=${ACL2}/books/projects/rac

all:
	(cd src; make all)
	(cd lisp; make all)

clean:
	(cd lisp; make clean)
	(cd src; make clean)
	(cd examples; make clean)

veryclean: clean
	(cd lisp; make veryclean)
	(cd src; make veryclean)
	(cd examples; make veryclean)
