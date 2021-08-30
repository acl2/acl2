export ACL2_DIR?=/Users/davrus01/acl2/
export ACL2?=${ACL2_DIR}/saved_acl2
export RAC?=${ACL2_DIR}/books/projects/rac

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
