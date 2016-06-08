export ACL2?=/nfs/pdx/disks/ccdo.val.work.238/valid/fvcoe/fvcoe_work.2/users/dmrussin/acl2
export MASC?=/nfs/pdx/disks/ccdo.val.work.238/valid/fvcoe/fvcoe_work.2/users/dmrussin/acl2/books/projects/masc

all:
	(cd src; make all)
	(cd lisp; make all)

clean:
	(cd lisp; make clean)
	(cd src; make clean)

veryclean: clean
	(cd lisp; make veryclean)
	(cd src; make veryclean)
