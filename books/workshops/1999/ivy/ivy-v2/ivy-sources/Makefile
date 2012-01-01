include ../../../../../Makefile-generic

# Override default setting since Certify.lisp is not intended to be certified.

BOOKS = alls arithmetic base close cnf derive		\
  flip gensym-e instance-closure instance keval		\
  modeler nnf paramod permutations prop-subsume		\
  prover pull-pulls pull-sound pull-top pull		\
  rename-sound rename-top rename-unique rename resolve	\
  right-assoc sets simple-check simplify simultaneous-d	\
  sk-misc-lemmas sk-step-sound sk-step sk-useless	\
  sk-xbuild skolem-top stage substitution sugar top	\
  uc-conj variables wfftype xeval

-include Makefile-deps

# Original target from Ivy distribution:
ivy:
	acl2 < Certify.lisp > Certify.out
	grep -v FAIL Certify.out > /dev/null

realclean:
	/bin/rm -f *.out
	/bin/rm -f *.cert
	/bin/rm -f *.o
	/bin/rm -f saved_ivy
	/bin/rm -f test/*.in
	/bin/rm -f test/*.proof-obj
	/bin/rm -f test/*.model
	/bin/rm -f examples/*.in
	/bin/rm -f examples/*.proof-obj
	/bin/rm -f examples/*.model
	/bin/rm -f exercises/*.out
	/bin/rm -f exercises/*.cert
	/bin/rm -f exercises/*.o
	/bin/rm -f util/ivy
	/bin/rm -f util/sivy
	/bin/rm -f util/checker
	/bin/rm -f util/make-saved-ivy
	/bin/rm -f *~ */*~
