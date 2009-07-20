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

# Dependencies:

# Certify.cert: Certify.lisp

alls.cert: alls.lisp
alls.cert: variables.cert
alls.cert: ../../../../../ordinals/e0-ordinal.cert

arithmetic.cert: arithmetic.lisp
arithmetic.cert: ../../../../../arithmetic/top.cert

base.cert: base.lisp
base.cert: sets.cert
base.cert: ../../../../../ordinals/e0-ordinal.cert

close.cert: close.lisp
close.cert: keval.cert
close.cert: permutations.cert
close.cert: ../../../../../ordinals/e0-ordinal.cert
close.cert: arithmetic.cert

cnf.cert: cnf.lisp
cnf.cert: wfftype.cert

derive.cert: derive.lisp
derive.cert: uc-conj.cert
derive.cert: prop-subsume.cert
derive.cert: substitution.cert
derive.cert: resolve.cert
derive.cert: paramod.cert
derive.cert: flip.cert

flip.cert: flip.lisp
flip.cert: paramod.cert
flip.cert: close.cert

gensym-e.cert: gensym-e.lisp

instance-closure.cert: instance-closure.lisp
instance-closure.cert: instance.cert
instance-closure.cert: ../../../../../ordinals/e0-ordinal.cert
instance-closure.cert: close.cert

instance.cert: instance.lisp
instance.cert: stage.cert

keval.cert: keval.lisp
keval.cert: stage.cert
keval.cert: ../../../../../ordinals/e0-ordinal.cert

modeler.cert: modeler.lisp
modeler.cert: nnf.cert
modeler.cert: rename-top.cert
modeler.cert: skolem-top.cert
modeler.cert: cnf.cert
modeler.cert: pull-top.cert
modeler.cert: derive.cert

nnf.cert: nnf.lisp
nnf.cert: stage.cert

paramod.cert: paramod.lisp
paramod.cert: stage.cert
paramod.cert: arithmetic.cert
paramod.cert: close.cert

permutations.cert: permutations.lisp
permutations.cert: sets.cert

prop-subsume.cert: prop-subsume.lisp
prop-subsume.cert: stage.cert
prop-subsume.cert: close.cert

prover.cert: prover.lisp
prover.cert: nnf.cert
prover.cert: rename-top.cert
prover.cert: skolem-top.cert
prover.cert: cnf.cert
prover.cert: right-assoc.cert
prover.cert: pull-top.cert
prover.cert: derive.cert
prover.cert: simplify.cert

pull-pulls.cert: pull-pulls.lisp
pull-pulls.cert: pull.cert

pull-sound.cert: pull-sound.lisp
pull-sound.cert: pull.cert

pull-top.cert: pull-top.lisp
pull-top.cert: pull.cert
pull-top.cert: pull-sound.cert
pull-top.cert: pull-pulls.cert

pull.cert: pull.lisp
pull.cert: wfftype.cert
pull.cert: permutations.cert

rename-sound.cert: rename-sound.lisp
rename-sound.cert: rename.cert
rename-sound.cert: xeval.cert

rename-top.cert: rename-top.lisp
rename-top.cert: rename.cert
rename-top.cert: rename-sound.cert
rename-top.cert: rename-unique.cert

rename-unique.cert: rename-unique.lisp
rename-unique.cert: rename.cert
rename-unique.cert: permutations.cert

rename.cert: rename.lisp
rename.cert: wfftype.cert
rename.cert: gensym-e.cert

resolve.cert: resolve.lisp
resolve.cert: stage.cert
resolve.cert: close.cert

right-assoc.cert: right-assoc.lisp
right-assoc.cert: stage.cert

sets.cert: sets.lisp

simple-check.cert: simple-check.lisp
simple-check.cert: derive.cert

simplify.cert: simplify.lisp
simplify.cert: stage.cert

simultaneous-d.cert: simultaneous-d.lisp
simultaneous-d.cert: substitution.cert

sk-misc-lemmas.cert: sk-misc-lemmas.lisp
sk-misc-lemmas.cert: stage.cert

sk-step-sound.cert: sk-step-sound.lisp
sk-step-sound.cert: sk-useless.cert
sk-step-sound.cert: sk-step.cert
sk-step-sound.cert: instance.cert
sk-step-sound.cert: sk-xbuild.cert

sk-step.cert: sk-step.lisp
sk-step.cert: stage.cert
sk-step.cert: sk-misc-lemmas.cert
sk-step.cert: ../../../../../ordinals/e0-ordinal.cert

sk-useless.cert: sk-useless.lisp
sk-useless.cert: sk-misc-lemmas.cert

sk-xbuild.cert: sk-xbuild.lisp
sk-xbuild.cert: sk-useless.cert
sk-xbuild.cert: sk-step.cert
sk-xbuild.cert: arithmetic.cert

skolem-top.cert: skolem-top.lisp
skolem-top.cert: sk-step-sound.cert
skolem-top.cert: permutations.cert
skolem-top.cert: gensym-e.cert

stage.cert: stage.lisp
stage.cert: wfftype.cert
stage.cert: xeval.cert

substitution.cert: substitution.lisp
substitution.cert: instance-closure.cert
substitution.cert: gensym-e.cert

sugar.cert: sugar.lisp
sugar.cert: base.cert

top.cert: top.lisp
top.cert: prover.cert
top.cert: modeler.cert

uc-conj.cert: uc-conj.lisp
uc-conj.cert: stage.cert
uc-conj.cert: close.cert

variables.cert: variables.lisp
variables.cert: base.cert

wfftype.cert: wfftype.lisp
wfftype.cert: alls.cert

xeval.cert: xeval.lisp
xeval.cert: base.cert
xeval.cert: ../../../../../ordinals/e0-ordinal.cert

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
