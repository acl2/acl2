include ../Makefile-generic

#  Put dependencies (from `make -s dependencies', or other sources) below.

alternating-series.cert: alternating-series.lisp
alternating-series.cert: ../arithmetic/top.cert
alternating-series.cert: ../arithmetic/realp.cert
alternating-series.cert: ../arithmetic/sumlist.cert

chain-rule.cert: chain-rule.lisp
chain-rule.cert: derivatives.cert

complex-polar.cert: complex-polar.lisp
complex-polar.cert: inverse-trig.cert

continuity-product.cert: continuity-product.lisp
continuity-product.cert: ../arithmetic/realp.cert
continuity-product.cert: nsa.cert

continuity.cert: continuity.lisp
continuity.cert: nsa.cert
continuity.cert: intervals.cert
continuity.cert: ../arithmetic/realp.cert

derivatives.cert: derivatives.lisp
derivatives.cert: continuity.cert

derivatives-composition.cert: derivatives-composition.lisp
derivatives-composition.cert: derivatives.cert

exp-continuous.cert: exp-continuous.lisp
exp-continuous.cert: exp-sum.cert

exp-sum.cert: exp-sum.lisp
exp-sum.cert: ../arithmetic/binomial.cert
exp-sum.cert: inner-sums.cert
exp-sum.cert: exp.cert

exp.cert: exp.lisp
exp.cert: ../arithmetic/abs.cert
exp.cert: ../arithmetic/sumlist.cert
exp.cert: nsa.cert
exp.cert: norm.cert
exp.cert: next-integer.cert
exp.cert: factorial.cert

factorial.cert: factorial.lisp
factorial.cert: ../arithmetic/factorial.cert
factorial.cert: nsa.cert

inner-sums.cert: inner-sums.lisp
inner-sums.cert: ../arithmetic/top.cert
inner-sums.cert: ../arithmetic/sumlist.cert

intervals.cert: intervals.lisp
intervals.cert: nsa.cert

inverse-derivatives.cert: inverse-derivatives.lisp
inverse-derivatives.cert: inverse-monotone.cert
inverse-derivatives.lisp: derivatives.cert

inverse-monotone.cert: inverse-monotone.lisp
inverse-monotone.cert: continuity.cert
inverse-monotone.cert: intervals.cert
inverse-monotone.cert: inverses.cert
inverse-monotone.cert: ../data-structures/utilities.cert

../data-structures/utilities.cert: ../data-structures/utilities.lisp
	cd ../data-structures; $(MAKE) utilities.cert

inverse-square.cert: inverse-square.lisp
inverse-square.cert: inverse-monotone.cert
inverse-square.cert: sqrt.cert

inverse-trig.cert: inverse-trig.lisp
inverse-trig.cert: inverse-monotone.cert
inverse-trig.cert: trig.cert

ln.cert: ln.lisp
ln.cert: inverse-monotone.cert
ln.cert: exp.cert
ln.cert: complex-polar.cert

next-integer.cert: next-integer.lisp
next-integer.cert: ../arithmetic/abs.cert
next-integer.cert: nsa.cert

norm.cert: norm.lisp
norm.cert: nsa.cert
norm.cert: sqrt.cert

nsa.cert: nsa.lisp
nsa.cert: ../arithmetic/idiv.cert
nsa.cert: ../arithmetic/realp.cert

raise.cert: raise.lisp
raise.cert: ln.cert


sine.cert: sine.lisp
sine.cert: ../arithmetic/realp.cert
sine.cert: ../arithmetic/abs.cert
sine.cert: nsa.cert
sine.cert: factorial.cert

sqrt.cert: sqrt.lisp
sqrt.cert: ../arithmetic/top.cert
sqrt.cert: nsa.cert

trig-approx.cert: trig-approx.lisp
trig-approx.cert: trig.cert

trig.cert: trig.lisp
trig.cert: exp.cert
trig.cert: exp-sum.cert
trig.cert: exp-continuous.cert
trig.cert: continuity.cert
trig.cert: alternating-series.cert
