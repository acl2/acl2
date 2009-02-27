include ../../../Makefile-generic
ACL2 ?= ../../../../saved_acl2


# don't alphabetize this!
BOOKS = ground-zero induct predicate rationalp negative-syntaxp integerp inverted-factor fp2 fp arith2 arith denominator numerator unary-divide product-proofs product nniq basic cg complex-rationalp even-odd  expt-proofs expt expo expo-proofs fl-proofs fl fl-expt floor floor-proofs hacks mod-proofs mod mod-expt power2p product unary-divide x-2xx even-odd2-proofs even-odd2 fl-hacks top extra-rules common-factor-defuns common-factor

# remove float?
# remove util?
# remove hacks?
# remove induct?
#  land lextra lior log logand logand-proofs logeqv logior logior1 lognot logorc1 logs logxor lxor lnot ash 



ground-zero.cert: ground-zero.lisp

induct.cert: induct.lisp
induct.cert: fl.cert

predicate.cert: predicate.lisp

rationalp.cert: rationalp.lisp
rationalp.cert: predicate.cert

negative-syntaxp.cert: negative-syntaxp.lisp

integerp.cert: integerp.lisp
integerp.cert: negative-syntaxp.cert
integerp.cert: predicate.cert
integerp.cert: fp2.cert

inverted-factor.cert: inverted-factor.lisp

fp2.cert: fp2.lisp
fp2.cert: ../../../ihs/ihs-definitions.cert
fp2.cert: ../../../ihs/ihs-lemmas.cert
fp2.cert: ../../../ihs/ihs-lemmas.cert
fp2.cert: ../../../arithmetic-2/meta/non-linear.cert
fp2.cert: inverted-factor.cert
fp2.cert: ../../../ordinals/e0-ordinal.cert

fp.cert: fp.lisp
fp.cert: fp2.cert

arith2.cert: arith2.lisp
arith2.cert: fp2.cert
arith2.cert: predicate.cert
arith2.cert: product.cert
arith2.cert: ../../../meta/meta-times-equal.cert
arith2.cert: ../../../meta/meta-plus-equal.cert
arith2.cert: ../../../meta/meta-plus-lessp.cert
arith2.cert: ../../../meta/meta-times-equal.cert
arith2.cert: ../../../meta/meta-plus-equal.cert
arith2.cert: ../../../meta/meta-plus-lessp.cert
arith2.cert: inverted-factor.cert

arith.cert: arith.lisp
arith.cert: arith2.cert
arith.cert: ../../../meta/meta-plus-equal.cert
arith.cert: ../../../meta/meta-plus-lessp.cert
arith.cert: ../../../meta/meta-times-equal.cert

denominator.cert: denominator.lisp
denominator.cert: ground-zero.cert
denominator.cert: fp2.cert
denominator.cert: ../../../arithmetic/mod-gcd.cert

numerator.cert: numerator.lisp
numerator.cert: ground-zero.cert
numerator.cert: fp2.cert
numerator.cert: denominator.cert
numerator.cert: predicate.cert

unary-divide.cert: unary-divide.lisp
unary-divide.cert: predicate.cert
unary-divide.cert: fp2.cert
unary-divide.cert: inverted-factor.cert

product-proofs.cert: product-proofs.lisp
product-proofs.cert: predicate.cert
product-proofs.cert: fp2.cert

product.cert: product.lisp
product.cert: product-proofs.cert

nniq.cert: nniq.lisp
nniq.cert: ground-zero.cert
nniq.cert: fp2.cert
nniq.cert: denominator.cert
nniq.cert: numerator.cert
nniq.cert: predicate.cert
nniq.cert: unary-divide.cert
nniq.cert: product.cert
nniq.cert: integerp.cert
nniq.cert: arith.cert
nniq.cert: ../../../arithmetic/rationals.cert
nniq.cert: ../../../arithmetic/idiv.cert
nniq.cert: ../../../arithmetic/idiv.cert
nniq.cert: ../../../arithmetic/top-with-meta.cert

basic.cert: basic.lisp
basic.cert: fp2.cert
basic.cert: even-odd.cert
basic.cert: fl.cert
basic.cert: fl.cert
basic.cert: expt.cert

cg.cert: cg.lisp
cg.cert: fl.cert
cg.cert: fp2.cert
cg.cert: integerp.cert
cg.cert: integerp.cert
cg.cert: arith2.cert
cg.cert: common-factor.cert

complex-rationalp.cert: complex-rationalp.lisp
complex-rationalp.cert: predicate.cert

even-odd.cert: even-odd.lisp
even-odd.cert: integerp.cert
even-odd.cert: predicate.cert
even-odd.cert: fp2.cert

expt-proofs.cert: expt-proofs.lisp
expt-proofs.cert: ground-zero.cert
expt-proofs.cert: negative-syntaxp.cert
expt-proofs.cert: predicate.cert
expt-proofs.cert: fp2.cert
expt-proofs.cert: numerator.cert
expt-proofs.cert: denominator.cert
expt-proofs.cert: integerp.cert
expt-proofs.cert: fl.cert
expt-proofs.cert: arith2.cert
expt-proofs.cert: ../../../arithmetic/top.cert
expt-proofs.cert: even-odd.cert

expt.cert: expt.lisp
expt.cert: ground-zero.cert
expt.cert: negative-syntaxp.cert
expt.cert: expt-proofs.cert

expo.cert: expo.lisp
expo.cert: ground-zero.cert
expo.cert: negative-syntaxp.cert
expo.cert: power2p.cert
expo.cert: expo-proofs.cert
expo.cert: common-factor-defuns.cert

expo-proofs.cert: expo-proofs.lisp
expo-proofs.cert: negative-syntaxp.cert
expo-proofs.cert: power2p.cert
expo-proofs.cert: unary-divide.cert
expo-proofs.cert: arith2.cert
expo-proofs.cert: integerp.cert
expo-proofs.cert: fl.cert
expo-proofs.cert: expt.cert
expo-proofs.cert: ../../../ordinals/e0-ordinal.cert
expo-proofs.cert: common-factor-defuns.cert
expo-proofs.cert: common-factor.cert

fl-proofs.cert: fl-proofs.lisp
fl-proofs.cert: numerator.cert
fl-proofs.cert: denominator.cert
fl-proofs.cert: nniq.cert
fl-proofs.cert: arith2.cert
fl-proofs.cert: ground-zero.cert
fl-proofs.cert: floor.cert
fl-proofs.cert: integerp.cert
fl-proofs.cert: rationalp.cert
fl-proofs.cert: unary-divide.cert
fl-proofs.cert: common-factor.cert
fl-proofs.cert: negative-syntaxp.cert

fl.cert: fl.lisp
fl.cert: negative-syntaxp.cert
fl.cert: fl-proofs.cert

fl-expt.cert: fl-expt.lisp
fl-expt.cert: numerator.cert
fl-expt.cert: denominator.cert
fl-expt.cert: nniq.cert
fl-expt.cert: arith2.cert
fl-expt.cert: ground-zero.cert
fl-expt.cert: floor.cert
fl-expt.cert: integerp.cert
fl-expt.cert: rationalp.cert
fl-expt.cert: unary-divide.cert
fl-expt.cert: expt.cert
fl-expt.cert: expo.cert
fl-expt.cert: power2p.cert
fl-expt.cert: fl.cert

floor.cert: floor.lisp
floor.cert: floor-proofs.cert

floor-proofs.cert: floor-proofs.lisp
floor-proofs.cert: ground-zero.cert
floor-proofs.cert: fp2.cert
floor-proofs.cert: denominator.cert
floor-proofs.cert: numerator.cert
floor-proofs.cert: predicate.cert
floor-proofs.cert: nniq.cert
floor-proofs.cert: product.cert
floor-proofs.cert: unary-divide.cert
floor-proofs.cert: rationalp.cert
floor-proofs.cert: inverted-factor.cert
floor-proofs.cert: ../../../meta/meta-plus-lessp.cert

hacks.cert: hacks.lisp
hacks.cert: fp2.cert

mod-proofs.cert: mod-proofs.lisp
mod-proofs.cert: ground-zero.cert
mod-proofs.cert: negative-syntaxp.cert
mod-proofs.cert: floor.cert
mod-proofs.cert: arith2.cert
mod-proofs.cert: power2p.cert
mod-proofs.cert: fp2.cert
mod-proofs.cert: arith.cert
mod-proofs.cert: integerp.cert
mod-proofs.cert: product.cert
mod-proofs.cert: complex-rationalp.cert
mod-proofs.cert: ../../../meta/meta-plus-equal.cert
mod-proofs.cert: ../../../meta/meta-plus-lessp.cert
mod-proofs.cert: predicate.cert
mod-proofs.cert: rationalp.cert
mod-proofs.cert: fl.cert

mod.cert: mod.lisp
mod.cert: ground-zero.cert
mod.cert: negative-syntaxp.cert
mod.cert: mod-proofs.cert
mod.cert: fl.cert

mod-expt.cert: mod-expt.lisp
mod-expt.cert: power2p.cert
mod-expt.cert: numerator.cert
mod-expt.cert: denominator.cert
mod-expt.cert: nniq.cert
mod-expt.cert: arith2.cert
mod-expt.cert: ground-zero.cert
mod-expt.cert: floor.cert
mod-expt.cert: integerp.cert
mod-expt.cert: rationalp.cert
mod-expt.cert: unary-divide.cert
mod-expt.cert: expt.cert
mod-expt.cert: expo.cert
mod-expt.cert: fl-expt.cert
mod-expt.cert: mod.cert
mod-expt.cert: fl.cert

power2p.cert: power2p.lisp
power2p.cert: fl.cert
power2p.cert: fp2.cert
power2p.cert: predicate.cert
power2p.cert: unary-divide.cert
power2p.cert: ../../../ordinals/e0-ordinal.cert

product.cert: product.lisp
product.cert: product-proofs.cert

unary-divide.cert: unary-divide.lisp
unary-divide.cert: predicate.cert
unary-divide.cert: fp2.cert
unary-divide.cert: inverted-factor.cert

x-2xx.cert: x-2xx.lisp
x-2xx.cert: ../../../arithmetic/top-with-meta.cert
x-2xx.cert: ../../../arithmetic/mod-gcd.cert

even-odd2-proofs.cert: even-odd2-proofs.lisp
even-odd2-proofs.cert: integerp.cert
even-odd2-proofs.cert: arith.cert
even-odd2-proofs.cert: arith2.cert
even-odd2-proofs.cert: fp2.cert

even-odd2.cert: even-odd2.lisp
even-odd2.cert: ground-zero.cert
even-odd2.cert: even-odd2-proofs.cert

fl-hacks.cert: fl-hacks.lisp
fl-hacks.cert: ground-zero.cert
fl-hacks.cert: inverted-factor.cert
fl-hacks.cert: nniq.cert
fl-hacks.cert: numerator.cert
fl-hacks.cert: denominator.cert
fl-hacks.cert: fp2.cert
fl-hacks.cert: predicate.cert
fl-hacks.cert: product.cert
fl-hacks.cert: unary-divide.cert
fl-hacks.cert: rationalp.cert
fl-hacks.cert: integerp.cert
fl-hacks.cert: fl.cert
fl-hacks.cert: mod.cert
fl-hacks.cert: even-odd.cert
fl-hacks.cert: ../../../meta/meta-plus-equal.cert
fl-hacks.cert: arith.cert

top.cert: top.lisp
top.cert: ground-zero.cert
top.cert: induct.cert
top.cert: denominator.cert
top.cert: numerator.cert
top.cert: nniq.cert
top.cert: complex-rationalp.cert
top.cert: rationalp.cert
top.cert: integerp.cert
top.cert: arith.cert
top.cert: arith2.cert
top.cert: fp2.cert
top.cert: basic.cert
top.cert: unary-divide.cert
top.cert: product.cert
top.cert: inverted-factor.cert
top.cert: negative-syntaxp.cert
top.cert: predicate.cert
top.cert: x-2xx.cert
top.cert: power2p.cert
top.cert: expt.cert
top.cert: expo.cert
top.cert: fl-hacks.cert
top.cert: even-odd2.cert
top.cert: even-odd.cert
top.cert: floor.cert
top.cert: fl.cert
top.cert: cg.cert
top.cert: mod.cert
top.cert: fl-expt.cert
top.cert: mod-expt.cert
top.cert: common-factor.cert

extra-rules.cert: extra-rules.lisp
extra-rules.cert: basic.cert

common-factor-defuns.cert: common-factor-defuns.lisp
common-factor-defuns.cert: inverted-factor.cert

common-factor.cert: common-factor.lisp
common-factor.cert: ../../../meta/meta-times-equal.cert
common-factor.cert: ../../../meta/meta-plus-equal.cert
common-factor.cert: ../../../meta/meta-plus-lessp.cert
common-factor.cert: common-factor-defuns.cert
common-factor.cert: predicate.cert
common-factor.cert: fp2.cert
common-factor.cert: product.cert
