include ../Makefile-generic

BOOKS = algebra simple gray-code sort merge-sort batcher-sort bitonic-sort \
        prefix-sum cla-adder

#  Put dependencies (from `make -s dependencies', or other sources) below.

algebra.cert: algebra.lisp
algebra.cert: ../data-structures/structures.cert
algebra.cert: ../ordinals/e0-ordinal.cert

simple.cert: simple.lisp
simple.cert: algebra.cert
simple.cert: ../arithmetic/top.cert

gray-code.cert: gray-code.lisp
gray-code.cert: algebra.cert
gray-code.cert: simple.cert

sort.cert: sort.lisp
sort.cert: algebra.cert

merge-sort.cert: merge-sort.lisp
merge-sort.cert: algebra.cert
merge-sort.cert: sort.cert
merge-sort.cert: ../ordinals/e0-ordinal.cert

batcher-sort.cert: batcher-sort.lisp
batcher-sort.cert: merge-sort.cert
batcher-sort.cert: ../arithmetic/top.cert

bitonic-sort.cert: bitonic-sort.lisp
bitonic-sort.cert: algebra.cert
bitonic-sort.cert: simple.cert
bitonic-sort.cert: sort.cert
bitonic-sort.cert: batcher-sort.cert
bitonic-sort.cert: ../arithmetic/top.cert

prefix-sum.cert: prefix-sum.lisp
prefix-sum.cert: algebra.cert
prefix-sum.cert: simple.cert
prefix-sum.cert: ../arithmetic/top.cert

cla-adder.cert: cla-adder.lisp
cla-adder.cert: prefix-sum.cert
cla-adder.cert: algebra.cert
cla-adder.cert: ../arithmetic/top.cert
