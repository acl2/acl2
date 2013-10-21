include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS =  seqs p-inform align

seqs.cert: seqs.lisp
seqs.cert: ../gen-trees/top.cert
seqs.cert: $(ACL2_SYSTEM_BOOKS)/misc/hons-help2.cert

p-inform.cert: p-inform.lisp
p-inform.cert: seqs.cert

align.cert: align.lisp
