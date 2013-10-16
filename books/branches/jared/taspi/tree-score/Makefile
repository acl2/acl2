include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
INHIBIT = (assign inhibit-output-lst (list (quote proof-tree) (quote prove) (quote observation) (quote event) (quote expansion)))

BOOKS = costs pscores fitch-scoring efficient-pscores-help \
	efficient-pscores min-length ambig-score \
	circle-scoring opt-pairwise

costs.cert: costs.lisp
costs.cert: ../code/sequences/seqs.cert

pscores.cert: pscores.lisp
pscores.cert: costs.cert

fitch-scoring.cert: fitch-scoring.lisp
fitch-scoring.cert: costs.cert

efficient-pscores-help.cert: efficient-pscores-help.lisp

efficient-pscores.cert: efficient-pscores.lisp
efficient-pscores.cert: ../code/gen-helper/extra.cert
efficient-pscores.cert: efficient-pscores-help.cert

min-length.cert: min-length.lisp
min-length.cert: efficient-pscores.cert

ambig-score.cert: ambig-score.lisp
ambig-score.cert: min-length.cert

circle-scoring.cert: circle-scoring.lisp
circle-scoring.cert: min-length.cert
circle-scoring.cert: ../code/gen-trees/top.cert

opt-pairwise.cert: opt-pairwise.lisp
opt-pairwise.cert: ../code/sequences/align.cert
opt-pairwise.cert: ../code/gen-helper/extra.cert