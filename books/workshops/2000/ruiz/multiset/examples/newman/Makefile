include ../../../../../../Makefile-generic


# Dependencies:

abstract-proofs.cert: abstract-proofs.lisp
abstract-proofs.cert: ../../../../../../data-structures/structures.cert
abstract-proofs.cert: ../../../../../../ordinals/e0-ordinal.cert

confluence-v0.cert: confluence-v0.lisp
confluence-v0.cert: abstract-proofs.cert

confluence.cert: confluence.lisp
confluence.cert: abstract-proofs.cert

local-confluence.cert: local-confluence.lisp
local-confluence.cert: confluence.cert
local-confluence.cert: newman.cert

newman.cert: newman.lisp
newman.cert: ../../defmul.cert
newman.cert: abstract-proofs.cert
newman.cert: ../../../../../../ordinals/e0-ordinal.cert
