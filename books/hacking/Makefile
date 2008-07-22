include ../Makefile-generic

# from "make dependencies" (seem to be accurate):

all.cert: all.lisp
all.cert: hacker.cert
all.cert: defstruct-parsing.cert
all.cert: rewrite-code.cert
all.cert: defcode.cert
all.cert: raw.cert
all.cert: redefun.cert
all.cert: bridge.cert
all.cert: subsumption.cert
all.cert: table-guard.cert
all.cert: all.acl2
all.cert: hacker-pkg.lsp
all.cert: rewrite-code-pkg.lsp

bridge.cert: bridge.lisp
bridge.cert: bridge.acl2
bridge.cert: hacker-pkg.lsp

defcode.cert: defcode.lisp
defcode.cert: progn-bang-enh.cert
defcode.cert: defcode.acl2
defcode.cert: hacker.cert
defcode.cert: hacker-pkg.lsp

defstruct-parsing.cert: defstruct-parsing.lisp
defstruct-parsing.cert: defstruct-parsing.acl2
defstruct-parsing.cert: hacker-pkg.lsp

hacker.cert: hacker.lisp
hacker.cert: hacker.acl2
hacker.cert: hacker-pkg.lsp

progn-bang-enh.cert: progn-bang-enh.lisp
progn-bang-enh.cert: progn-bang-enh.acl2

raw.cert: raw.lisp
raw.cert: raw.acl2
raw.cert: defstruct-parsing.cert
raw.cert: hacker-pkg.lsp

redefun.cert: redefun.lisp
redefun.cert: redefun.acl2
redefun.cert: hacker-pkg.lsp

rewrite-code.cert: rewrite-code.lisp
rewrite-code.cert: rewrite-code.acl2
rewrite-code.cert: rewrite-code-pkg.lsp

subsumption.cert: subsumption.lisp
subsumption.cert: subsumption.acl2
subsumption.cert: hacker-pkg.lsp

table-guard.cert: table-guard.lisp
table-guard.cert: table-guard.acl2
table-guard.cert: defcode.cert
table-guard.cert: rewrite-code.cert
table-guard.cert: redefun.cert
table-guard.cert: hacker-pkg.lsp
