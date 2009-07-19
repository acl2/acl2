ACL2 = ../../../../../saved_acl2
include ../../../../Makefile-generic

# From make dependencies:

all.cert: all.lisp
all.cert: hacker.cert
all.cert: defcode-macro.cert
all.cert: defcode.cert
all.cert: defstruct-parsing.cert
all.cert: raw.cert
all.cert: rewrite-code.cert
all.cert: redefun.cert
all.cert: bridge.cert
all.cert: subsumption.cert
all.cert: table-guard.cert
all.cert: all.acl2

bridge.cert: bridge.lisp
bridge.cert: defcode.cert
bridge.cert: bridge.acl2
bridge.cert: defcode.cert
bridge.cert: hacker-pkg.lsp

defcode.cert: defcode.lisp
defcode.cert: hacker.cert
defcode.cert: defcode-macro.cert
defcode.cert: defcode.acl2
defcode.cert: hacker.cert

defcode-macro.cert: defcode-macro.lisp
defcode-macro.cert: hacker.cert
defcode-macro.cert: defcode-macro.acl2
defcode-macro.cert: hacker.cert

defstruct-parsing.cert: defstruct-parsing.lisp
defstruct-parsing.cert: defstruct-parsing.acl2
defstruct-parsing.cert: hacker-pkg.lsp

hacker.cert: hacker.lisp
hacker.cert: hacker.acl2
hacker.cert: hacker-pkg.lsp

raw.cert: raw.lisp
raw.cert: defcode.cert
raw.cert: defstruct-parsing.cert
raw.cert: raw.acl2
raw.cert: defcode.cert
raw.cert: hacker-pkg.lsp

redefun.cert: redefun.lisp
redefun.cert: defcode.cert
redefun.cert: rewrite-code.cert
redefun.cert: redefun.acl2
redefun.cert: defcode.cert

rewrite-code.cert: rewrite-code.lisp
rewrite-code.cert: rewrite-code.acl2

subsumption.cert: subsumption.lisp
subsumption.cert: defcode.cert
subsumption.cert: subsumption.acl2
subsumption.cert: defcode.cert
subsumption.cert: hacker-pkg.lsp

table-guard.cert: table-guard.lisp
table-guard.cert: defcode.cert
table-guard.cert: redefun.cert
table-guard.cert: table-guard.acl2
table-guard.cert: defcode.cert
table-guard.cert: redefun.cert
