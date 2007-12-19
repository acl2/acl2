# The following variable should represent the ACL2 source directory.  It and
# ACL2 are the only variables in this Makefile that may need to be edited.
ACL2_SYSTEM_BOOKS ?= ../../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 ?= $(ACL2_SYSTEM_BOOKS)/../saved_acl2

BOOKS = syn-pkg syntax syntax-extensions auxilary

# Dependencies:

syn-pkg.cert: syn-pkg.lisp
syn-pkg.cert: syn-pkg.acl2

syntax.cert: syntax.lisp
syntax.cert: syntax.acl2
syntax.acl2: syntax-extensions.cert

syntax-extensions.cert: syntax-extensions.lisp
syntax-extensions.cert: syntax-extensions.acl2
syntax-extensions.acl2: auxilary.cert
syntax-extensions.acl2: syn-pkg.cert
syntax-extensions.acl2: ../lists/list-top.cert

auxilary.cert: auxilary.lisp
auxilary.cert: auxilary.acl2
auxilary.acl2: ../symbol-fns/symbol-fns.cert
