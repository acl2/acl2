include ../../../../Makefile-generic


# List books explicitly to avoid vhdl-acl2, which is not certifiable (has forms
# that are not embedded event forms).
BOOKS = acl2-transl generates-functions generates-theorems utils

-include Makefile-deps

vhdl-acl2.cert: vhdl-acl2.lisp
vhdl-acl2.cert: acl2-transl.cert
