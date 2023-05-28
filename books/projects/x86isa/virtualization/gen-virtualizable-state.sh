#!/bin/sh

rlwrap ../../../saved_acl2 <<EOF
(ld "setup-linux.lisp")
(include-book "virtualization/top")
(dump-virtualizable-state "state.virt" x86 state)
EOF
