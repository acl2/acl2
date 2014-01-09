;; Silly file to trick cert.pl into including the right books.

(in-package "ACL2")

#||
; Seems to be needed; see support/make-consistency-test.lisp.
(include-book "data-structures/set-theory" :dir :system)
||#
