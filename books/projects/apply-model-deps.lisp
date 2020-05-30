;; Silly file to trick cert.pl into including the right books.

(in-package "ACL2")

#||
(depends-on "build/first-order-like-terms-and-out-arities.certdep" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "std/testing/eval" :dir :system)
||#
