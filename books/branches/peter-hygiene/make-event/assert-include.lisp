; Here we make sure that we can include assert, which is particularly
; interesting in light of the comment before the last form in assert.lisp about
; the expansion checking that the latest command is (exit-boot-strap-mode).

(in-package "ACL2")

(deflabel assert-include-label)

(include-book "assert")
