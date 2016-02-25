#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "acl2s/package.lsp" :dir :system)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "std/portcullis" :dir :system)
; cert-flags: ? t :ttags :all
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Note: This book just gathers in one place all ACL2 books
;; that need to be certified for acl2s-mode to be used in emacs.
(in-package "ACL2")


(include-book "misc/expander" :dir :system)
(include-book "misc/bash" :dir :system)
(include-book "ordinals/lexicographic-ordering" :dir :system)
(include-book "hacking/all" :dir :system :ttags :all)
(include-book "hacking/evalable-ld-printing" :dir :system :ttags :all)
(include-book "make-event/inline-book" :dir :system)
(include-book "make-event/defconst-fast" :dir :system)
(include-book "misc/evalable-printing" :dir :system)
(include-book "misc/trace-star" :dir :system)
(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "data-structures/utilities" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "acl2s/cgen/top" :dir :system :ttags :all)


