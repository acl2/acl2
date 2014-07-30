#|$ACL2s-Preamble$;
;(ld "hacker-pkg.lsp")

(acl2::begin-book t :ttags ((defcode) (table-guard)));$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "hacker" :load-compiled-file :comp)
(include-book "defcode-macro" :ttags ((defcode)) :load-compiled-file :comp)
(include-book "defcode" :ttags ((defcode)) :load-compiled-file :comp)

(include-book "defstruct-parsing" :load-compiled-file :comp)
(include-book "raw" :ttags ((defcode)) :load-compiled-file :comp)

(include-book "rewrite-code" :load-compiled-file :comp)
(include-book "redefun" :ttags ((defcode)) :load-compiled-file :comp)

(include-book "bridge" :ttags ((defcode)) :load-compiled-file :comp)

(include-book "subsumption" :ttags ((defcode)) :load-compiled-file :comp)

(include-book "table-guard" :ttags ((defcode) (table-guard)) :load-compiled-file :comp)
