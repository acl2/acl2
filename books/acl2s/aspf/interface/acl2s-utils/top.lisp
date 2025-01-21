; (depends-on "additions.lsp")
; (depends-on "extras.lsp")
(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
(include-book "itest-ithm")
(include-book "../top")

(defttag :acl2s-interface)
(include-raw "additions.lsp")
(include-raw "extras.lsp")

(include-book "extras-doc")
