(in-package "ACL2")
(include-book "base")

(defttag :quicklisp.zippy)
; (depends-on "zippy-raw.lsp")
#-allegro ; see base-raw.lsp
(include-raw "zippy-raw.lsp" :host-readtable t)
