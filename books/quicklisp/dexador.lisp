; ACL2 Quicklisp http client library

;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;

(in-package "ACL2")
(include-book "base")

(defttag :quicklisp.dexador)
; (depends-on "dexador-raw.lsp")
(include-raw "dexador-raw.lsp" :host-readtable t)
