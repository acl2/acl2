; ACL2 Quicklisp library for reading and writing ZIP files

;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "base")

(defttag :quicklisp.zippy)
; (depends-on "zippy-raw.lsp")
#-allegro ; see base-raw.lsp
(include-raw "zippy-raw.lsp" :host-readtable t)
