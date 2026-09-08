; ACL2 Quicklisp Socket Interface

;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "base")

(defttag :quicklisp.usocket)
; (depends-on "usocket-raw.lsp")
(include-raw "usocket-raw.lsp" :host-readtable t)
