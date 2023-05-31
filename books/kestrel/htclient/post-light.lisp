; HTCLIENT -- HTTP/HTTPS Client Library
;
; Copyright (C) 2022-2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HTCLIENT")

;; This book is just a lighter-weight variant of post.lisp.
;; And by lighter-weight, we mean fewer books are included.

(include-book "post-light-logic")
(include-book "quicklisp/dexador" :dir :system)
; (depends-on "post-light-raw.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag htclient)
(include-raw "post-light-raw.lsp"
             :host-readtable t)
