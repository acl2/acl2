; Decompression Utility Wrapper
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "decompress-bytes-logic")
(include-book "quicklisp/zippy" :dir :system :ttags :all)
; (depends-on "decompress-bytes-raw.lsp")

; Matt K. mod 2/2/2024: Avoid error, ``Package "3BZ" not found''.
; cert_param: (non-allegro)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag decompress-bytes)
(include-raw "decompress-bytes-raw.lsp"
             :host-readtable t)
