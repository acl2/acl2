; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

; (ld "Makefile.acl2")

;(include-book "../super-ihs/symbols")
;BZO what should we do with this?
(ld "../super-ihs/symbols.lsp")

;(include-book "../lists/list-exports")
(ld "../lists/list-exports.lsp")

;(include-book "../bags/bag-exports")
(ld "../bags/bag-exports.lsp")

(ld "../util/util-exports.lsp")

(defpkg "GACC"
;;  (remove-duplicates-eql   ;no longer necessary due to change in ACL2
   (union-eq

    ;; added by eric:
    '(acl2::clr loghead logtail logapp logext signed-byte-p unsigned-byte-p the-usb the-sb)

    `(,@*util-exports*
      ,@BAG::*exports*
      ,@LIST::*exports*
      ,@SYMBOLS::*base-symbols* ;try without this?
      ))
   ;)
   )