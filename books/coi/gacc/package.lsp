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

(include-book "../lists/portcullis")
(include-book "../bags/portcullis")
(include-book "../util/portcullis")

;; [Jared] bozo doesn't quite exactly follow best practices but it's kind of
;; obscure and not clear that the super-ihs library should include this
;; symbols stuff in all of its books.
(include-book "../super-ihs/symbols")

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
