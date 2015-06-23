; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "../lexer/tokens")
(include-book "../../mlib/print-warnings")

(defsection vl-report-parse-error

; This is a truly horrific use of memoization to avoid printing the same errors
; multiple times.
;
; We put this in its own file so that the rest of the parser doesn't have to
; depend on the writer.

  (defund vl-actually-report-parse-error (err context)
    (declare (xargs :guard (and (vl-warning-p err)
                                (stringp context))))
    (if (not err)
        nil
      (vl-cw-ps-seq
       (vl-ps-update-autowrap-col 68)
       (vl-print-warning err)
       (vl-println context)
       (vl-println ""))))

  (memoize 'vl-actually-report-parse-error)

  (defund vl-report-parse-error (err tokens)
    (declare (xargs :guard (and (vl-warning-p err)
                                (vl-tokenlist-p tokens))))
    (if (not err)
        nil
      (let ((context (cat "  Near: \""
                          (vl-tokenlist->string-with-spaces
                           (take (min 4 (len tokens))
                                 (list-fix tokens)))
                          (if (> (len tokens) 4) "..." "")
                          "\"")))
        (vl-actually-report-parse-error
         ;; Have to hons the arguments for the memoization to work correctly.
         ;; Fortunately they're usually very small.
         (hons-copy err)
         (hons-copy context))))))
