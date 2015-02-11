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
(include-book "expressions")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))



; Dimensions and ranges are introduced with the following rules.
;
; dimension ::= '[' dimension_constant_expression ':' dimension_constant_expression ']'
;
; range ::= '[' msb_constant_expression ':' lsb_constant_expression ']'
;
; But these are all just aliases to constant_expression, which we treat as
; regular expressions.  Note also that the names above in "range" are
; misleading, since no particular order is required.  Moreover, we do not make
; any distinction between dimensions and ranges.  That is, in either case, we
; call vl-parse-range and produce vl-range-p objects.

(defparser vl-parse-range ()
  :result (vl-range-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-lbrack))
       (msb := (vl-parse-expression))
       (:= (vl-match-token :vl-colon))
       (lsb := (vl-parse-expression))
       (:= (vl-match-token :vl-rbrack))
       (return (make-vl-range :msb msb
                              :lsb lsb))))

(defparser vl-parse-0+-ranges ()
  ;; Note: assumes brackets denote subsequent ranges to be matched, and as a
  ;; result it may indeed cause an error.
  :result (vl-rangelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
       (unless (vl-is-token? :vl-lbrack)
         (return nil))
       (first := (vl-parse-range))
       (rest := (vl-parse-0+-ranges))
       (return (cons first rest))))

