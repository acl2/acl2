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
(include-book "base")
(include-book "../statements")

;; BOZO no tests at all... :(

#||

(defparser-top vl-parse-state)

(let ((tokens (make-test-tokens "foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "assign foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "force foo = bar ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "deassign foo ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "release foo ;")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "(* taco = delicious *) begin end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin deassign foo ; end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))

(let ((tokens (make-test-tokens "begin foo = bar ; end")))
  (mv-let (erp val tokens)
          (vl-parse-statement tokens)
          (list (list :erp erp)
                (list :val val)
                (list :tokens tokens))))


(defmacro test-parse-integer-declaration (&key input atts names arrdims initvals (successp 't))
    `(assert! (let ((tokens (make-test-tokens ,input)))
                (mv-let (erp val tokens)
                        (vl-parse-integer-declaration ',atts tokens)
                        (declare (ignore tokens))
                        (if erp
                            (prog2$ (cw "ERP is ~x0.~%" erp)
                                    (not ,successp))
                          (prog2$ (cw "VAL is ~x0.~%" val)
                                  (and ,successp
                                       (test-vardecls-fn val :vl-integer ',atts
                                                         ',names ',arrdims ',initvals))))))))

||#

