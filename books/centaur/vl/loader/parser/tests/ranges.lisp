; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "base")
(include-book "../ranges")

(defmacro test-range (&key input range (successp 't))
  `(assert! (let ((tokens (make-test-tokens ,input)))
              (mv-let (erp val tokens warnings)
                (vl-parse-range :tokens tokens
                                :warnings nil
                                :config *vl-default-loadconfig*)
                (declare (ignore tokens))
                (if erp
                    (prog2$ (cw "ERP is ~x0.~%" erp)
                            (not ,successp))
                  (prog2$ (cw "VAL is ~x0.~%" val)
                          (and ,successp
                               (vl-range-p val)
                               (not warnings)
                               (equal ',range (vl-pretty-range val)))))))))

(test-range :input "[7:0]"
            :range (range 7 0))

(test-range :input "[3:6]"
            :range (range 3 6))

(test-range :input "[7 : 0]"
            :range (range 7 0))

(test-range :input "[foo : bar]"
            :range (range (id "foo") (id "bar")))

(test-range :input "[foo : ]"
            :successp nil)

(test-range :input "[foo]"
            :successp nil)