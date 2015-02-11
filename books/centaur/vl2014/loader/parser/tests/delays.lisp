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
(include-book "../delays")

(defparser-top vl-parse-delay3)

(defmacro test-delay3 (&key input rise fall high (successp 't))
  `(assert!
    (b* ((config *vl-default-loadconfig*)
         (tokens (make-test-tokens ,input))
         (pstate (make-vl-parsestate :warnings 'blah-warnings))
         ((mv erp val ?tokens (vl-parsestate pstate)) (vl-parse-delay3-top))
         ((when erp)
          (cw "ERP is ~x0.~%" erp)
          (and (equal pstate.warnings 'blah-warnings)
               (not ,successp))))
      (cw "VAL is ~x0.~%" val)
      (and ,successp
           (equal pstate.warnings 'blah-warnings)
           (vl-gatedelay-p val)
           (prog2$ (cw "Rise = ~x0.~%" (vl-pretty-expr (vl-gatedelay->rise val)))
                   (equal (vl-pretty-expr (vl-gatedelay->rise val)) ',rise))
           (prog2$ (cw "Fall = ~x0.~%" (vl-pretty-expr (vl-gatedelay->fall val)))
                   (equal (vl-pretty-expr (vl-gatedelay->fall val)) ',fall))
           (prog2$ (cw "High = ~x0.~%"
                       (and (vl-gatedelay->high val)
                            (vl-pretty-expr (vl-gatedelay->high val))))
                   (if (vl-gatedelay->high val)
                       (equal (vl-pretty-expr (vl-gatedelay->high val)) ',high)
                     (not ',high)))))))

(test-delay3 :input "#5"
             :rise 5
             :fall 5
             :high 5)

(test-delay3 :input "#2 0"
             :rise 2
             :fall 2
             :high 2)

(test-delay3 :input "#3.4"
             :rise (real "3.4")
             :fall (real "3.4")
             :high (real "3.4"))

(test-delay3 :input "#foo"
             :rise (id "foo")
             :fall (id "foo")
             :high (id "foo"))

(test-delay3 :input "#'sd15"
             :successp nil)

(test-delay3 :input "#('sd15)"
             :rise 15
             :fall 15
             :high 15)

(test-delay3 :input "#(5, foo)"
             :rise 5
             :fall (id "foo")
             :high nil)

(test-delay3 :input "#(5, 20, 55)"
             :rise 5
             :fall 20
             :high 55)

(test-delay3 :input "#(1:2:3, 4:5:6, 7:8:9)"
             :rise (:vl-mintypmax nil 1 2 3)
             :fall (:vl-mintypmax nil 4 5 6)
             :high (:vl-mintypmax nil 7 8 9))

(test-delay3 :input "#(1:2:3, 4:5:6)"
             :rise (:vl-mintypmax nil 1 2 3)
             :fall (:vl-mintypmax nil 4 5 6)
             :high nil)
