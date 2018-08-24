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
(include-book "../eventctrl")

(defparser-top vl-parse-delay-or-event-control)

(defmacro test-vl-parse-delay-or-eventcontrol (&key input expect (successp 't))
  `(assert!
    (b* ((tokens (make-test-tokens ,input))
         (pstate (make-vl-parsestate :warnings 'blah-warnings))
         (config *vl-default-loadconfig*)
         ((mv err val tokens (vl-parsestate pstate))
          (vl-parse-delay-or-event-control-top))
         ((when err)
          (not ,successp)))
      (debuggable-and ,successp
                      (not tokens)
                      (equal pstate.warnings 'blah-warnings)
                      (or (vl-delayoreventcontrol-p val)
                          (cw "Not a valid delayoreventcontrol: ~x0.~%" val))
                      (or (equal (vl-pretty-delayoreventcontrol val) ,expect)
                          (cw "Expected: ~x0~%Found:~x1~%"
                              ,expect
                              (vl-pretty-delayoreventcontrol val)))))))


(test-vl-parse-delay-or-eventcontrol :input "@(foo or bar or baz)"
                                     :expect '((:vl-noedge (id "foo"))
                                               (:vl-noedge (id "bar"))
                                               (:vl-noedge (id "baz"))))

(test-vl-parse-delay-or-eventcontrol :input "@(posedge foo)"
                                     :expect '((:vl-posedge (id "foo"))))

(test-vl-parse-delay-or-eventcontrol :input "@(negedge foo)"
                                     :expect '((:vl-negedge (id "foo"))))

(test-vl-parse-delay-or-eventcontrol :input "@*" :expect '(*))
(test-vl-parse-delay-or-eventcontrol :input "@(*)" :expect '(*))
(test-vl-parse-delay-or-eventcontrol :input "@( *)" :expect '(*))
(test-vl-parse-delay-or-eventcontrol :input "@(* )" :expect '(*))
(test-vl-parse-delay-or-eventcontrol :input "@( * )" :expect '(*))

(test-vl-parse-delay-or-eventcontrol :input "@(foo or bar or baz or *)"
                                     :successp nil)

(test-vl-parse-delay-or-eventcontrol :input "@(foo or bar or)"
                                     :successp nil)

(test-vl-parse-delay-or-eventcontrol :input "@(* or foo)"
                                     :successp nil)

(test-vl-parse-delay-or-eventcontrol :input "@(foo or posedge bar)"
                                     :expect '((:vl-noedge (id "foo"))
                                               (:vl-posedge (id "bar"))))

(test-vl-parse-delay-or-eventcontrol :input "@(* or posedge bar)"
                                     :successp nil)

(test-vl-parse-delay-or-eventcontrol :input "@(posedge bar or *)"
                                     :successp nil)

(test-vl-parse-delay-or-eventcontrol :input "@(posedge bar or)"
                                     :successp nil)


(test-vl-parse-delay-or-eventcontrol :input "@((posedge foo))"
                                     :expect '((:vl-posedge (id "foo"))))

(test-vl-parse-delay-or-eventcontrol :input "@((posedge foo) or ((posedge bar) or (posedge baz)))"
                                     :expect '((:vl-posedge (id "foo"))
                                               (:vl-posedge (id "bar"))
                                               (:vl-posedge (id "baz"))
                                               ))

(test-vl-parse-delay-or-eventcontrol
 :input "@((foo & bar) or (foo & baz))"
 :expect '((:vl-noedge (:vl-binary-bitand nil (id "foo") (id "bar")))
           (:vl-noedge (:vl-binary-bitand nil (id "foo") (id "baz")))))
