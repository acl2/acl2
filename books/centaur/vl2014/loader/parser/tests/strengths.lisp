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
(include-book "../strengths")

(defparser-top vl-parse-drive-strength-or-charge-strength)

(defmacro test-drive/charge-strength (&key input expect (successp 't))
  `(assert! (let ((tokens (make-test-tokens ,input))
                  (pstate (make-vl-parsestate))
                  (config *vl-default-loadconfig*))
              (mv-let (erp val tokens pstate)
                (vl-parse-drive-strength-or-charge-strength-top)
                (declare (ignore tokens))
                (if erp
                    (prog2$
                     (cw "ERP is ~x0.~%" erp)
                     (not ,successp))
                  (prog2$
                   (cw "VAL is ~x0.~%" val)
                   (debuggable-and ,successp
                                   (equal val ,expect)
                                   (not (vl-parsestate->warnings pstate)))))))))

(test-drive/charge-strength :input "(supply0, pull1)"
                            :expect (make-vl-gatestrength
                                     :zero :vl-supply
                                     :one :vl-pull))

(test-drive/charge-strength :input "(weak1, highz0)"
                            :expect (make-vl-gatestrength
                                     :zero :vl-highz
                                     :one :vl-weak))

(test-drive/charge-strength :input "(strong0, pull1)"
                            :expect (make-vl-gatestrength
                                     :zero :vl-strong
                                     :one :vl-pull))

(test-drive/charge-strength :input "(strong0, weak0)"
                            :successp nil)

(test-drive/charge-strength :input "(highz0, highz1)"
                            :successp nil)

(test-drive/charge-strength :input "(supply0, supply1, weak0, weak1)"
                            :successp nil)

(test-drive/charge-strength :input "(small)"
                            :expect :vl-small)

(test-drive/charge-strength :input "(medium)"
                            :expect :vl-medium)

(test-drive/charge-strength :input "(large)"
                            :expect :vl-large)

(test-drive/charge-strength :input "(huge)"
                            :successp nil)

(test-drive/charge-strength :input "(supply0)"
                            :successp nil)
