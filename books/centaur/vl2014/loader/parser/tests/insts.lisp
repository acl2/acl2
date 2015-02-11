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
(include-book "../insts")

(defparser-top vl-parse-udp-or-module-instantiation
  :guard (vl-atts-p atts))

(defmacro test-parse-modinst-args (&key input (successp 't) expect remainder)
  `(with-output
     :off summary
     (assert! (b* ((config *vl-default-loadconfig*)
                   (tokens (make-test-tokens ,input))
                   (pstate (make-vl-parsestate :warnings 'warnings))
                   (atts   nil)
                   ((mv erp val ?tokens (vl-parsestate pstate))
                    (vl-parse-udp-or-module-instantiation-top atts))
                   ((unless ,successp)
                    ;; We expect it to fail
                    (cw "Expect an error.  Error is: ~x0.~%" erp)
                    erp))
                ;; Expect success.
                (and (prog2$ (cw "Erp: ~x0.~%" erp)
                             (not erp))
                     (prog2$ (cw "VAL: ~x0.~%" val)
                             (and (vl-modinstlist-p val)
                                  (equal (len val) 1)))
                     (let* ((inst (first val))
                            (args (vl-modinst->portargs inst)))
                       (and
                        (prog2$ (cw "ARGS: ~x0.~%" (vl-pretty-arguments args))
                                (equal (vl-pretty-arguments args) ',expect))
                        (prog2$ (cw "Atts: ~x0.~%" (vl-modinst->atts inst))
                                (equal (vl-modinst->atts inst) nil))
                        (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                (equal tokens ,remainder))
                        (prog2$ (cw "Warnings: ~x0.~%" pstate.warnings)
                                (equal pstate.warnings 'warnings)))))))))

(test-parse-modinst-args
 :input "foo inst (a, b, c);"
 :expect (:PLAINARGS ((ID "a") (ID "b") (ID "c"))))

(test-parse-modinst-args
 :input "foo inst ();"
 :expect (:PLAINARGS ()))

(test-parse-modinst-args
 :input "foo inst (a,);"
 :expect (:PLAINARGS ((ID "a") :blank)))

(test-parse-modinst-args
 :input "foo inst (,a);"
 :expect (:PLAINARGS (:blank (ID "a"))))

(test-parse-modinst-args
 :input "foo inst (,);"
 :expect (:PLAINARGS (:blank :blank)))

(test-parse-modinst-args
 :input "foo inst (,,);"
 :expect (:PLAINARGS (:blank :blank :blank)))

(test-parse-modinst-args
 :input "foo inst (,,,);"
 :expect (:PLAINARGS (:blank :blank :blank :blank)))

(test-parse-modinst-args
 :input "foo inst (a,,c);"
 :expect (:PLAINARGS ((ID "a") :blank (ID "c"))))

(test-parse-modinst-args
 :input "foo inst (, a, , c);"
 :expect (:PLAINARGS (:blank (ID "a") :blank (ID "c"))))

(test-parse-modinst-args
 :input "foo inst (.a(1), .b(2));"
 :expect (:NAMEDARGS (("a" <-- 1) ("b" <-- 2))))

(test-parse-modinst-args
 :input "foo inst (.a(1), .b(2), );"
 :successp nil)

(test-parse-modinst-args
 :input "foo inst (.a(1), );"
 :successp nil)

(test-parse-modinst-args
 :input "foo inst (, .a(1));"
 :successp nil)
