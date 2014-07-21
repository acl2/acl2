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
(include-book "../paramdecls")






(defun test-paramdecls-fn (params type localp range atts names exprs)
  (if (atom params)
      (and (atom names)
           (atom exprs))
    (debuggable-and
     (consp names)
     (consp exprs)
     (not (cw "Inspecting ~x0.~%" (car params)))
     (vl-paramdecl-p (car params))
     (equal type          (vl-paramdecl->type   (car params)))
     (equal localp        (vl-paramdecl->localp (car params)))
     (equal atts          (vl-paramdecl->atts   (car params)))
     (equal range         (and (vl-paramdecl->range (car params))
                               (vl-pretty-range (vl-paramdecl->range (car params)))))
     (equal (car names)   (vl-paramdecl->name   (car params)))
     (equal (car exprs)   (vl-pretty-expr (vl-paramdecl->expr (car params))))
     (test-paramdecls-fn (cdr params) type localp range atts (cdr names) (cdr exprs)))))

(defmacro test-parse-param-declaration
  (&key input type localp range atts names exprs (successp 't))
  `(assert!
    (let ((tokens (make-test-tokens ,input))
          (warnings 'blah-warnings)
          (config   *vl-default-loadconfig*))
      (mv-let (erp val tokens warnings)
        (vl-parse-param-or-localparam-declaration ',atts
                                                  '(:vl-kwd-parameter
                                                    :vl-kwd-localparam))
        (declare (ignore tokens))
        (if erp
            (prog2$ (cw "ERP is ~x0.~%" erp)
                    (and (equal warnings 'blah-warnings)
                         (not ,successp)))
          (prog2$ (cw "VAL is ~x0.~%" val)
                  (and ,successp
                       (equal warnings 'blah-warnings)
                       (test-paramdecls-fn val ',type ',localp ',range
                                           ',atts ',names ',exprs))))))))

(test-parse-param-declaration :input "parameter a = 1"
                              :names ("a")
                              :exprs (1)
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter a = 1 : 2 : 3"
                              :names ("a")
                              :exprs ((:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "localparam a = 1 : 2 : 3"
                              :names ("a")
                              :exprs ((:vl-mintypmax nil 1 2 3))
                              :localp t
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter signed a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-signed
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter signed [7:8] a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range (range 7 8)
                              :type :vl-signed
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter [7:8] a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range (range 7 8)
                              :type :vl-plain
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter integer a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-integer
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter real a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-real
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter time a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-time
                              :atts (("some") ("atts")))

(test-parse-param-declaration :input "parameter realtime a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :type :vl-realtime
                              :atts (("some") ("atts")))

;; can only use ranges on signed and plain
(test-parse-param-declaration :input "parameter time [7:0] a = 1, b = 1 : 2 : 3"
                              :successp nil)

(test-parse-param-declaration :input "localparam realtime a = 1, b = 1 : 2 : 3"
                              :names ("a" "b")
                              :exprs (1   (:vl-mintypmax nil 1 2 3))
                              :range nil
                              :localp t
                              :type :vl-realtime
                              :atts (("some") ("atts")))

