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
(include-book "../ports")

;; BOZO more unit tests!

#||
(trace-parser vl-parse-port-reference-fn)
(trace-parser vl-parse-1+-port-references-separated-by-commas-fn)
(trace-parser vl-parse-port-expression-fn)
(trace-parser vl-parse-nonnull-port-fn)
||#

(defparser-top vl-parse-nonnull-port)

(defmacro test-parse-port (&key input (successp 't) name expr)
  `(with-output
     :off summary
     (assert! (b* ((tokens (make-test-tokens ,input))
                   (config *vl-default-loadconfig*)
                   (pstate (make-vl-parsestate :warnings 'blah-warnings))
                   ((mv erp val tokens (vl-parsestate pstate))
                    (vl-parse-nonnull-port-top))
                   ((unless ,successp)
                    (cw "Expect error.  Actual error: ~x0.~%" erp)
                    erp))
                (and (prog2$ (cw "Erp: ~x0.~%" erp)
                             (not erp))
                     (prog2$ (cw "Val: ~x0.~%" val)
                             (vl-regularport-p val))
                     (prog2$ (cw "Name: ~x0.~%" (vl-regularport->name val))
                             (equal (vl-regularport->name val) ',name))
                     (prog2$ (cw "Expr: ~x0.~%" (vl-pretty-expr (vl-regularport->expr val)))
                             (or (equal (vl-pretty-expr (vl-regularport->expr val))
                                        ',expr)
                                 (cw "Expected ~x0~%" ',expr)))
                     (prog2$ (cw "Tokens: ~x0.~%" tokens)
                             (not tokens))
                     (prog2$ (cw "Warnings: ~x0.~%" pstate.warnings)
                             (equal pstate.warnings 'blah-warnings)))))))

(test-parse-port :input "a"
                 :name "a"
                 :expr (id "a"))

(test-parse-port :input "a[3:0]"
                 :name nil
                 :expr (:index nil "a" nil (:colon 3 0)))

(test-parse-port :input "a[3]"
                 :name nil
                 :expr (:index nil "a" (3) nil))

(test-parse-port :input "{a, b, c}"
                 :name nil
                 :expr (:vl-concat nil
                                   (id "a")
                                   (id "b")
                                   (id "c")))

(test-parse-port :input ".foo(bar)"
                 :name "foo"
                 :expr (id "bar"))

(test-parse-port :input ".foo(a[3:0])"
                 :name "foo"
                 :expr (:index nil "a" nil (:colon 3 0)))

(test-parse-port :input ".foo(a[3])"
                 :name "foo"
                 :expr (:index nil "a" (3) nil))

(test-parse-port :input ".foo({a, b, c})"
                 :name "foo"
                 :expr (:vl-concat nil
                                   (id "a")
                                   (id "b")
                                   (id "c")))

(test-parse-port :input ".(a[3:0])"
                 :successp nil)

(test-parse-port :input ".(a[3])"
                 :successp nil)

(test-parse-port :input ".foo(a[3 +: 0])"
                 :successp nil)

(test-parse-port :input ".foo(a[3 -: 0])"
                 :successp nil)


(defprojection vl-regularportlist->exprs ((x vl-regularportlist-p))
  :parents (vl-portlist-p)
  :nil-preservingp t
  (vl-regularport->expr x))




(defparser-top vl-parse-module-port-list-top)

(defmacro test-parse-portlist (&key input (successp 't) names exprs)
  `(with-output
     :off summary
     (assert! (b* ((tokens (make-test-tokens ,input))
                   (config *vl-default-loadconfig*)
                   (pstate (make-vl-parsestate :warnings 'blah-warnings))
                   ((mv erp val tokens (vl-parsestate pstate))
                    (vl-parse-module-port-list-top-top))
                   (val (vl-nonansi-ports->ports val))
                   ((unless ,successp)
                    (cw "Expect failure.  Actual Erp: ~x0.~%" erp)
                    erp))
                (and (prog2$ (cw "Erp: ~x0.~%" erp)
                             (not erp))
                     (prog2$ (cw "Val: ~x0.~%" val)
                             (vl-regularportlist-p val))
                     (prog2$ (cw "Names: ~x0.~%" (vl-portlist->names val))
                             (equal (vl-portlist->names val) ',names))
                     (prog2$ (cw "Exprs: ~x0.~%"
                                 (vl-pretty-maybe-exprlist (vl-regularportlist->exprs val)))
                             (equal (vl-pretty-maybe-exprlist (vl-regularportlist->exprs val))
                                    ',exprs))
                     (prog2$ (cw "Tokens: ~x0.~%" tokens)
                             (not tokens))
                     (prog2$ (cw "Warnings: ~x0.~%" pstate.warnings)
                             (equal pstate.warnings 'blah-warnings)))))))
#||
(trace-parser vl-parse-module-port-list-top-fn)
(trace-parser vl-parse-0+-attribute-instances-fn)
(trace-parser vl-parse-ansi-port-declaration-fn)
(trace$ vl-port-starts-ansi-port-list-p)
(trace-parser vl-parse-1+-ansi-port-declarations-fn)
(trace-parser vl-parse-1+-ports-separated-by-commas-fn)
||#

(test-parse-portlist :input "()"
                     :names nil
                     :exprs nil)

(test-parse-portlist :input "(a)"
                     :names ("a")
                     :exprs ((id "a")))

(test-parse-portlist :input "(a,b)"
                     :names ("a"      "b")
                     :exprs ((id "a") (id "b")))

(test-parse-portlist :input "(a,,b)"
                     :names ("a"      nil "b")
                     :exprs ((id "a") nil (id "b")))

(test-parse-portlist :input "(,)"
                     :names (nil nil)
                     :exprs (nil nil))

(test-parse-portlist :input "(,,,,,)"
                     :names (nil nil nil nil nil nil)
                     :exprs (nil nil nil nil nil nil))

(test-parse-portlist :input "(a,,,b)"
                     :names ("a" nil nil "b")
                     :exprs ((id "a") nil nil (id "b")))

(test-parse-portlist :input "(,a)"
                     :names (nil "a")
                     :exprs (nil (id "a")))

(test-parse-portlist :input "(a,)"
                     :names ("a" nil)
                     :exprs ((id "a") nil))

(test-parse-portlist :input "(.a(), b[3:0])"
                     :names ("a" nil)
                     :exprs (nil (:index nil "b" nil (:colon 3 0))))

