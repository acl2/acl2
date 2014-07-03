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

(defmacro test-parse-port (&key input (successp 't) name expr)
  `(with-output
     :off summary
     (assert! (mv-let (erp val tokens warnings)
                (vl-parse-nonnull-port
                 :tokens (make-test-tokens ,input)
                 :warnings 'blah-warnings
                 :config *vl-default-loadconfig*)
                (if ,successp
                    (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                 (not erp))
                         (prog2$ (cw "Val: ~x0.~%" val)
                                 (vl-port-p val))
                         (prog2$ (cw "Name: ~x0.~%" (vl-port->name val))
                                 (equal (vl-port->name val) ',name))
                         (prog2$ (cw "Expr: ~x0.~%"
                                     (vl-pretty-expr (vl-port->expr val)))
                                 (equal (vl-pretty-expr (vl-port->expr val))
                                        ',expr))
                         (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                 (not tokens))
                         (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                 (equal warnings 'blah-warnings)))
                  ;; Otherwise, we expect it to fail.
                  (prog2$ (cw "Erp: ~x0.~%" erp)
                          erp))))))

(test-parse-port :input "a"
                 :name "a"
                 :expr (id "a"))

(test-parse-port :input "a[3:0]"
                 :name nil
                 :expr (:vl-partselect-colon nil (id "a") 3 0))

(test-parse-port :input "a[3]"
                 :name nil
                 :expr (:vl-index nil (id "a") 3))

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
                 :expr (:vl-partselect-colon nil (id "a") 3 0))

(test-parse-port :input ".foo(a[3])"
                 :name "foo"
                 :expr (:vl-index nil (id "a") 3))

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




(defun vl-pretty-maybe-exprlist (x)
  (if (atom x)
      nil
    (cons (if (car x)
              (vl-pretty-expr (car x))
            nil)
          (vl-pretty-maybe-exprlist (cdr x)))))





(defmacro test-parse-portlist (&key input (successp 't) names exprs)
  `(with-output
     :off summary
     (assert! (mv-let (erp val tokens warnings)
                (vl-parse-list-of-ports
                 :tokens (make-test-tokens ,input)
                 :warnings 'blah-warnings
                 :config *vl-default-loadconfig*)
                (if ,successp
                    (and (prog2$ (cw "Erp: ~x0.~%" erp)
                                 (not erp))
                         (prog2$ (cw "Val: ~x0.~%" val)
                                 (vl-portlist-p val))
                         (prog2$ (cw "Names: ~x0.~%" (vl-portlist->names val))
                                 (equal (vl-portlist->names val) ',names))
                         (prog2$ (cw "Exprs: ~x0.~%"
                                     (vl-pretty-maybe-exprlist (vl-portlist->exprs val)))
                                 (equal (vl-pretty-maybe-exprlist (vl-portlist->exprs val))
                                        ',exprs))
                         (prog2$ (cw "Tokens: ~x0.~%" tokens)
                                 (not tokens))
                         (prog2$ (cw "Warnings: ~x0.~%" warnings)
                                 (equal warnings 'blah-warnings)))
                  ;; Otherwise, we expect it to fail.
                  (prog2$ (cw "Erp: ~x0.~%" erp)
                          erp))))))

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
                     :exprs (nil (:vl-partselect-colon nil (id "b") 3 0)))

