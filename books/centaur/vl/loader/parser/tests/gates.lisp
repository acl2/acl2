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
(include-book "../gates")

; vl-parse-gate-instantiation -> gateinstlist


(define vl-pretty-gatestrength ((x vl-gatestrength-p))
  (b* (((vl-gatestrength x) x))
    (list 'strength x.one x.zero)))

(define vl-pretty-delay ((x vl-gatedelay-p))
  (b* (((vl-gatedelay x) x))
    (list 'delay
          (vl-pretty-expr x.rise)
          (vl-pretty-expr x.fall)
          (and x.high (vl-pretty-expr x.high)))))

(define vl-pretty-gateinst ((x vl-gateinst-p))
  (b* (((vl-gateinst x) x))
    (list* x.type
           x.name
           (vl-pretty-plainarg-list x.args)
           (append (if x.range
                       (list (vl-pretty-range x.range))
                     nil)
                   (if x.strength
                       (list (vl-pretty-gatestrength x.strength))
                     nil)
                   (if x.delay
                       (list (vl-pretty-delay x.delay))
                     nil)
                   (if x.atts
                       (list (cons 'atts (vl-pretty-atts x.atts)))
                     nil)))))

(defprojection vl-pretty-gateinstlist ((x vl-gateinstlist-p))
  (vl-pretty-gateinst x))

(defparser-top vl-parse-gate-instantiation
  :guard (vl-atts-p atts))

(defmacro test-parse-gateinst (&key input (successp 't) atts expect)
  `(with-output
     :off summary
     (assert! (b* ((tokens (make-test-tokens ,input))
                   (pstate (make-vl-parsestate :warnings nil))
                   (config *vl-default-loadconfig*)
                   ((mv erp val ?tokens ?pstate) (vl-parse-gate-instantiation-top ,atts))
                   (- (cw "ERP ~x0.~%" erp))
                   (- (cw "VAL ~x0.~%" val))
                   (- (cw "Pretty val: ~x0.~%" (vl-pretty-gateinstlist val)))
                   (- (cw "Expect    : ~x0.~%" ',expect))
                   ;(- (cw "TOKENS ~x0.~%" tokens))
                   ;(- (cw "WARNINGS ~x0.~%" warnings))
                   ((when ,successp)
                    (and (not erp)
                         (vl-gateinstlist-p val)
                         (equal ',expect (vl-pretty-gateinstlist val)))))
                ;; Otherwise we expect it to fail
                erp))))



;; basic and tests

(test-parse-gateinst :input "" :successp nil)
(test-parse-gateinst :input "and" :successp nil)
(test-parse-gateinst :input "and(" :successp nil)
(test-parse-gateinst :input "and();" :successp nil)
(test-parse-gateinst :input "and(o);" :successp nil) ;; not enough args

(test-parse-gateinst :input "and(o, a);" ;; These surprisingly are actually allowed
                     :expect ((:vl-and nil ((id "o") (id "a")))))

(test-parse-gateinst :input "and(o, a, b);"
                     :expect ((:vl-and nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "and(o, a, b)" :successp nil) ; missing semi
(test-parse-gateinst :input "and(o, a, b;" :successp nil) ; missing close
(test-parse-gateinst :input "and(o, a, b"  :successp nil) ; missing close and semi
(test-parse-gateinst :input "and(o, a b);" :successp nil) ; missing comma

(test-parse-gateinst :input "and foo (o, a);"
                     :expect ((:vl-and "foo" ((id "o") (id "a")))))

(test-parse-gateinst :input "and foo (o, a, b);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "and foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")))))


(test-parse-gateinst :input "and [3:0] (o, a, b);" :successp nil) ;; range without name

(test-parse-gateinst :input "and foo [3:0] (o, a, b);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b")) (:range 3 0))))

(test-parse-gateinst :input "and foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-and "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))


(test-parse-gateinst :input "and #2 foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "and #blah foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay (id "blah") (id "blah") (id "blah")))))

(test-parse-gateinst :input "and #2.5 foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay (real "2.5") (real "2.5") (real "2.5")))))

(test-parse-gateinst :input "and #3+4 foo (o, a, b, c);" ;; not a valid delay_value, needs parens for exprs
                     :successp nil)

(test-parse-gateinst :input "and #(3+4) foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay (:vl-binary-plus nil 3 4)
                                                                                          (:vl-binary-plus nil 3 4)
                                                                                          (:vl-binary-plus nil 3 4)))))

(test-parse-gateinst :input "and #(1:2:3) foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay (:vl-mintypmax nil 1 2 3)
                                                                                          (:vl-mintypmax nil 1 2 3)
                                                                                          (:vl-mintypmax nil 1 2 3)))))

(test-parse-gateinst :input "and #(2) foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "and #(2,3) foo (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))))

(test-parse-gateinst :input "and #(2,3,4) foo (o, a, b, c);" :successp nil) ;; only 2 delays on an and gate


(test-parse-gateinst :input "and #2 foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-and "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "and #(2) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-and "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "and #(2, 3) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))
                              (:vl-and "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 3 nil))))


(test-parse-gateinst :input "and #2 foo [3:0] (o, a, b, c);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))))

(test-parse-gateinst :input "and #2 foo [3:0] (o, a, b, c), bar [1:0] (m, n, o, p);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-and "bar" ((id "m") (id "n") (id "o") (id "p")) (:range 1 0) (delay 2 2 2))))

(test-parse-gateinst :input "and #2 foo [3:0] (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-and "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "and (supply1, pull0) #2 foo (o, a, b);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))

(test-parse-gateinst :input "and (pull0, supply1) #2 foo (o, a, b);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))

(test-parse-gateinst :input "and #2 (supply1, supply0) foo (o, a, b);"
                     :successp nil) ;; strength/delay in wrong order

(test-parse-gateinst :input "and (supply1, supply1) foo (o, a, b);"
                     :successp nil) ;; both strength1s instead of strength0

(test-parse-gateinst :input "and (pull0, supply1) #2 foo (o, a, b), bar [3:0] (m, n, o);"
                     :expect ((:vl-and "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))
                              (:vl-and "bar" ((id "m") (id "n") (id "o"))
                               (:range 3 0)
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))





;; copied and tests for xnor

(test-parse-gateinst :input "" :successp nil)
(test-parse-gateinst :input "xnor" :successp nil)
(test-parse-gateinst :input "xnor(" :successp nil)
(test-parse-gateinst :input "xnor();" :successp nil)
(test-parse-gateinst :input "xnor(o);" :successp nil) ;; not enough args

(test-parse-gateinst :input "xnor(o, a);" ;; These surprisingly are actually allowed
                     :expect ((:vl-xnor nil ((id "o") (id "a")))))

(test-parse-gateinst :input "xnor(o, a, b);"
                     :expect ((:vl-xnor nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "xnor(o, a, b)" :successp nil) ; missing semi
(test-parse-gateinst :input "xnor(o, a, b;" :successp nil) ; missing close
(test-parse-gateinst :input "xnor(o, a, b"  :successp nil) ; missing close xnor semi
(test-parse-gateinst :input "xnor(o, a b);" :successp nil) ; missing comma

(test-parse-gateinst :input "xnor foo (o, a);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a")))))

(test-parse-gateinst :input "xnor foo (o, a, b);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "xnor foo (o, a, b, c);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")))))


(test-parse-gateinst :input "xnor [3:0] (o, a, b);" :successp nil) ;; range without name

(test-parse-gateinst :input "xnor foo [3:0] (o, a, b);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b")) (:range 3 0))))

(test-parse-gateinst :input "xnor foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))


(test-parse-gateinst :input "xnor #2 foo (o, a, b, c);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "xnor #(2) foo (o, a, b, c);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "xnor #(2,3) foo (o, a, b, c);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))))

(test-parse-gateinst :input "xnor #(2,3,4) foo (o, a, b, c);" :successp nil) ;; only 2 delays on an xnor gate


(test-parse-gateinst :input "xnor #2 foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "xnor #(2) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "xnor #(2, 3) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 3 nil))))


(test-parse-gateinst :input "xnor #2 foo [3:0] (o, a, b, c);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))))

(test-parse-gateinst :input "xnor #2 foo [3:0] (o, a, b, c), bar [1:0] (m, n, o, p);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "o") (id "p")) (:range 1 0) (delay 2 2 2))))

(test-parse-gateinst :input "xnor #2 foo [3:0] (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "xnor (supply1, pull0) #2 foo (o, a, b);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))

(test-parse-gateinst :input "xnor (pull0, supply1) #2 foo (o, a, b);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))

(test-parse-gateinst :input "xnor #2 (supply1, supply0) foo (o, a, b);"
                     :successp nil) ;; strength/delay in wrong order

(test-parse-gateinst :input "xnor (supply1, supply1) foo (o, a, b);"
                     :successp nil) ;; both strength1s instead of strength0

(test-parse-gateinst :input "xnor (pull0, supply1) #2 foo (o, a, b), bar [3:0] (m, n, o);"
                     :expect ((:vl-xnor "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))
                              (:vl-xnor "bar" ((id "m") (id "n") (id "o"))
                               (:range 3 0)
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))




;; basic tests for other logic gates


(test-parse-gateinst :input "or foo (o, a);"
                     :expect ((:vl-or "foo" ((id "o") (id "a")))))

(test-parse-gateinst :input "or foo (o, a, b);"
                     :expect ((:vl-or "foo" ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "or foo (o, a, b, c);"
                     :expect ((:vl-or "foo" ((id "o") (id "a") (id "b") (id "c")))))


(test-parse-gateinst :input "xor foo (o, a);"
                     :expect ((:vl-xor "foo" ((id "o") (id "a")))))

(test-parse-gateinst :input "xor foo (o, a, b);"
                     :expect ((:vl-xor "foo" ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "xor foo (o, a, b, c);"
                     :expect ((:vl-xor "foo" ((id "o") (id "a") (id "b") (id "c")))))


(test-parse-gateinst :input "nand foo (o, a);"
                     :expect ((:vl-nand "foo" ((id "o") (id "a")))))

(test-parse-gateinst :input "nand foo (o, a, b);"
                     :expect ((:vl-nand "foo" ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "nand foo (o, a, b, c);"
                     :expect ((:vl-nand "foo" ((id "o") (id "a") (id "b") (id "c")))))


(test-parse-gateinst :input "nor foo (o, a);"
                     :expect ((:vl-nor "foo" ((id "o") (id "a")))))

(test-parse-gateinst :input "nor foo (o, a, b);"
                     :expect ((:vl-nor "foo" ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "nor foo (o, a, b, c);"
                     :expect ((:vl-nor "foo" ((id "o") (id "a") (id "b") (id "c")))))





;; buf tests

(test-parse-gateinst :input "buf" :successp nil)
(test-parse-gateinst :input "buf(" :successp nil)
(test-parse-gateinst :input "buf();" :successp nil)
(test-parse-gateinst :input "buf(o);" :successp nil) ;; not enough args

(test-parse-gateinst :input "buf(o, a);"
                     :expect ((:vl-buf nil ((id "o") (id "a")))))

(test-parse-gateinst :input "buf(o, a, b);"
                     :expect ((:vl-buf nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "buf foo (o, a, b, c);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")))))

(test-parse-gateinst :input "buf(o, a, b)" :successp nil) ; missing semi
(test-parse-gateinst :input "buf(o, a, b;" :successp nil) ; missing close
(test-parse-gateinst :input "buf(o, a, b"  :successp nil) ; missing close buf semi
(test-parse-gateinst :input "buf(o, a b);" :successp nil) ; missing comma

(test-parse-gateinst :input "buf foo [3:0] (o, a, b);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b")) (:range 3 0))))

(test-parse-gateinst :input "buf foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-buf "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))


(test-parse-gateinst :input "buf #2 foo (o, a, b, c);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "buf #(2) foo (o, a, b, c);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "buf #(2,3) foo (o, a, b, c);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))))

(test-parse-gateinst :input "buf #(2,3,4) foo (o, a, b, c);" :successp nil) ;; only 2 delays on an buf gate


(test-parse-gateinst :input "buf #2 foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-buf "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "buf #(2) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-buf "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "buf #(2, 3) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))
                              (:vl-buf "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 3 nil))))

(test-parse-gateinst :input "buf #2 foo [3:0] (o, a, b, c);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))))

(test-parse-gateinst :input "buf #2 foo [3:0] (o, a, b, c), bar [1:0] (m, n, o, p);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-buf "bar" ((id "m") (id "n") (id "o") (id "p")) (:range 1 0) (delay 2 2 2))))

(test-parse-gateinst :input "buf #2 foo [3:0] (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-buf "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-buf "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))


;; same tests for not gates

(test-parse-gateinst :input "not" :successp nil)
(test-parse-gateinst :input "not(" :successp nil)
(test-parse-gateinst :input "not();" :successp nil)
(test-parse-gateinst :input "not(o);" :successp nil) ;; not enough args

(test-parse-gateinst :input "not(o, a);"
                     :expect ((:vl-not nil ((id "o") (id "a")))))

(test-parse-gateinst :input "not(o, a, b);"
                     :expect ((:vl-not nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "not foo (o, a, b, c);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")))))

(test-parse-gateinst :input "not(o, a, b)" :successp nil) ; missing semi
(test-parse-gateinst :input "not(o, a, b;" :successp nil) ; missing close
(test-parse-gateinst :input "not(o, a, b"  :successp nil) ; missing close not semi
(test-parse-gateinst :input "not(o, a b);" :successp nil) ; missing comma

(test-parse-gateinst :input "not foo [3:0] (o, a, b);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b")) (:range 3 0))))

(test-parse-gateinst :input "not foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-not "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))


(test-parse-gateinst :input "not #2 foo (o, a, b, c);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "not #(2) foo (o, a, b, c);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))))

(test-parse-gateinst :input "not #(2,3) foo (o, a, b, c);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))))

(test-parse-gateinst :input "not #(2,3,4) foo (o, a, b, c);" :successp nil) ;; only 2 delays on an not gate


(test-parse-gateinst :input "not #2 foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-not "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "not #(2) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 2 2))
                              (:vl-not "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))

(test-parse-gateinst :input "not #(2, 3) foo (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 nil))
                              (:vl-not "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 3 nil))))

(test-parse-gateinst :input "not #2 foo [3:0] (o, a, b, c);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))))

(test-parse-gateinst :input "not #2 foo [3:0] (o, a, b, c), bar [1:0] (m, n, o, p);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-not "bar" ((id "m") (id "n") (id "o") (id "p")) (:range 1 0) (delay 2 2 2))))

(test-parse-gateinst :input "not #2 foo [3:0] (o, a, b, c), bar (m, n, o, p);"
                     :expect ((:vl-not "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0) (delay 2 2 2))
                              (:vl-not "bar" ((id "m") (id "n") (id "o") (id "p")) (delay 2 2 2))))



;; bufif1 tests

(test-parse-gateinst :input "bufif1" :successp nil)
(test-parse-gateinst :input "bufif1(" :successp nil)
(test-parse-gateinst :input "bufif1();" :successp nil)
(test-parse-gateinst :input "bufif1(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "bufif1(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "bufif1(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "bufif1(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "bufif1(o, a, b);"
                     :expect ((:vl-bufif1 nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "bufif1(o, a, b)" :successp nil) ; missing semi
(test-parse-gateinst :input "bufif1(o, a, b;" :successp nil) ; missing close
(test-parse-gateinst :input "bufif1(o, a, b"  :successp nil) ; missing close bufif1 semi
(test-parse-gateinst :input "bufif1(o, a b);" :successp nil) ; missing comma

(test-parse-gateinst :input "bufif1 foo [3:0] (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (:range 3 0))))

(test-parse-gateinst :input "bufif1 foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))

;; they can have delay3s instead of just delay2s

(test-parse-gateinst :input "bufif1 #2 foo (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #(2) foo (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #(2,3) foo (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 3 nil))))

(test-parse-gateinst :input "bufif1 #(2,3,4) foo (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "bufif1 #(2,3,4,5) foo (o, a, b);"
                     :successp nil)

(test-parse-gateinst :input "bufif1 #2 foo (o, a, b), bar (m, n, o);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 2 2))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "o")) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #(2) foo (o, a, b), bar (m, n, o);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 2 2))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "o")) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #(2, 3) foo (o, a, b), bar (m, n, o);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 3 nil))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "o")) (delay 2 3 nil))))

(test-parse-gateinst :input "bufif1 #2 foo [3:0] (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (:range 3 0) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #2 foo [3:0] (o, a, b), bar [1:0] (m, n, o);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (:range 3 0) (delay 2 2 2))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "o")) (:range 1 0) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #2 foo [3:0] (o, a, b), bar (m, n, o);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b")) (:range 3 0) (delay 2 2 2))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "o")) (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 (supply1, pull0) #2 foo (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 (pull0, supply1) #2 foo (o, a, b);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))

(test-parse-gateinst :input "bufif1 #2 (supply1, supply0) foo (o, a, b);"
                     :successp nil) ;; strength/delay in wrong order

(test-parse-gateinst :input "bufif1 (supply1, supply1) foo (o, a, b);"
                     :successp nil) ;; both strength1s instead of strength0

(test-parse-gateinst :input "bufif1 (pull0, supply1) #2 foo (o, a, b), bar [3:0] (m, n, o);"
                     :expect ((:vl-bufif1 "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))
                              (:vl-bufif1 "bar" ((id "m") (id "n") (id "o"))
                               (:range 3 0)
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))


;; very limited tests of other bufif style gates


(test-parse-gateinst :input "bufif0(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "bufif0(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "bufif0(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "bufif0(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "bufif0 #(2,3,4) foo (o, a, b);"
                     :expect ((:vl-bufif0 "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "bufif0 foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-bufif0 "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-bufif0 "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))

(test-parse-gateinst :input "bufif0 (pull0, supply1) #2 foo (o, a, b);"
                     :expect ((:vl-bufif0 "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))



(test-parse-gateinst :input "notif0(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "notif0(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "notif0(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "notif0(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "notif0 #(2,3,4) foo (o, a, b);"
                     :expect ((:vl-notif0 "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "notif0 foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-notif0 "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-notif0 "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))

(test-parse-gateinst :input "notif0 (pull0, supply1) #2 foo (o, a, b);"
                     :expect ((:vl-notif0 "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))


(test-parse-gateinst :input "notif1(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "notif1(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "notif1(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "notif1(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "notif1 #(2,3,4) foo (o, a, b);"
                     :expect ((:vl-notif1 "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "notif1 foo [3:0] (o, a, b), bar[0:4] (m, n, p);"
                     :expect ((:vl-notif1 "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-notif1 "bar" ((id "m") (id "n") (id "p")) (:range 0 4))))

(test-parse-gateinst :input "notif1 (pull0, supply1) #2 foo (o, a, b);"
                     :expect ((:vl-notif1 "foo" ((id "o") (id "a") (id "b"))
                               (strength :vl-supply :vl-pull)
                               (delay 2 2 2))))






; very limited tests of cmos gates
; cmos supports delay3
; cmos doesn't support strengths

(test-parse-gateinst :input "cmos(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "cmos(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "cmos(o, a, b);" :successp nil) ;; not enough args
(test-parse-gateinst :input "cmos(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "cmos(o, a, b, c);"
                     :expect ((:vl-cmos nil ((id "o") (id "a") (id "b") (id "c")))))

(test-parse-gateinst :input "cmos #(2,3,4) foo (o, a, b, c);"
                     :expect ((:vl-cmos "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 4))))

(test-parse-gateinst :input "cmos foo [3:0] (o, a, b, c), bar[0:4] (m, n, o, p);"
                     :expect ((:vl-cmos "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0))
                              (:vl-cmos "bar" ((id "m") (id "n") (id "o") (id "p")) (:range 0 4))))

(test-parse-gateinst :input "cmos (pull0, supply1) foo (o, a, b, c);"
                     :successp nil)


;; same for rcmos

(test-parse-gateinst :input "rcmos(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rcmos(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rcmos(o, a, b);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rcmos(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "rcmos(o, a, b, c);"
                     :expect ((:vl-rcmos nil ((id "o") (id "a") (id "b") (id "c")))))

(test-parse-gateinst :input "rcmos #(2,3,4) foo (o, a, b, c);"
                     :expect ((:vl-rcmos "foo" ((id "o") (id "a") (id "b") (id "c")) (delay 2 3 4))))

(test-parse-gateinst :input "rcmos foo [3:0] (o, a, b, c), bar[0:4] (m, n, o, p);"
                     :expect ((:vl-rcmos "foo" ((id "o") (id "a") (id "b") (id "c")) (:range 3 0))
                              (:vl-rcmos "bar" ((id "m") (id "n") (id "o") (id "p")) (:range 0 4))))

(test-parse-gateinst :input "rcmos (pull0, supply1) foo (o, a, b, c);"
                     :successp nil)



; nmos/pmos gates

(test-parse-gateinst :input "pmos(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "pmos(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "pmos(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "pmos(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "pmos(o, a, b);"
                     :expect ((:vl-pmos nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "pmos #(2,3,4) foo (o, a, b);" ;; support delay3
                     :expect ((:vl-pmos "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "pmos foo [3:0] (o, a, b), bar[0:4] (m, n, o);"
                     :expect ((:vl-pmos "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-pmos "bar" ((id "m") (id "n") (id "o")) (:range 0 4))))

(test-parse-gateinst :input "pmos (pull0, supply1) foo (o, a, b);" ;; no strengths on mos gates
                     :successp nil)


(test-parse-gateinst :input "rpmos(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rpmos(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rpmos(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "rpmos(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "rpmos(o, a, b);"
                     :expect ((:vl-rpmos nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "rpmos #(2,3,4) foo (o, a, b);" ;; support delay3
                     :expect ((:vl-rpmos "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "rpmos foo [3:0] (o, a, b), bar[0:4] (m, n, o);"
                     :expect ((:vl-rpmos "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-rpmos "bar" ((id "m") (id "n") (id "o")) (:range 0 4))))

(test-parse-gateinst :input "rpmos (pull0, supply1) foo (o, a, b);" ;; no strengths on mos gates
                     :successp nil)


(test-parse-gateinst :input "nmos(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "nmos(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "nmos(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "nmos(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "nmos(o, a, b);"
                     :expect ((:vl-nmos nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "nmos #(2,3,4) foo (o, a, b);" ;; support delay3
                     :expect ((:vl-nmos "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "nmos foo [3:0] (o, a, b), bar[0:4] (m, n, o);"
                     :expect ((:vl-nmos "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-nmos "bar" ((id "m") (id "n") (id "o")) (:range 0 4))))

(test-parse-gateinst :input "nmos (pull0, supply1) foo (o, a, b);" ;; no strengths on mos gates
                     :successp nil)


(test-parse-gateinst :input "rnmos(o);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rnmos(o, a);" :successp nil) ;; not enough args
(test-parse-gateinst :input "rnmos(o, a, b, c);" :successp nil) ;; too many args
(test-parse-gateinst :input "rnmos(o, a, b, c, d);" :successp nil) ;; too many args

(test-parse-gateinst :input "rnmos(o, a, b);"
                     :expect ((:vl-rnmos nil ((id "o") (id "a") (id "b")))))

(test-parse-gateinst :input "rnmos #(2,3,4) foo (o, a, b);" ;; support delay3
                     :expect ((:vl-rnmos "foo" ((id "o") (id "a") (id "b")) (delay 2 3 4))))

(test-parse-gateinst :input "rnmos foo [3:0] (o, a, b), bar[0:4] (m, n, o);"
                     :expect ((:vl-rnmos "foo" ((id "o") (id "a") (id "b")) (:range 3 0))
                              (:vl-rnmos "bar" ((id "m") (id "n") (id "o")) (:range 0 4))))

(test-parse-gateinst :input "rnmos (pull0, supply1) foo (o, a, b);" ;; no strengths on mos gates
                     :successp nil)



;; bozo could use more tests -- tran gates, pull gates

