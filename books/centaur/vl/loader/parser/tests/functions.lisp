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
(include-book "../functions")

(defund taskport-summary (x)
  (declare (xargs :guard (vl-portdecl-p x)))
  (b* (((vl-portdecl x) x))
    (list x.name
          x.dir
          (vl-pretty-datatype x.type))))

(defprojection taskportlist-summary (x)
  (taskport-summary x)
  :guard (vl-portdecllist-p x))

(defparser-top vl-parse-taskport-list)

(defmacro test-parse-taskports (&key input (successp 't) summary)
  `(with-output
     :off summary
     (assert! (b* ((tokens (make-test-tokens ,input))
                   (config (change-vl-loadconfig *vl-default-loadconfig*
                                                 :edition :verilog-2005))
                   (pstate (make-vl-parsestate :warnings 'blah-warnings))
                   ((mv erp val tokens (vl-parsestate pstate))
                    (vl-parse-taskport-list-top))
                   ((unless ,successp)
                    (cw "Expected failure.~%")
                    (cw "Actual erp: ~x0.~%" erp)
                    erp)
                   ((when erp)
                    (cw "Expected success, but ERP is ~x0~%" erp))
                   (spec-summary ',summary)
                   (impl-summary (taskportlist-summary val)))
                (and (progn$
                      (cw "Spec-Summary: ~x0~%" spec-summary)
                      (cw "Impl-Summary: ~x0~%" impl-summary)
                      (equal spec-summary impl-summary))
                     (progn$
                      (cw "Tokens: ~x0~%" tokens)
                      (not tokens))
                     (progn$
                      (cw "Warnings: ~x0~%" pstate.warnings)
                      (equal pstate.warnings 'blah-warnings)))))))


(test-parse-taskports :input ""
                      :successp nil)

(test-parse-taskports :input "foo"
                      :successp nil)

(test-parse-taskports :input "input a"
                      :summary (("a" :vl-input (:vl-logic unsigned))))

(test-parse-taskports :input "input a, b"
                      :summary (("a" :vl-input (:vl-logic unsigned))
                                ("b" :vl-input (:vl-logic unsigned))))

(test-parse-taskports :input "input a, b, c, d"
                      :summary (("a" :vl-input (:vl-logic unsigned))
                                ("b" :vl-input (:vl-logic unsigned))
                                ("c" :vl-input (:vl-logic unsigned))
                                ("d" :vl-input (:vl-logic unsigned))))

;; bozo we're currently ignoring reg.  does it mean anything?
(test-parse-taskports :input "input reg a"
                      :summary (("a" :vl-input (:vl-logic unsigned))))

(test-parse-taskports :input "input reg a, b"
                      :summary (("a" :vl-input (:vl-logic unsigned))
                                ("b" :vl-input (:vl-logic unsigned))))

(test-parse-taskports :input "input signed a"
                      :summary (("a" :vl-input (:vl-logic signed))))

(test-parse-taskports :input "input signed a, b"
                      :summary (("a" :vl-input (:vl-logic signed))
                                ("b" :vl-input (:vl-logic signed))))


(test-parse-taskports :input "input [3:0] a"
                      :summary (("a" :vl-input (:vl-logic unsigned (:range 3 0)))))

(test-parse-taskports :input "input [3:0] a, b"
                      :summary (("a" :vl-input (:vl-logic unsigned (:range 3 0)))
                                ("b" :vl-input (:vl-logic unsigned (:range 3 0)))))

(test-parse-taskports :input "input [3:0] a, b, \c , d"
                      :summary (("a" :vl-input (:vl-logic unsigned (:range 3 0)))
                                ("b" :vl-input (:vl-logic unsigned (:range 3 0)))
                                ("c" :vl-input (:vl-logic unsigned (:range 3 0)))
                                ("d" :vl-input (:vl-logic unsigned (:range 3 0)))
                                ))

(test-parse-taskports :input "input signed [3:0] a"
                      :summary (("a" :vl-input (:vl-logic signed (:range 3 0)))))

(test-parse-taskports :input "input signed [3:0] a, b"
                      :summary (("a" :vl-input (:vl-logic signed (:range 3 0)))
                                ("b" :vl-input (:vl-logic signed (:range 3 0)))))

(test-parse-taskports :input "input reg [3:0] a"
                      :summary (("a" :vl-input (:vl-logic unsigned (:range 3 0)))))

(test-parse-taskports :input "input reg signed [3:0] a"
                      :summary (("a" :vl-input (:vl-logic signed (:range 3 0)))))

(test-parse-taskports :input "input integer a"
                      :summary (("a" :vl-input (:vl-integer signed))))

(test-parse-taskports :input "input real a"
                      :summary (("a" :vl-input (:vl-real unsigned))))

(test-parse-taskports :input "input time a"
                      :summary (("a" :vl-input (:vl-time unsigned))))

(test-parse-taskports :input "input realtime a"
                      :summary (("a" :vl-input (:vl-realtime unsigned))))


;; reg must come before signed
(test-parse-taskports :input "input signed reg a"
                      :successp nil)

;; signed not okay with int/real/time/realtime
(test-parse-taskports :input "input integer signed a" :successp nil)
(test-parse-taskports :input "input signed integer a" :successp nil)
(test-parse-taskports :input "input real signed a" :successp nil)
(test-parse-taskports :input "input signed real a" :successp nil)
(test-parse-taskports :input "input integer signed a" :successp nil)
(test-parse-taskports :input "input signed integer a" :successp nil)
(test-parse-taskports :input "input integer signed a" :successp nil)
(test-parse-taskports :input "input signed integer a" :successp nil)
(test-parse-taskports :input "input time signed a" :successp nil)
(test-parse-taskports :input "input signed time a" :successp nil)
(test-parse-taskports :input "input time signed a" :successp nil)
(test-parse-taskports :input "input signed time a" :successp nil)
(test-parse-taskports :input "input realtime signed a" :successp nil)
(test-parse-taskports :input "input signed realtime a" :successp nil)
(test-parse-taskports :input "input realtime signed a" :successp nil)
(test-parse-taskports :input "input signed realtime a" :successp nil)

;; reg not okay with int/real/time/realtime
(test-parse-taskports :input "input integer reg a" :successp nil)
(test-parse-taskports :input "input reg integer a" :successp nil)
(test-parse-taskports :input "input real reg a" :successp nil)
(test-parse-taskports :input "input reg real a" :successp nil)
(test-parse-taskports :input "input integer reg a" :successp nil)
(test-parse-taskports :input "input reg integer a" :successp nil)
(test-parse-taskports :input "input integer reg a" :successp nil)
(test-parse-taskports :input "input reg integer a" :successp nil)
(test-parse-taskports :input "input time reg a" :successp nil)
(test-parse-taskports :input "input reg time a" :successp nil)
(test-parse-taskports :input "input time reg a" :successp nil)
(test-parse-taskports :input "input reg time a" :successp nil)
(test-parse-taskports :input "input realtime reg a" :successp nil)
(test-parse-taskports :input "input reg realtime a" :successp nil)
(test-parse-taskports :input "input realtime reg a" :successp nil)
(test-parse-taskports :input "input reg realtime a" :successp nil)

;; range not okay with int/real/time/realtime
(test-parse-taskports :input "input integer [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] integer a" :successp nil)
(test-parse-taskports :input "input real [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] real a" :successp nil)
(test-parse-taskports :input "input integer [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] integer a" :successp nil)
(test-parse-taskports :input "input integer [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] integer a" :successp nil)
(test-parse-taskports :input "input time [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] time a" :successp nil)
(test-parse-taskports :input "input time [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] time a" :successp nil)
(test-parse-taskports :input "input realtime [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] realtime a" :successp nil)
(test-parse-taskports :input "input realtime [3:0] a" :successp nil)
(test-parse-taskports :input "input [3:0] realtime a" :successp nil)
