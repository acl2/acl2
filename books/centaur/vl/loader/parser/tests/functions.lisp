; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "base")
(include-book "../functions")

(defund taskport-summary (x)
  (declare (xargs :guard (vl-taskport-p x)))
  (b* (((vl-taskport x) x))
    (list x.name x.dir x.type (vl-pretty-maybe-range x.range))))

(defprojection taskportlist-summary (x)
  (taskport-summary x)
  :guard (vl-taskportlist-p x))

(defmacro test-parse-taskports (&key input (successp 't) summary)
  `(with-output
     :off summary
     (assert! (b* (((mv erp val tokens warnings)
                    (vl-parse-taskport-list
                     :tokens (make-test-tokens ,input)
                     :warnings 'blah-warnings
                     :config *vl-default-loadconfig*))

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
                      (cw "Warnings: ~x0~%" warnings)
                      (equal warnings 'blah-warnings)))))))


(test-parse-taskports :input ""
                      :successp nil)

(test-parse-taskports :input "foo"
                      :successp nil)

(test-parse-taskports :input "input a"
                      :summary (("a" :vl-input :vl-unsigned (no-range))))

(test-parse-taskports :input "input a, b"
                      :summary (("a" :vl-input :vl-unsigned (no-range))
                                ("b" :vl-input :vl-unsigned (no-range))))

(test-parse-taskports :input "input a, b, c, d"
                      :summary (("a" :vl-input :vl-unsigned (no-range))
                                ("b" :vl-input :vl-unsigned (no-range))
                                ("c" :vl-input :vl-unsigned (no-range))
                                ("d" :vl-input :vl-unsigned (no-range))))

;; bozo we're currently ignoring reg.  does it mean anything?
(test-parse-taskports :input "input reg a"
                      :summary (("a" :vl-input :vl-unsigned (no-range))))

(test-parse-taskports :input "input reg a, b"
                      :summary (("a" :vl-input :vl-unsigned (no-range))
                                ("b" :vl-input :vl-unsigned (no-range))))

(test-parse-taskports :input "input signed a"
                      :summary (("a" :vl-input :vl-signed (no-range))))

(test-parse-taskports :input "input signed a, b"
                      :summary (("a" :vl-input :vl-signed (no-range))
                                ("b" :vl-input :vl-signed (no-range))))


(test-parse-taskports :input "input [3:0] a"
                      :summary (("a" :vl-input :vl-unsigned (range 3 0))))

(test-parse-taskports :input "input [3:0] a, b"
                      :summary (("a" :vl-input :vl-unsigned (range 3 0))
                                ("b" :vl-input :vl-unsigned (range 3 0))))

(test-parse-taskports :input "input [3:0] a, b, \c , d"
                      :summary (("a" :vl-input :vl-unsigned (range 3 0))
                                ("b" :vl-input :vl-unsigned (range 3 0))
                                ("c" :vl-input :vl-unsigned (range 3 0))
                                ("d" :vl-input :vl-unsigned (range 3 0))
                                ))

(test-parse-taskports :input "input signed [3:0] a"
                      :summary (("a" :vl-input :vl-signed (range 3 0))))

(test-parse-taskports :input "input signed [3:0] a, b"
                      :summary (("a" :vl-input :vl-signed (range 3 0))
                                ("b" :vl-input :vl-signed (range 3 0))))

(test-parse-taskports :input "input reg [3:0] a"
                      :summary (("a" :vl-input :vl-unsigned (range 3 0))))

(test-parse-taskports :input "input reg signed [3:0] a"
                      :summary (("a" :vl-input :vl-signed (range 3 0))))

(test-parse-taskports :input "input integer a"
                      :summary (("a" :vl-input :vl-integer (no-range))))

(test-parse-taskports :input "input real a"
                      :summary (("a" :vl-input :vl-real (no-range))))

(test-parse-taskports :input "input time a"
                      :summary (("a" :vl-input :vl-time (no-range))))

(test-parse-taskports :input "input realtime a"
                      :summary (("a" :vl-input :vl-realtime (no-range))))


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
