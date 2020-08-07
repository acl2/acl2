; Oracle Timing
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "oracle-time")

(defun fib (n)
  (if (zp n)
      1
    (if (equal n 1)
        1
      (+ (fib (- n 1))
         (fib (- n 2))))))

; [Jared] Fib seems to execute really slowly on CMUCL, so use smaller numbers
; for it.
(defconst *fib-small* #+cmucl 25 #-cmucl 30)
(defconst *fib-med*   #+cmucl 28 #-cmucl 35)
(defconst *fib-large* #+cmucl 30 #-cmucl 38)

(comp t) ; especially important for Allegro CL

;; Test of basic forms
(make-event
 (b* (((mv time1 bytes1 ans1 state) (oracle-time (fib *fib-small*)))
      ((mv time2 bytes2 ans2 state) (oracle-time (fib *fib-med*) :ret foo))
      ((mv time3 bytes3 ans3 state) (oracle-time (fib *fib-large*) :ret (mv foo)))
      (- (cw "(fib *fib-small*): ~x0 sec, ~x1 bytes~%" time1 bytes1))
      (- (cw "(fib *fib-med*): ~x0 sec, ~x1 bytes~%" time2 bytes2))
      (- (cw "(fib *fib-large*): ~x0 sec, ~x1 bytes~%" time3 bytes3))
      ((unless (and (< time1 time2)
                    (< time2 time3)))
       (er soft 'oracle-time
           "Fib test timings don't seem plausible."))
      ((unless (and (equal ans1 (fib *fib-small*))
                    (equal ans2 (fib *fib-med*))
                    (equal ans3 (fib *fib-large*))))
       (er soft 'oracle-time
           "Fib results aren't right.")))
   (value '(value-triple :success))))

;; Test of a form that takes state.
(make-event
 (b* (((mv ?time ?bytes ans state)
       (oracle-time (mv (fib 6) state) :ret (mv ans state)))
      ((unless (equal ans (fib 6)))
       (er soft 'oracle-time "Wrong answer for (mv (fib 6) state).")))
   (value '(value-triple :success))))

;; Test of a form that takes state, return values swapped
(make-event
 (b* (((mv ?time ?bytes state ans)
       (oracle-time (mv state (fib 6)) :ret (mv state ans)))
      ((unless (equal ans (fib 6)))
       (er soft 'oracle-time "Wrong answer for (mv state (fib 6)).")))
   (value '(value-triple :success))))

;; Test of a form that just returns state and nothing else
(make-event
 (b* (((mv ?time ?bytes state)
       (oracle-time (f-put-global ':foo (fib 7) state) :ret state))
      ((unless (equal (f-get-global ':foo state) (fib 7)))
       (er soft 'oracle-time "Wrong answer for (assign :foo (fib 7)).")))
   (value '(value-triple :success))))

;; Basic test of nested forms
(make-event
 (b* (((mv time-total
           ?bytes-total
           time38 ?bytes38 ans38
           time35 ?bytes35 ans35
           state)
       (oracle-time
        (b* (((mv time38 bytes38 ans38 state) (oracle-time (fib *fib-large*)))
             ((mv time35 bytes35 ans35 state) (oracle-time (fib *fib-med*))))
          (mv time38 bytes38 ans38 time35 bytes35 ans35 state))
        :ret (mv time38 bytes38 ans38 time35 bytes35 ans35 state)))
      ((unless (eql ans38 (fib *fib-large*)))
       (er soft 'oracle-time "Wrong answer for (fib *fib-large*).~%"))
      ((unless (eql ans35 (fib *fib-med*)))
       (er soft 'oracle-time "Wrong answer for (fib *fib-med*).~%"))
      ((unless (and (< time35 time38)
                    (< time38 time-total)))
       (er soft 'oracle-time "Implausible timings for nested test.~%")))
   (cw "time35 ~x0~%" time35)
   (cw "time38 ~x0~%" time38)
   (cw "time-total ~x0~%" time-total)
   (value '(value-triple :success))))
