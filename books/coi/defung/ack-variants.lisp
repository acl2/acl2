; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "ACL2")

(include-book "defung")

;; -----------------------------------------
;; A non executable model
;; -----------------------------------------

(def::ung ack0 (x y)
  (declare (xargs :non-executable t))
  (if (= x 0) (1+ y)
    (if (= y 0) (ack0 (1- x) 1)
      (ack0 (1- x) (ack0 x (1- y))))))

#|
ACL2 !>(time$ (ack0 3 10))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 0.00 seconds realtime, 0.00 seconds runtime
; (1,296 bytes allocated).

ACL2 Error in TOP-LEVEL:  ACL2 cannot ev the call of undefined function
|ARB-iACK0-INDEX| on argument list:

(3 10)

To debug see :DOC print-gv, see :DOC trace, and see :DOC wet.
|#

;; -----------------------------------------
;; Evaluation via ev-call
;; -----------------------------------------

(def::ung ack1 (x y)
  (if (= x 0) (1+ y)
    (if (= y 0) (ack1 (1- x) 1)
      (ack1 (1- x) (ack1 x (1- y))))))

#|
ACL2 !>(time$ (ack1 3 7))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 23.46 seconds realtime, 23.45 seconds runtime
; (1,120 bytes allocated).
1021
|#

;; -----------------------------------------
;; Evaluation without indexed computation
;; -----------------------------------------

(def::ung ack2 (x y)
  (declare (xargs :signature ((natp natp) natp)))
  (if (= x 0) (1+ y)
    (if (= y 0) (ack2 (1- x) 1)
      (ack2 (1- x) (ack2 x (1- y))))))

#|
ACL2 !>(time$ (ack2 3 7))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 1.91 seconds realtime, 1.91 seconds runtime
; (1,120 bytes allocated).
|#

#|
ACL2 !>(time$ (ack2 3 8))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 15.34 seconds realtime, 15.34 seconds runtime
; (1,120 bytes allocated).
2045
|#
#|
ACL2 !>(time$ (ack2-domain 3 8))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 15.32 seconds realtime, 15.31 seconds runtime
; (1,120 bytes allocated).
T
|#

;; -----------------------------------------
;; Evaluation with indexed computation
;; -----------------------------------------

(def::ung ack3 (x y)
  (declare (xargs :signature ((natp natp) natp)))
  (if (= x 0) (1+ y)
    (if (= y 0) (ack3 (1- x) 1)
      (ack3 (1- x) (ack3 x (1- y))))))

#|
ACL2 !>(time$ (ack3 3 8))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 0.02 seconds realtime, 0.02 seconds runtime
; (1,120 bytes allocated).
2045
|#
#|
ACL2 !>(time$ (ack3 3 11))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 1.25 seconds realtime, 1.25 seconds runtime
; (1,120 bytes allocated).
16381
|#

;; -----------------------------------------
;; :program mode evaluation
;; -----------------------------------------

(defun ack4 (x y)
  (declare (xargs :mode :program))
  (if (= x 0) (1+ y)
    (if (= y 0) (ack4 (1- x) 1)
      (ack4 (1- x) (ack4 x (1- y))))))

#|
ACL2 !>(time$ (ack4 3 11))
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 0.61 seconds realtime, 0.61 seconds runtime
; (1,120 bytes allocated).
16381
|#