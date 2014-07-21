; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; Provides a measure and efficient termination check
;; for functions that recur by counting up to a limit.

(defmacro count-up-meas (x max)
  `(nfix (- (nfix ,max) (nfix ,x))))

(defmacro count-up-guard (x max)
  `(let ((x ,x) (max ,max))
     (and (natp x) (natp max) (<= x max))))

(defmacro count-up-done (x max)
  `(mbe :logic (zp (- (nfix ,max) (nfix ,x)))
        :exec (= ,x ,max)))

(defmacro count-past-guard (x max)
  `(and (natp ,x) (natp ,max)))

(defmacro count-past-done (x max)
  `(mbe :logic (zp (- (nfix ,max) (nfix ,x)))
        :exec (>= ,x ,max)))

(defun-inline lnfix (x)
  (declare (xargs :guard (natp x)))
  (mbe :logic (nfix x) :exec x))

(defmacro nincr (x)
  `(1+ (lnfix ,x)))

;; examples:
(local
 (defun collect-range (min max)
   (declare (xargs :guard (count-up-guard min max)
                   :measure (count-up-meas min max)))
   (if (count-up-done min max)
       (list max)
     (cons (lnfix min)
           (collect-range (nincr min) max)))))

(local
 (defun collect-range-by (min incr max)
   (declare (Xargs :guard (and (count-past-guard min max)
                               (posp incr))
                   :measure (count-up-meas min max)))
   (if (count-past-done min max)
       nil
     (cons (lnfix min)
           (collect-range-by
            (+ (lnfix min)
               ;; (lpfix incr)
               (mbe :logic (if (and (integerp incr)
                                    (< 0 incr))
                               incr
                             1)
                    :exec incr))
            incr max)))))
