; FTY Performance Tests
; Copyright (C) 2014 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "FTY")
(include-book "utils")

(defun make-prod-fields (n)
  (if (zp n)
      nil
    (cons `(,(intern$ (cat "FIELD" (str::natstr n)) "FTY") integerp)
          (make-prod-fields (- n 1)))))

(defun make-tagsum-prods (numprods numfields)
  (if (zp numprods)
      nil
    (cons `(,(intern$ (str::cat "SUBPROD" (str::natstr numprods)) "KEYWORD")
            :layout :fulltree
            ,(make-prod-fields numfields))
          (make-tagsum-prods (- numprods 1) numfields))))

(defun make-tagsum-fn (numprods numfields verbosep prefix)
  `(deftagsum ,(intern$
                (str::cat prefix "-" (str::natstr numprods) "." (str::natstr numfields))
                "FTY")
     :verbosep ,verbosep
     ,@(make-tagsum-prods numprods numfields)))

(defmacro make-tagsum (&key numprods numfields verbosep (prefix '"TAGSUM"))
  (make-tagsum-fn numprods numfields verbosep prefix))

;; Scaling Product Count
;;
;; Original times on compute-1-4:            0.15, 0.24, 0.53, 1.06, 2.29,  7.81, 27.39
;; With deffixequiv hints tweak:             0.15, 0.24, 0.53, 1.06, 2.26,  7.62, 26.67
;; After transsum fixes (tag-reasoning):     0.19, 0.30, 0.67, 1.35, 2.92, 10.04, 35.02
;; Aggressive disabling kind-possibilities:  0.19, 0.32, 0.68, 1.34, 2.85,  8.50, 23.68  (breaks deftypes-tests tho)
;; Less aggressive (kind fix only):          0.21, 0.32, 0.70, 1.40, 2.99,  9.84, 32.25  arrgh
;; Aggressive but fix count returns:         0.20, 0.32, 0.69, 1.36, 2.83,  8.45, 24.10  yaaaa
;; Baseline after splitting out deftranssum: 0.20, 0.32, 0.67, 1.33, 2.82,  8.88, 27.07

(tm (make-tagsum :numprods 1 :numfields 3))
(tm (make-tagsum :numprods 2 :numfields 3))
(tm (make-tagsum :numprods 5 :numfields 3))
(tm (make-tagsum :numprods 10 :numfields 3))
(tm (make-tagsum :numprods 20 :numfields 3))
(tm (make-tagsum :numprods 50 :numfields 3))
(tm (make-tagsum :numprods 100 :numfields 3))

;; Unfortunately there isn't a lot of fat to trim here.  Original version:

;; (accumulated-persistence t)
;; (make-tagsum :numprods 100 :numfields 3)







;; Scaling Field Count
;;
;; Original times on compute-1-4:            0.24, 0.34, 0.64, 1.19, 2.55,  9.92, 52.11
;; After transsum fixes (tag-reasoning):     0.32, 0.46, 0.89, 1.68, 3.51, 12.32, 58.29
;; Selectively disabling kind-possibilities: 0.41, 0.56, 1.04, 1.91, 3.94, 13.59, 62.26
;; Post count-returns kind-possibilities:    0.45, 0.59, 1.09, 1.97, 4.09, 14.17, 62.90
(tm (make-tagsum :numprods 4 :numfields 1))
(tm (make-tagsum :numprods 4 :numfields 2))
(tm (make-tagsum :numprods 4 :numfields 5))
(tm (make-tagsum :numprods 4 :numfields 10))
(tm (make-tagsum :numprods 4 :numfields 20))
(tm (make-tagsum :numprods 4 :numfields 50))
(tm (make-tagsum :numprods 4 :numfields 100))

