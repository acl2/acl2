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

(defun make-prod-fn (n prefix)
  `(defprod ,(intern$ (cat prefix (str::natstr n)) "FTY")
     :tag ,(intern$ (cat prefix (str::natstr n)) "KEYWORD")
     :layout :tree
     (,@(make-prod-fields n))))

(defmacro make-prod (n &key (prefix '"PROD"))
  (make-prod-fn n prefix))


;; Original times on compute-1-3:          0.14, 0.16, 0.25, 0.42, 0.88, 4.18, 43.35
;; Move deffixequiv past equal-of- rule:   0.14, 0.18, 0.27, 0.43, 0.91, 3.14, 15.77
;; Disable tmp/type-pres/fwd-chaining:     0.17, 0.21, 0.33, 0.40, 0.79, 2.72, 14.13
;; After transsum fixes (tag-reasoning):   0.20, 0.18, 0.30, 0.51, 0.98, 3.24, 15.42
;; After kind-possibilities hacking:       0.16, 0.20, 0.31, 0.52, 1.00, 3.29, 15.45
(tm (make-prod 1))
(tm (make-prod 2))
(tm (make-prod 5))
(tm (make-prod 10))
(tm (make-prod 20))
(tm (make-prod 50))
(tm (make-prod 100))

;; This is pretty well tuned now.  The only thing we're doing that still takes
;; any time is EQUAL-OF-PROD100.  It seems like ACL2 is spending a good bit of
;; time in FIND-SUBSUMER-REPLACEMENT.  Not much to do about that.
