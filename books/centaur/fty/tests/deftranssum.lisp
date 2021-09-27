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

(defun make-subprod-fn (n)
  `(defprod ,(intern$ (cat "SUBPROD" (str::natstr n)) "FTY")
     :tag ,(intern$ (cat "SUBPROD" (str::natstr n)) "KEYWORD")
     :layout :fulltree
     (,@(make-prod-fields 3))))

(defun make-transsum-prods-fn (n)
  (if (zp n)
      nil
    (cons (make-subprod-fn n)
          (make-transsum-prods-fn (- n 1)))))

(tm (with-output
      ;; Make 100 products to use in our tests.
      :off :all
      :gag-mode t
      :on (error)
      (make-event (cons 'progn (make-transsum-prods-fn 100)))))

;; Basic transsum tests -- just have individual products.

(defun make-transsum-members (n)
  (if (zp n)
      nil
    (cons (intern$ (str::cat "SUBPROD" (str::natstr n)) "FTY")
          (make-transsum-members (- n 1)))))

(defun make-transsum-fn (n)
  `(deftranssum ,(intern$ (str::cat "TRANSSUM-" (str::natstr n)) "FTY")
     ,(make-transsum-members n)))

(defmacro make-transsum (n)
  (make-transsum-fn n))

;;                                           2     3     5    10     15     25     100
;; Original times on compute-1-4:         0.51, 0.95, 2.16, 7.45, 16.21, 45.47,    ???
;; Case-optimized kind function:          0.48, 0.90, 2.31, 8.54, 20.40, 60.77,    ???
;;   (hints not updated)
;; Open-member-equal-on-lists-of-tags:    0.31, 0.53, 1.18, 3.88, 8.53,  23.00,    ???
;;   (+ kind-preservation-helper)
;; Fixed hints for preservation-helper:   0.32, 0.44, 0.69, 1.25, 1.98,   2.72,  23.74
;; Remove "case" hack, fix tag issue:     0.48, 0.64, 0.96, 1.81, 2.87,   5.46,  44.52
;;   (incompatible with some VL books,
;;    also, tag of sub-sums was fubar)
;; After kind-possibilities hacking:      0.31, 0.44, 0.68, 1.30, 2.07,   3.86,  31.76
;; Remove -kind function entirely:        0.48, 0.80, 1.44, 4.12, 9.60,  29.95,  ???
;; Separate deftranssum from defsum:      0.16, 0.19, 0.28, 0.49, 0.75,   1.31,  17.16
;;   (may be somewhat incomplete)
(tm (make-transsum 2))
(tm (make-transsum 3))
(tm (make-transsum 5))
(tm (make-transsum 10))
(tm (make-transsum 15))
(tm (make-transsum 25))
(tm (make-transsum 100))

;; (make-transsum 25)

;; Form:  ( DEFTHM TRANSSUM-25-SUBPROD1->VAL$INLINE-OF-TRANSSUM-25-FIX-X
;; ...)
;; Time:  12.09 seconds (prove: 12.09, print: 0.00, other: 0.00)
;; Goal'



; Transsums with mixed product and tagsum members.

(defun make-subtagsum-prods (name n)
  (if (zp n)
      nil
    (cons `(,(intern$ (str::cat name ".PROD" (str::natstr n)) "KEYWORD")
            :layout :fulltree
            ,(make-prod-fields 3))
          (make-subtagsum-prods name (- n 1)))))

(defun make-subtagsum (n)
  (let ((name (str::cat "SUBTAGSUM" (str::natstr n))))
    `(deftagsum ,(intern$ name "FTY")
       ,@(make-subtagsum-prods name 3))))

(defun make-subtagsums (n)
  (if (zp n)
      nil
    (cons (make-subtagsum n)
          (make-subtagsums (- n 1)))))

(tm (with-output
      ;; Make 100 subtagsums to use in our tests.
      :off :all
      :gag-mode t
      :on (error)
      (make-event (cons 'progn (make-subtagsums 100)))))

(defun make-mixed-transsum-members (n)
  (if (zp n)
      nil
    (list* (intern$ (str::cat "SUBPROD" (str::natstr n)) "FTY")
           (intern$ (str::cat "SUBTAGSUM" (str::natstr n)) "FTY")
           (make-mixed-transsum-members (- n 1)))))

(defmacro make-mixed-transsum (n)
  `(deftranssum ,(intern$ (str::cat "MIXEDSUM" (str::natstr n)) "FTY")
     ,(make-mixed-transsum-members n)))

;; compute-1-4:                          1     2      5     10      15      25
;;
;; basic starting point:              1.08, 3.44, 22.64    ???     ???     ???
;; disable open-tags in kind guards:  0.95, 3.14, 20.89    ???     ???     ???
;; separate deftranssum from defsum:  0.53, 1.47, 10.12

(tm (make-mixed-transsum 1))
(tm (make-mixed-transsum 2))
(tm (make-mixed-transsum 5))
;; (tm (make-mixed-transsum 10))
;; (tm (make-mixed-transsum 15))
;; (tm (make-mixed-transsum 25))



;; (make-mixed-transsum 5)
;; Form:  ( DEFTHM MIXEDSUM5-P-OF-MIXEDSUM5-FIX ...)
;; Time:  6.18 seconds (prove: 6.13, print: 0.01, other: 0.04)

