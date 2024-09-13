; Copyright (C) 2024 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>


(in-package "ACL2")

;; This just defines two rules, kind of in the spirit of
;; meta/cancel-plus-lessp.lisp, which just find reciprocals in equivalences or
;; comparisons and multiply them through.  This seems to help ACL2's nonlinear
;; decision procedure, in cases where certain factors appear both in a
;; reciprocal and not.

(local (include-book "arithmetic/top" :dir :system))


(defun find-recip-in-poly (x)
  (declare (xargs :mode :program))
  (case-match x
    (('binary-+ a b) (or (find-recip-in-poly a)
                         (find-recip-in-poly b)))
    (('unary-- a) (find-recip-in-poly a))
    (('binary-* a b) (or (find-recip-in-poly a)
                         (find-recip-in-poly b)))
    (('unary-/ a) a)
    (& nil)))

(defthm multiply-out-equal
  (implies (and (bind-free (let ((z (or (find-recip-in-poly x)
                                        (find-recip-in-poly y))))
                             (and z `((z . ,z))))
                           (z))
                (not (equal (rfix z) 0))
                (acl2-numberp x)
                (acl2-numberp y))
           (iff (equal x y)
                (equal (* z x) (* z y)))))

(defthm multiply-out-<
  (implies (and (bind-free (let ((z (or (find-recip-in-poly x)
                                        (find-recip-in-poly y))))
                             (and z `((z . ,z))))
                           (z))
                (not (equal (rfix z) 0))
                (rationalp x)
                (rationalp y))
           (iff (< x y)
                (if (< z 0)
                    (> (* z x) (* z y))
                  (< (* z x) (* z y))))))


(defun collect-factors (x)
  (case-match x
    (('quote &) nil)
    (('binary-* a b) (append (collect-factors a)
                             (collect-factors b)))
    (& (list x))))

(mutual-recursion
 (defun find-common-terms-in-poly (x)
  (declare (xargs :mode :program))
  (case-match x
    (('binary-+ a b) (find-common-terms a b))
    (('unary-- a) (find-common-terms-in-poly a))
    (('binary-* & &) (collect-factors x))
    (& (list x))))

 (defun find-common-terms (x y)
   (cond ((equal x ''0) (find-common-terms-in-poly y))
         ((equal y ''0) (find-common-terms-in-poly x))
         (t (intersection-equal (find-common-terms-in-poly x)
                                (find-common-terms-in-poly y))))))

(defthmd divide-out-common-factors-equal
  (implies (and (bind-free (and (or (not (equal x ''0))
                                    (case-match y (('binary-+ & &) t)))
                                (or (not (equal y ''0))
                                    (case-match x (('binary-+ & &) t)))
                                (let ((factors (find-common-terms x y)))
                                  (and (consp factors)
                                       `((factor . ,(car factors))))))
                           (factor))
                (acl2-numberp factor)
                (not (equal 0 factor))
                (acl2-numberp x)
                (acl2-numberp y))
           (iff (equal x y)
                (equal (* (/ factor) x) (* (/ factor) y)))))

(defthmd divide-out-common-factors-<
  (implies (and (bind-free (and (or (not (equal x ''0))
                                      (case-match y (('binary-+ & &) t)))
                                (or (not (equal y ''0))
                                    (case-match x (('binary-+ & &) t)))
                                (let ((factors (find-common-terms x y)))
                                  (and (consp factors)
                                       `((factor . ,(car factors))))))
                           (factor))
                (rationalp factor)
                (not (equal 0 factor))
                (rationalp x)
                (rationalp y))
           (iff (< x y)
                (if (< 0 factor)
                    (< (* (/ factor) x) (* (/ factor) y))
                  (> (* (/ factor) x) (* (/ factor) y))))))



     
       
