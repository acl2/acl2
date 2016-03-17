; Lispfloat - Interface to the Common Lisp Floating Point Operations
; Copyright (C) 2016 Centaur Technology
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

(in-package "LISPFLOAT")


; Safe conversion from rationals to floats ------------------------------------

(assert (equal (type-of 1.0f+0) 'single-float))

(defun rat-to-float-raw (x)
  (check-type x rational)
  ;; Common lisp weirdness: the second argument here is a "prototype" that gives
  ;; the type of float to use for the conversion.  We give a single-float by
  ;; doing 1.0f+0.
  (float (rational x) 1.0f+0))

(defun float-to-rat-raw (x)
  (check-type x short-float)
  (rational x))

(defun rat-to-float (x)
  "Returns (MV ERRMSG ANS)"
  (check-type x rational)
  (b* ((ans   (rat-to-float-raw x))
       (check (float-to-rat-raw ans)))
    (mv (if (eql check x)
            nil
          (format nil "Error: ~s cannot be converted to a float without rounding." x))
        ans)))

(defun float-to-rat (x)
  "Returns (MV ERRMSG ANS)"
  (check-type x short-float)
  (b* ((ans   (float-to-rat-raw x))
       (check (rat-to-float-raw ans)))
    (mv (if (eql check x)
            nil
          (format nil "Error: ~s cannot be re-converted to a float without rounding." x))
        ans)))

(assert (equal (rat-to-float-raw 1/2) 0.5))
(assert (equal (float-to-rat-raw 0.5) 1/2))

(assert (b* (((mv err ans) (rat-to-float 1/2)))
          (and (not err)
               (equal ans 0.5))))

(assert (b* (((mv err ans) (rat-to-float 1/3)))
          (and err
               (and (<= 0.33333 ans)
                    (<= ans 0.33334)))))

(assert (b* (((mv err ans) (float-to-rat 0.5)))
          (and (not err)
               (equal ans 1/2))))



(assert (equal (type-of 1.0d+0) 'double-float))

(defun rat-to-double-raw (x)
  (check-type x rational)
  ;; Common lisp weirdness: the second argument here is a "prototype" that gives
  ;; the type of double to use for the conversion.  We give a single-double by
  ;; doing 1.0f+0.
  (float (rational x) 1.0d+0))

(defun double-to-rat-raw (x)
  (check-type x double-float)
  (rational x))

(defun rat-to-double (x)
  "Returns (MV ERRMSG ANS)"
  (check-type x rational)
  (b* ((ans   (rat-to-double-raw x))
       (check (double-to-rat-raw ans)))
    (mv (if (eql check x)
            nil
          (format nil "Error: ~s cannot be converted to a double without rounding." x))
        ans)))

(defun double-to-rat (x)
  "Returns (MV ERRMSG ANS)"
  (check-type x double-float)
  (b* ((ans   (double-to-rat-raw x))
       (check (rat-to-double-raw ans)))
    (mv (if (eql check x)
            nil
          (format nil "Error: ~s cannot be re-converted to a double without rounding." x))
        ans)))

(assert (equal (rat-to-double-raw 1/2) 0.5d0))
(assert (equal (double-to-rat-raw 0.5d0) 1/2))

(assert (b* (((mv err ans) (rat-to-double 1/2)))
          (and (not err)
               (equal ans 0.5d0))))

(assert (b* (((mv err ans) (rat-to-double 1/3)))
          (and err
               (<= 0.33333333333d0 ans)
               (<= ans 0.33333333334d0))))

(assert (b* (((mv err ans) (double-to-rat 0.5d0)))
          (and (not err)
               (equal ans 1/2))))



; FP operation implementations ------------------------------------------------

(defmacro unary-float-template (body)
  `(b* (((mv err1 afloat) (rat-to-float a))
        ((mv err2 ansfloat)
         (handler-case
           (mv nil ,body)
           (arithmetic-error (condition)
                             (mv (format nil "~s" condition) 0))))
        ((mv err3 ansrat) (float-to-rat ansfloat)))
     ;; Putting the errors in this order priorities FP computation errors over
     ;; conversion errors.
     (mv (or err2 err1 err3)
         ansrat)))

(defmacro binary-float-template (body)
  `(b* (((mv err1 afloat) (rat-to-float a))
        ((mv err2 bfloat) (rat-to-float b))
        ((mv err3 ansfloat)
         (handler-case
           (mv nil ,body)
           (arithmetic-error (condition)
                             (mv (format nil "~s" condition) 0))))
        ((mv err4 ansrat) (float-to-rat ansfloat)))
     ;; Putting the errors in this order priorities FP computation errors over
     ;; conversion errors.
     (mv (or err3 err1 err2 err4)
         ansrat)))

(defun real-er-float+ (a b) (binary-float-template (+ afloat bfloat)))
(defun real-er-float- (a b) (binary-float-template (- afloat bfloat)))
(defun real-er-float* (a b) (binary-float-template (* afloat bfloat)))
(defun real-er-float/ (a b) (binary-float-template (/ afloat bfloat)))
(defun real-er-float-expt (a b) (binary-float-template (expt afloat bfloat)))

(defun real-er-float-sqrt (a) (unary-float-template (sqrt afloat)))
(defun real-er-float-e^x (a) (unary-float-template (exp afloat)))

(defun real-er-float-sin (a) (unary-float-template (sin afloat)))
(defun real-er-float-cos (a) (unary-float-template (cos afloat)))
(defun real-er-float-tan (a) (unary-float-template (tan afloat)))



(defmacro unary-double-template (body)
  `(b* (((mv err1 adouble) (rat-to-double a))
        ((mv err2 ansdouble)
         (handler-case
           (mv nil ,body)
           (arithmetic-error (condition)
                             (mv (format nil "~s" condition) 0))))
        ((mv err3 ansrat) (double-to-rat ansdouble)))
     ;; Putting the errors in this order priorities FP computation errors over
     ;; conversion errors.
     (mv (or err2 err1 err3)
         ansrat)))

(defmacro binary-double-template (body)
  `(b* (((mv err1 adouble) (rat-to-double a))
        ((mv err2 bdouble) (rat-to-double b))
        ((mv err3 ansdouble)
         (handler-case
           (mv nil ,body)
           (arithmetic-error (condition)
                             (mv (format nil "~s" condition) 0))))
        ((mv err4 ansrat) (double-to-rat ansdouble)))
     ;; Putting the errors in this order priorities FP computation errors over
     ;; conversion errors.
     (mv (or err3 err1 err2 err4)
         ansrat)))

(defun real-er-double+ (a b) (binary-double-template (+ adouble bdouble)))
(defun real-er-double- (a b) (binary-double-template (- adouble bdouble)))
(defun real-er-double* (a b) (binary-double-template (* adouble bdouble)))
(defun real-er-double/ (a b) (binary-double-template (/ adouble bdouble)))
(defun real-er-double-expt (a b) (binary-double-template (expt adouble bdouble)))

(defun real-er-double-sqrt (a) (unary-double-template (sqrt adouble)))
(defun real-er-double-e^x (a) (unary-double-template (exp adouble)))

(defun real-er-double-sin (a) (unary-double-template (sin adouble)))
(defun real-er-double-cos (a) (unary-double-template (cos adouble)))
(defun real-er-double-tan (a) (unary-double-template (tan adouble)))

