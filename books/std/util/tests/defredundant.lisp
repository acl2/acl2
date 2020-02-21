; Standard Utilities Library
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

(in-package "STD")
(include-book "../defredundant")
(include-book "misc/definline" :dir :system)
(include-book "std/testing/assert" :dir :system)
(include-book "../defines")

(encapsulate
 ()

(local (progn   ;; some events that we'll redundantly introduce

(defun f1 (x)
  (declare (xargs :normalize nil))
  (+ 1 x))

(defthm natp-of-f1
  (implies (natp x)
           (natp (f1 x))))

(defund f2 (x)
  (declare (xargs :verify-guards nil))
  (+ 1 x))

(defthmd natp-of-f2
  (implies (natp x)
           (natp (f2 x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable f2))))

(defun f3 (x)
  (declare (xargs :guard (natp x)
                  :verify-guards t))
  (+ 1 x))

(in-theory (disable (:e f3)))

(mutual-recursion
 (defun f4-term (x)
   (declare (xargs :guard (pseudo-termp x)))
   (if (atom x)
       1
     (if (quotep x)
         2
       (cons (car x) (f4-list (cdr x))))))
 (defund f4-list (x)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (cons (f4-term (car x))
           (f4-list (cdr x))))))

(definline f5 (x)
  (declare (xargs :guard t))
  x)

(definlined f6 (x)
  (declare (xargs :guard (natp x)))
  (+ 1 x))

(defun f7 (x)
  (declare (xargs :mode :program))
  (+ 1 x))

(definline f8 (x)
  (declare (xargs :mode :program :guard (natp x)))
  (+ 1 x))

(defun m (x y)
  (+ (acl2-count x) (acl2-count y)))

(defund f9 (x y)
  (declare (xargs :measure (m x y)))
  (if (and (atom x)
           (atom y))
      0
    (+ (f9 (cdr x) (cdr y)))))

(defines g0
 (define g0-term (x)
   :inline t
   :guard (pseudo-termp x)
   (if (atom x)
       1
     (if (quotep x)
         2
       (cons (car x) (g0-list (cdr x))))))
 (define g0-list (x)
   :guard (pseudo-term-listp x)
   :enabled t
   (if (atom x)
       nil
     (cons (g0-term (car x))
           (g0-list (cdr x))))))


))


(defredundant  ;; redundantly introduce the above
  :names (f1
          natp-of-f1
          f2
          natp-of-f2
          f3
          f4-term
          f5
          f9
          g0-list))

) ;; end of encapsulate


;; basic unit tests to make sure things are working right

(defmacro assert-enabled (rune enabled-p)
  `(make-event
    (b* ((rune      ',rune)
         (acl2::ens (acl2::ens state))
         (actual    (if (acl2::active-runep rune) t nil))
         ((when (equal actual ',enabled-p))
          (value '(value-triple :success))))
      (er soft 'assert-enabled "Expected (active-runep ~x0) to be ~x1, found ~x2.~%"
          rune ',enabled-p actual))))

(defmacro assert-macro (name)
  `(make-event
    (b* ((macro-args (getprop ',name 'acl2::macro-args :bad 'acl2::current-acl2-world (w state)))
         ((unless (eq macro-args :bad))
          (value '(value-triple :success))))
      (er soft 'assert-macro "Expected ~x0 to be a macro, but found no macro args." ',name))))

(assert-enabled (:definition f1) t)
(assert-enabled (:definition f2) nil)
(assert-enabled (:definition f3) t)

(assert-enabled (:definition f4-term) t)
(assert-enabled (:definition f4-list) nil)

(assert-enabled (:definition f5$inline) t)
(assert-enabled (:type-prescription f5$inline) t)
(assert-macro f5)

(assert-enabled (:definition f9) nil)

(assert-enabled (:definition g0-term) nil)
(assert-enabled (:definition g0-list) t)
(assert-macro g0-term)

(assert-enabled (:rewrite natp-of-f1) t)
(assert-enabled (:type-prescription natp-of-f2) nil)

(assert-enabled (:executable-counterpart f1) t)
(assert-enabled (:executable-counterpart f2) t)
(assert-enabled (:executable-counterpart f3) nil)
(assert-enabled (:executable-counterpart f9) t)
