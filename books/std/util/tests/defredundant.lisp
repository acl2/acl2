; Standard Utilities Library
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

(in-package "STD")
(include-book "../defredundant")
(include-book "misc/definline" :dir :system)
(include-book "misc/assert" :dir :system)

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
 (defun f4-list (x)
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

))


(defredundant  ;; redundantly introduce the above
  :names (f1
          natp-of-f1
          f2
          natp-of-f2
          f3
          f9))

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

(assert-enabled (:definition f1) t)
(assert-enabled (:definition f2) nil)
(assert-enabled (:definition f3) t)
(assert-enabled (:definition f9) nil)

(assert-enabled (:rewrite natp-of-f1) t)
(assert-enabled (:type-prescription natp-of-f2) nil)

(assert-enabled (:executable-counterpart f1) t)
(assert-enabled (:executable-counterpart f2) t)
(assert-enabled (:executable-counterpart f3) nil)
(assert-enabled (:executable-counterpart f9) t)


