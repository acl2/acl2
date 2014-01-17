; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(in-package "ACL2")
(include-book "def-typed-record")
(include-book "ihs/basic-definitions" :dir :system)

; This book just has some examples of def-typed-record commands.  Sometimes
; you have to do various tricks (like supplying the :in-package-of argument,
; or using make-event to generate (code-char 0), etc.).


(def-typed-record int
  :elem-p        (integerp x)
  :elem-list-p   (integer-listp x)
  :elem-fix      (ifix x)
  :elem-default  0)


(defun cons-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      x
    (cons nil nil)))

(def-typed-record rstobj-package-cons
  :elem-p        (consp x)
  :elem-list-p   (alistp x)
  :elem-fix      (cons-fix x)
  :elem-default  '(nil . nil)
  :in-package-of rstobj::foo)


(defun character-fix (x)
  (declare (xargs :guard t))
  (if (characterp x)
      x
    (code-char 0)))

(make-event
 `(def-typed-record char
    :elem-p        (characterp x)
    :elem-list-p   (character-listp x)
    :elem-fix      (character-fix x)
    :elem-default  ,(code-char 0)
    ;; avoid problems with common-lisp package
    :in-package-of foo))


(defun bit-fix (x)
  (declare (xargs :guard t))
  (if (bitp x)
      x
    0))

(defun bit-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (bitp (car x))
         (bit-listp (cdr x)))))

(def-typed-record bit
  :elem-p        (bitp x)
  :elem-list-p   (bit-listp x)
  :elem-fix      (bit-fix x)
  :elem-default  0
  :in-package-of foo)



; Here's a way to do typed records for bounded signed-byte and unsigned-bytes:

(defun signed-byte-fix (n x)
  (declare (xargs :guard t))
  (if (signed-byte-p n x)
      x
    0))

(defun signed-byte-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (signed-byte-p n (car x))
         (signed-byte-listp n (cdr x)))))

(defun unsigned-byte-fix (n x)
  (declare (xargs :guard t))
  (if (unsigned-byte-p n x)
      x
    0))

(defun unsigned-byte-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (unsigned-byte-p n (car x))
         (unsigned-byte-listp n (cdr x)))))



(def-typed-record sb32
  :elem-p       (signed-byte-p 32 x)
  :elem-list-p  (signed-byte-listp 32 x)
  :elem-fix     (signed-byte-fix 32 x)
  :elem-default 0)

(def-typed-record ub8
  :elem-p       (unsigned-byte-p 8 x)
  :elem-list-p  (unsigned-byte-listp 8 x)
  :elem-fix     (unsigned-byte-fix 8 x)
  :elem-default 0)

(def-typed-record ub128
  :elem-p       (unsigned-byte-p 128 x)
  :elem-list-p  (unsigned-byte-listp 128 x)
  :elem-fix     (unsigned-byte-fix 128 x)
  :elem-default 0)


