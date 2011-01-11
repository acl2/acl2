;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(local (include-book "app"))
(local (include-book "append"))
(local (include-book "list-fix"))
(local (include-book "flatten"))
(local (include-book "prefixp"))
(local (include-book "take"))
(local (include-book "repeat"))
(local (include-book "revappend"))
(local (include-book "rev"))
(set-enforce-redundancy t)

(defund list-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (list-fix (cdr x)))
    nil))

(defund binary-app (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (binary-app (cdr x) y))
    (list-fix y)))

(defmacro app (x y &rest rst)
  (xxxjoin 'binary-app (list* x y rst)))

(add-macro-alias app binary-app)

(defun binary-append-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic
       (append x y)
       :exec
       (if (consp x)
           (cons (car x)
                 (binary-append-without-guard (cdr x) y))
         y)))

(defmacro append-without-guard (x y &rest rst)
  (xxxjoin 'binary-append-without-guard (list* x y rst)))

(add-macro-alias append-without-guard binary-append-without-guard)

(defun revappend-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic (revappend x y)
       :exec  (if (consp x)
                  (revappend-without-guard (cdr x)
                                           (cons (car x) y))
                y)))

(defund rev (x)
  (declare (xargs :guard t))
  (mbe :logic (if (consp x)
                  (append (rev (cdr x))
                          (list (car x)))
                nil)
       :exec (revappend-without-guard x nil)))

(defund simpler-take (n xs)
  (declare (xargs :guard (and (natp n)
                              (true-listp xs))))
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take (1- n) (cdr xs)))))

(defund prefixp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

(defund flatten (x)
  (declare (xargs :guard t))
  (if (consp x)
      (mbe :logic (app (car x)
                       (flatten (cdr x)))
           :exec (binary-append-without-guard (car x)
                                          (flatten (cdr x))))
    nil))

(defund repeat (x n)
  (declare (xargs :guard (natp n)))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat x (- n 1))))
       :exec (make-list n :initial-element x)))
