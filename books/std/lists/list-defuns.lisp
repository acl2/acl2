; Definitions of List Functions
; Portions are Copyright (C) 2008-2013 Centaur Technology
; Portions are Copyright (C) 2004-2013 by Jared Davis
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
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
;
; list-defuns.lisp
;
; This file was originally part of the Unicode library.  It has since then been
; extended with additional definitions, e.g., from Centaur libraries.

(in-package "ACL2")
(include-book "tools/bstar" :dir :system)
(include-book "tools/rulesets" :dir :system)
(local (include-book "append"))
(local (include-book "duplicity"))
(local (include-book "list-fix"))
(local (include-book "flatten"))
(local (include-book "final-cdr"))
(local (include-book "prefixp"))
(local (include-book "take"))
(local (include-book "repeat"))
(local (include-book "revappend"))
(local (include-book "nthcdr"))
(local (include-book "rcons"))
(local (include-book "rev"))
(local (include-book "equiv"))
(local (include-book "sets"))
(local (include-book "same-lengthp"))
(local (include-book "sublistp"))
(set-enforce-redundancy t)

(defund list-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (list-fix (cdr x)))
    nil))

(defund fast-list-equiv (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (fast-list-equiv (cdr x) (cdr y)))
    (atom y)))

(defund list-equiv (x y)
  (mbe :logic (equal (list-fix x) (list-fix y))
       :exec (fast-list-equiv x y)))

(defequiv list-equiv
  ;; We include this, even though this book isn't really meant to include
  ;; theorems, in order to avoid subtle errors that can arise in different
  ;; books.  Without this, in book A we could just load LIST-DEFUNS and then
  ;; prove a theorem that concluded (LIST-EQUIV X Y).  If then in book B we
  ;; load list/equiv.lisp first and then include book A, this is no longer a
  ;; valid rewrite rule and we get a horrible error!
  )

(defun set-equiv (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (and (subsetp-equal x y)
       (subsetp-equal y x)))

(defequiv set-equiv)

(defrefinement list-equiv set-equiv)


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
      (append-without-guard (car x)
                            (flatten (cdr x)))
    nil))

(defund repeat (x n)
  (declare (xargs :guard (natp n)))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat x (- n 1))))
       :exec (make-list n :initial-element x)))

(defund final-cdr (x)
  (declare (xargs :guard t))
  (if (atom x)
      x
    (final-cdr (cdr x))))

(defun rest-n (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (nthcdr n x)
       :exec
       (cond ((zp n)
              x)
             ((atom x)
              nil)
             (t
              (rest-n (- n 1) (cdr x))))))

(defun first-n (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (take n x)
       :exec
       (cond ((zp n)
              nil)
             ((atom x)
              (make-list n))
             (t
              (cons (car x)
                    (first-n (- n 1) (cdr x)))))))

(defun same-lengthp (x y)
  (declare (xargs :guard t))
  (mbe :logic (equal (len x) (len y))
       :exec (if (consp x)
                 (and (consp y)
                      (same-lengthp (cdr x) (cdr y)))
               (not (consp y)))))

(defund sublistp (x y)
  (declare (xargs :guard t))
  (cond ((prefixp x y) t)
        ((atom y)      nil)
        (t             (sublistp x (cdr y)))))

(defund listpos (x y)
  (declare (xargs :guard t))
  (cond ((prefixp x y)
         0)
        ((atom y)
         nil)
        (t
         (let ((pos-in-cdr (listpos x (cdr y))))
           (and pos-in-cdr
                (+ 1 pos-in-cdr))))))

(defund duplicity-exec (a x n)
  (declare (xargs :guard (natp n)))
  (if (atom x)
      n
    (duplicity-exec a (cdr x)
                    (if (equal (car x) a)
                        (+ 1 n)
                      n))))

(defund duplicity (a x)
  (declare (xargs :guard t))
  (mbe :logic (cond ((atom x)
                     0)
                    ((equal (car x) a)
                     (+ 1 (duplicity a (cdr x))))
                    (t
                     (duplicity a (cdr x))))
       :exec (duplicity-exec a x 0)))
