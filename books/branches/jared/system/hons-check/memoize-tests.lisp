; Memoize Sanity Checking
; Copyright (C) 2011 Centaur Technology
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

(in-package "ACL2")
(include-book "misc/assert" :dir :system)
(include-book "std/lists/flatten" :dir :system)

; cert_param: (hons-only)

; This file does nothing useful and should never be included in another
; book.  We just do some very basic computations to make sure the memoize
; system seems to be working right.

(defun f1 (x)
  (declare (xargs :guard t))
  x)

(defun f1-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (f1 (car x))
          (f1-list (cdr x)))))


(defun f2 (x)
  (declare (xargs :guard t))
  (cons x x))

(defun f2-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (f2 (car x))
          (f2-list (cdr x)))))


(defun f3 (x)
  (declare (xargs :guard t))
  (mv x (cons x x)))

(defun f3-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (mv-let (a b) (f3 (car x))
      (list* a b (f3-list (cdr x))))))


(defun f4 (x y)
  (declare (xargs :guard t))
  (cons x y))

(defun f4-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom (cdr x))
        nil
      (cons (f4 (first x) (second x))
            (f4-list (cdr x))))))


(defun f5 (x y)
  (declare (xargs :guard t))
  (mv x y))

(defun f5-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom (cdr x))
        nil
      (mv-let (a b) (f5 (first x) (second x))
        (list* a b (f5-list (cdr x)))))))



(defun f6 (x y z)
  (declare (xargs :guard t))
  (list x y z))

(defun f6-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom (cdr x))
        nil
      (if (atom (cddr x))
          nil
        (cons (f6 (first x) (second x) (third x))
              (f6-list (cdr x)))))))



(defconst *stuff*
  ;; A list with lots of different kinds of objects
  '(0 1 2 3 4
      nil t a b c d
      1/2 1/3 1/5
      -1 -2 -3 -4
      -1/2 -1/3 -1/4
      #c(0 1) #c(0 2) #c(1 2)
      #c(-1 -2) #c(-2 -3) #c(-1 -3)
      #c(1 0) #c(3 0) #c(-1 0)
      #c(0 0)
      #\a #\b #\c #\d
      "foo" "bar" "baz"
      (1 . 2) (1 . 3) (a b c d)))

(defun nats (n)
  (if (zp n)
      nil
    (cons n (nats (1- n)))))

(defconst *data*
  (flatten (append (make-list 1000 :initial-element *stuff*)
                   (hons-copy (make-list 1000 :initial-element *stuff*)))))



(defconst *f1-test* (f1-list *data*))
(defconst *f2-test* (f2-list *data*))
(defconst *f3-test* (f3-list *data*))
(defconst *f4-test* (f4-list *data*))
(defconst *f5-test* (f5-list *data*))
(defconst *f6-test* (f6-list *data*))

(memoize 'f1)
(memoize 'f2)
(memoize 'f3)
(memoize 'f4)
(memoize 'f5)
(memoize 'f6)

(assert! (equal *f1-test* (f1-list *data*)))
(assert! (equal *f2-test* (f2-list *data*)))
(assert! (equal *f3-test* (f3-list *data*)))
(assert! (equal *f4-test* (f4-list *data*)))
(assert! (equal *f5-test* (f5-list *data*)))
(assert! (equal *f6-test* (f6-list *data*)))

(value-triple (memsum))

(unmemoize 'f1)
(unmemoize 'f2)
(unmemoize 'f3)
(unmemoize 'f4)
(unmemoize 'f5)
(unmemoize 'f6)

(memoize 'f1 :condition '(not (equal x -1/3)))
(memoize 'f2 :condition '(not (equal x -1/3)))
(memoize 'f3 :condition '(not (equal x -1/3)))
(memoize 'f4 :condition '(not (equal x -1/3)))
(memoize 'f5 :condition '(not (equal x -1/3)))
(memoize 'f6 :condition '(not (equal x -1/3)))

(assert! (equal *f1-test* (f1-list *data*)))
(assert! (equal *f2-test* (f2-list *data*)))
(assert! (equal *f3-test* (f3-list *data*)))
(assert! (equal *f4-test* (f4-list *data*)))
(assert! (equal *f5-test* (f5-list *data*)))
(assert! (equal *f6-test* (f6-list *data*)))

(value-triple (memsum))

(unmemoize 'f1)
(unmemoize 'f2)
(unmemoize 'f3)
(unmemoize 'f4)
(unmemoize 'f5)
(unmemoize 'f6)
