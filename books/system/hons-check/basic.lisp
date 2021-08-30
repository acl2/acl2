; Hons Sanity Checking
; Copyright (C) 2010 Centaur Technology
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
(include-book "hons-check")
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/osets/top" :dir :system)

; This file does nothing useful and should never be included in another
; book.  We just do some very basic computations to make sure the hons
; system seems to be working right.

(value-triple (hons-check))


;; Just an object with all the different kinds of atoms and such.

(defconst *mixed-obj*
  (list t nil
        'a 'b 'c 'd
        :a (list :b :c)
        0
        (list 1 2 3 4)
        -1 -2
        (list -3 -4)
        (list* 0 #x-FFFFFFFFFFFFFFFF0000 #x-FFFFFFFFFFFFFFFF0001)
        (cons #xFFFFFFFF000000000000 #xFFFFFFFF000000000001)
        1/2 1/3
        (list 1/4 1/5)
        -1/2 -1/3 -1/4 -1/5
        #C(0 1)
        (list #C(2 3) #C(1/2 -3/4) "foo")
        (list "bar" "baz")
        #\a #\b
        (list #\c #\d)
        #\Space
        (+ -2 (- (expt 2 14)))
        (+ -1 (- (expt 2 14)))
        (- (expt 2 14))
        (+ 1 (- (expt 2 14)))
        (+ 2 (- (expt 2 14)))
        (+ -2 (expt 2 23))
        (+ -1 (expt 2 23))
        (- (expt 2 23))
        (+ 1 (- (expt 2 23)))
        (+ 2 (- (expt 2 23)))))


(value-triple (hons-check))

(assert! (not (unsound-normedp *mixed-obj*)))
(assert! (not (unsound-falp *mixed-obj*)))

(defconst *foo* (hons-copy *mixed-obj*))

(value-triple (hons-check))

(assert! (equal *foo* *mixed-obj*))
(assert! (hons-equal *foo* *mixed-obj*))
(assert! (hons-equal-lite *foo* *mixed-obj*))

(assert! (hons-equal *foo* *foo*))
(assert! (hons-equal-lite *foo* *foo*))

(assert! (hons-equal (cons *foo* 1) (cons *foo* 1)))
(assert! (hons-equal-lite (cons *foo* 1) (cons *foo* 1)))

(assert! (not (hons-equal (cons *foo* 1) (cons *foo* 0))))
(assert! (not (hons-equal-lite (cons *foo* 1) (cons *foo* 0))))

(assert! (unsound-normedp *foo*))
(assert! (not (unsound-falp *foo*)))

(value-triple (hons-summary))
(value-triple (hons-check))


(value-triple (hons-copy-persistent (nthcdr 5 *mixed-obj*)))
(value-triple (hons-check))

(value-triple (hons-clear t))

(value-triple (hons-check))




(defun flat (x)
  (if (atom x)
      (list x)
    (append (flat (car x))
            (flat (cdr x)))))

(defconst *atoms* (set::mergesort (flat *mixed-obj*)))

(assert! (not (unsound-normedp *atoms*)))
(assert! (not (unsound-falp *atoms*)))
(value-triple (hons-check))



(defun make-fal (x name)
  (if (atom x)
      name
    (hons-acons (caar x)
                (cdar x)
                (make-fal (cdr x) name))))

(defconst *fal1* (make-fal (pairlis$ *atoms* nil) nil))
(defconst *fal2* (make-fal (pairlis$ *atoms* nil) 100))
(defconst *fal3* (make-fal (pairlis$ *atoms* nil) 'foo))
(defconst *fal4* (make-fal (pairlis$ (append *atoms* *atoms*) nil) 1/2))

(value-triple (fast-alist-summary))
(value-triple (hons-check))


(defun change-final-cdr (x a)
  (if (atom x)
      a
    (cons (car x)
          (change-final-cdr (cdr x) a))))

(assert! (equal *fal1* (pairlis$ *atoms* nil)))
(assert! (equal *fal2* (change-final-cdr (pairlis$ *atoms* nil) 100)))
(assert! (equal *fal3* (change-final-cdr (pairlis$ *atoms* nil) 'foo)))
(assert! (equal *fal4* (change-final-cdr (pairlis$ (append *atoms* *atoms*) nil) 1/2)))

(assert! (unsound-falp *fal1*))
(assert! (unsound-falp *fal2*))
(assert! (unsound-falp *fal3*))
(assert! (unsound-falp *fal4*))

(assert! (equal (fast-alist-len *fal1*) (len *atoms*)))
(assert! (equal (fast-alist-len *fal2*) (len *atoms*)))
(assert! (equal (fast-alist-len *fal3*) (len *atoms*)))
(assert! (equal (fast-alist-len *fal4*) (len *atoms*)))

(value-triple (hons-check))


(defun check-alist-agree (domain slow-al fast-al)
  (or (atom domain)
      (and (or (equal (assoc-equal (car domain) slow-al)
                      (hons-get (car domain) fast-al))
               (cw "Fail for ~x0: slow = ~x1, fast = ~x2~%"
                   (car domain)
                   (assoc-equal (car domain) slow-al)
                   (hons-get (car domain) fast-al)))
           (check-alist-agree (cdr domain) slow-al fast-al))))

(assert! (check-alist-agree *atoms* *fal1* *fal1*))
(assert! (check-alist-agree *atoms* *fal1* *fal2*))
(assert! (check-alist-agree *atoms* *fal1* *fal3*))
(assert! (check-alist-agree *atoms* *fal1* *fal4*))

(value-triple (hons-check))


(defconst *fal5* (hons-shrink-alist *fal1* nil))
(assert! (check-alist-agree *atoms* *fal5* *fal1*))

(value-triple (hons-check))
