; Memoize Sanity Checking
; Copyright (C) 2011-2014 Centaur Technology
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
;
; Modified 8/2014 by Matt Kaufmann to make functions tail recursive, to avoid
; errors in LispWorks and Allegro CL (at least).

(in-package "ACL2")

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 92.53 sec. vs. 314.30 sec.
(value-triple (set-gc-strategy :delay))

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/lists/flatten" :dir :system)
(include-book "std/util/bstar" :dir :system)

; This file does nothing useful and should never be included in another
; book.  We just do some very basic computations to make sure the memoize
; system seems to be working right.

(defun f1 (x)
  (declare (xargs :guard t))
  x)

(defun f1-list-tailrec (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom x)
      (reverse acc)
    (f1-list-tailrec (cdr x)
                     (cons (f1 (car x)) acc))))

(defun f1-list (x)
  (declare (xargs :guard t))
  (f1-list-tailrec x nil))


(defun f2 (x)
  (declare (xargs :guard t))
  (cons x x))

(defun f2-list-tailrec (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom x)
      (reverse acc)
    (f2-list-tailrec (cdr x)
                     (cons (f2 (car x)) acc))))

(defun f2-list (x)
  (declare (xargs :guard t))
  (f2-list-tailrec x nil))


(defun f3 (x)
  (declare (xargs :guard t))
  (mv x (cons 1 x)))

(defun f3-list-tailrec (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom x)
      (reverse acc)
    (mv-let (a b)
            (f3 (car x))
            (f3-list-tailrec (cdr x)
                             (list* b a acc)))))


(defun f3-list (x)
  (declare (xargs :guard t))
  (f3-list-tailrec x nil))


(defun f4 (x y)
  (declare (xargs :guard t))
  (cons 1/2 (cons x y)))

(defun f4-list-tailrec (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom x)
      (reverse acc)
    (if (atom (cdr x))
        (reverse acc)
      (f4-list-tailrec (cdr x)
                       (cons (f4 (first x) (second x))
                             acc)))))

(defun f4-list (x)
  (declare (xargs :guard t))
  (f4-list-tailrec x nil))


(defun f5 (x y)
  (declare (xargs :guard t))
  (mv x y))

(defun f5-list-tailrec (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom x)
      (reverse acc)
    (if (atom (cdr x))
        (reverse acc)
      (mv-let (a b)
              (f5 (first x) (second x))
              (f5-list-tailrec (cdr x)
                               (list* b a acc))))))

(defun f5-list (x)
  (declare (xargs :guard t))
  (f5-list-tailrec x nil))


(defun f6 (x y z)
  (declare (xargs :guard t))
  (list x y z))

(defun f6-list-tailrec (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom x)
      (reverse acc)
    (if (atom (cdr x))
        (reverse acc)
      (if (atom (cddr x))
          (reverse acc)
        (f6-list-tailrec (cdr x)
                         (cons (f6 (first x) (second x) (third x))
                               acc))))))

(defun f6-list (x)
  (declare (xargs :guard t))
  (f6-list-tailrec x nil))


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

(comp t) ; needed for GCL (and maybe other Lisps)

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


;; (defun show-me-default-hons-space (from)
;;   (declare (xargs :guard t)
;;            (ignorable from))
;;   (er hard? 'show-me-default-hons-space
;;       "Raw lisp definition not installed"))
;; (defttag :show-me-default-hons-space)
;; (progn!
;;  (set-raw-mode t)
;;  (defun show-me-default-hons-space (from)
;;    (format t "~S: Default-hs is ~S~%"
;;            from
;;            (funcall (intern "%ADDRESS-OF" "CCL") *default-hs*))
;;    nil))

(defun test-simultaneously-acons ()
; We may need to verify guards to execute the raw Lisp (parallelized) version
; of pand.
  (declare (xargs :verify-guards t))
  (pand (progn$
         ;; (show-me-default-hons-space 'thread-1-pre)
         ;; (hons-summary)
         (hons-acons 1 2 nil)
         ;; (show-me-default-hons-space 'thread-1-post)
         ;; (hons-summary)
         t)
        (progn$
         ;; (show-me-default-hons-space 'thread-2-pre)
         ;; (hons-summary)
         (hons-acons 2 3 nil)
         ;; (show-me-default-hons-space 'thread-2-post)
         ;; (hons-summary)
         t)))

(assert! (test-simultaneously-acons))

(defun test-simultaneously-acons-with-spec-mv-let ()
; We must verify guards to execute the raw Lisp (parallelized) version of
; spec-mv-let.
  (declare (xargs :verify-guards t))
  (spec-mv-let (x)
    (hons-acons 1 2 nil)
    (mv-let (y z)
      (mv (hons-acons 3 4 nil)
          6)
      (if t
          (+ (caar x) (cdar x) (caar y) (cdar y) z)
        (+ (caar y) (cadr y) z)))))

(assert! (test-simultaneously-acons-with-spec-mv-let))

(defun test-simultaneously-hons ()
; We may need to verify guards to execute the raw Lisp (parallelized) version
; of pand.
  (declare (xargs :verify-guards t))
  (pand (hons 1 2)
        (hons 3 4)))

(assert! (test-simultaneously-hons))

(defun test-simultaneously-hons-with-spec-mv-let ()
; We must verify guards to execute the raw Lisp (parallelized) version of
; spec-mv-let.
  (declare (xargs :verify-guards t))
  (spec-mv-let (x)
    (hons 7 8)
    (mv-let (y z)
      (mv (hons 9 10) 11)
      (if t
          (+ (car x) (cdr x) (car y) (cdr y) z)
        (+ (car y) (cdr y) z)))))

(assert! (test-simultaneously-hons-with-spec-mv-let))



(defun make-memoized-alist (x)
  (declare (xargs :guard t))
  (make-fast-alist (cons (cons 'x x)
                         '(("a" . 1)
                           (b . 2)
                           (c . 3)))))

(memoize 'make-memoized-alist)

(defun do-stuff-to-fast-alist (n alist)
  (declare (xargs :guard (natp n)))
  (b* (((when (zp n))
        alist)
       (?a (hons-get 'a alist))
       (?b (hons-get 'b alist))
       (?c (hons-get 'c alist))
       (alist (hons-acons n n alist)))
    (do-stuff-to-fast-alist (- n 1) alist)))

(comp t)

(defconst *spec* (do-stuff-to-fast-alist 1000 (make-memoized-alist 5)))

(defun check-both-with-pand (n)
  (declare (xargs :guard (natp n)))
  (pand (equal (do-stuff-to-fast-alist n (make-fast-alist (make-memoized-alist 5))) *spec*)
        (equal (do-stuff-to-fast-alist n (make-fast-alist (make-memoized-alist 5))) *spec*)))

(assert! (check-both-with-pand 1000))




;; Basic check to try to see if threads will interfere with one another

(defun add-some-honses (x acc)
  (declare (xargs :guard t))
  (if (atom x)
      acc
    (add-some-honses (cdr x)
                     (list* (hons-copy (car x))
                            (hons (car x) (car x))
                            acc))))
(defun thread1 (x)
  (declare (xargs :guard t))
  (let ((x (add-some-honses x x)))
    (list (f1-list x)
          (f2-list x)
          (f3-list x)
          (f4-list x)
          (f5-list x)
          (f6-list x))))

(defun thread2 (x)
  (declare (xargs :guard t))
  (let ((x (add-some-honses x x)))
    (list (f2-list x)
          (f4-list x)
          (f6-list x)
          (f1-list x)
          (f3-list x)
          (f5-list x))))

(comp t) ;; so gcl will compile add-some-honses instead of stack overflowing

(defconst *thread1-spec* (thread1 *data*))
(defconst *thread2-spec* (thread2 *data*))

(defun check-thread1 (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (equal *thread1-spec* (thread1 *data*))
         (check-thread1 (- n 1)))))

(defun check-thread2 (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (equal *thread2-spec* (thread2 *data*))
         (check-thread2 (- n 1)))))

(defun check-both (n)
  (declare (xargs :guard (natp n)))
  (pand (check-thread1 n)
        (check-thread2 n)))

(comp t) ;; so gcl will compile to avoid stack overflow in (check-both 100) below

;; Timings on compute-1-1:
;;  - ACL2(hp): no memoization: 12.33 seconds (many GC messages)
;;  - ACL2(h):  no memoization: 15.54 seconds (many GC messages)

(assert! (time$ (check-both 100)))

(value-triple (clear-memoize-tables))

(memoize 'f1)
(memoize 'f2 :condition '(not (equal x -1/3)))
(memoize 'f3)
(memoize 'f4 :condition '(not (equal x -1/3)))
(memoize 'f5)
(memoize 'f6 :condition '(not (equal x -1/3)))

;; Timings on compute-1-1:
;;  - ACL2(hp): memoization, lock contention:     242 seconds (many gc messages)
;;  - ACL2(h):  memoization, no lock contention:   61 seconds (many gc messages)
(assert! (time$ (check-both 100)))
