; Index-of -- like "position" but sane(ish)
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>


(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection index-of
  :parents (std/lists search)
  :short "@(call index-of) returns the index of the first occurrence of element
@('k') in list @('x') if it exists, @('NIL') otherwise."

  :long "Index-of is like the Common Lisp function @(tsee position), but only
  operates on lists and is not (logically) tail-recursive."



  ;; BOZO this isn't the standard way to do equality variants but perhaps it's
  ;; about as good.  In any case, index-of doesn't have a guard and should be
  ;; pretty fast because it chooses which aux function to call based just on
  ;; the type of the element.  The one case we lose is if we're looking for a
  ;; badly-typed element in a well-typed list, e.g. a cons structure in a list
  ;; of integers, in which case we'll run the equal version where we could have
  ;; done the eql version.
  (defun index-of-aux (k x acc)
    (declare (type (integer 0 *) acc))
    (cond ((atom x) nil)
          ((equal k (car x)) (mbe :logic (ifix acc) :exec acc))
          (t (index-of-aux k (cdr x) (+ 1 (mbe :logic (ifix acc) :exec
                                               acc))))))

  (defun index-of-aux-eq (k x acc)
    (declare (type (integer 0 *) acc)
             (type symbol k))
    (cond ((atom x) nil)
          ((eq k (car x)) (mbe :logic (ifix acc) :exec acc))
          (t (index-of-aux k (cdr x) (+ 1 (mbe :logic (ifix acc) :exec
                                               acc))))))

  (defun index-of-aux-eql (k x acc)
    (declare (type (integer 0 *) acc)
             (xargs :guard (eqlablep k)))
    (cond ((atom x) nil)
          ((eql k (car x)) (mbe :logic (ifix acc) :exec acc))
          (t (index-of-aux k (cdr x) (+ 1 (mbe :logic (ifix acc) :exec acc))))))

  (defthm index-of-aux-eq-normalize
    (equal (index-of-aux-eq k x acc)
           (index-of-aux k x acc)))

  (defthm index-of-aux-eql-normalize
    (equal (index-of-aux-eql k x acc)
           (index-of-aux k x acc)))

  (defund index-of (k x)
    (declare (xargs :guard t
                    :verify-guards nil))
    (mbe :logic (cond ((atom x) nil)
                      ((equal k (car x)) 0)
                      (t (let ((res (index-of k (cdr x))))
                           (and res (+ 1 res)))))
         :exec (cond ((symbolp k) (index-of-aux-eq k x 0))
                     ((eqlablep k) (index-of-aux-eql k x 0))
                     (t (index-of-aux k x 0)))))

  (local (in-theory (enable index-of)))

; Matt K. mod: Beta-reduced the right-hand side; then the first occurrence of
; index-of may be rewritten maintaining IFF.  In community books
; books/centaur/vl2014/util/position.lisp, the lemma
; position-equal-upper-bound-weak-when-stringp failed after ACL2 no longer
; expanded away LETs on right-hand sides of rewrite rules (after v8-0).  That
; seemed to be because ACL2 no longer used an IFF rule,
; acl2::index-of-iff-member, to rewrite (and (index-of k x) ...) to (and
; (member-equal k x) ...) for specific values of k and x.
  (defthm index-of-aux-removal
    (equal (index-of-aux k x acc)
;          (let ((res (index-of k x)))
;            (and res (+ res (ifix acc))))
           (and (index-of k x)
                (+ (index-of k x) (ifix acc)))))

  (verify-guards index-of)

  (defthm position-equal-ac-is-index-of-aux
    (implies (integerp acc)
             (equal (position-equal-ac k x acc)
                    (index-of-aux k x acc))))

  (defthm index-of-iff-member
    (iff (index-of k x)
         (member k x)))

  (defthm integerp-of-index-of
    (iff (integerp (index-of k x))
         (member k x)))

  (defthm natpp-of-index-of
    (iff (natp (index-of k x))
         (member k x)))

  (defthm nth-of-index-when-member
    (implies (member k x)
             (equal (nth (index-of k x) x)
                    k)))

  (defthm index-of-<-len
    (implies (member k x)
             (< (index-of k x) (len x)))
    :rule-classes :linear)

  (defthm index-of-append-first
    (implies (index-of k x)
             (equal (index-of k (append x y))
                    (index-of k x))))

  (defthm index-of-append-second
    (implies (and (not (index-of k x))
                  (index-of k y))
             (equal (index-of k (append x y))
                    (+ (len x) (index-of k y)))))

  (defthm index-of-append-neither
    (implies (and (not (index-of k x))
                  (not (index-of k y)))
             (not (index-of k (append x y)))))

  (defthmd index-of-append-split
    (equal (index-of k (append x y))
           (or (index-of k x)
               (and (index-of k y)
                    (+ (len x) (index-of k y)))))))
