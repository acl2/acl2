; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

#|

 set-order.lisp

   This is a top level file which you should use if you intend to
   reason about the set order.  Normally you should not do this,
   but you might need it if you want to argue "from first principles"
   that list operations create sets, i.e. for efficiency reasons.

   Note that merely including this file will do nothing for you.
   You need to also enable the relavent theories:

      primitive-reasoning
        basic definitions of the primitive functions.  useful if you
        have a very low level proof about the stucture of sets or
        something.  doesn't pertain to the order itself.

      order-reasoning
        properties of the order itself, and its relation to the set
        primitives.  most of the membership level is based on this.

      cons-reasoning
        properties relating cons to sets through the set order.
        this might be useful if you are introducing new "fast"
        functions, based on cons rather than insert to construct
        sets.  it is not easy to reason with.

|#

(in-package "SET")
(set-verify-guards-eagerness 2)
(local (include-book "primitives"))
(local (include-book "membership"))
(local (include-book "fast"))
(include-book "sets")

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))


; -------------------------------------------------------------------
; primitive-reasoning

(deftheory primitive-reasoning
  '(setp
    empty
    head
    tail
    sfix
    insert))



; -------------------------------------------------------------------
; order-reasoning

;;; Replaced by Matt K. after Jared D.'s modification
;;; in svn 1015 of that book, since there is now a conflict:
(include-book "misc/total-order" :dir :system)
#||
(defthmd <<-type
  (or (equal (<< a b) t)
      (equal (<< a b) nil))
  :rule-classes :type-prescription)

(defthmd <<-irreflexive
  (not (<< a a)))

(defthmd <<-transitive
  (implies (and (<< a b) (<< b c))
           (<< a c)))

(defthmd <<-asymmetric
  (implies (<< a b)
           (not (<< b a))))

(defthmd <<-trichotomy
  (implies (and (not (<< b a))
                (not (equal a b)))
           (<< a b)))
||#

(defthmd head-insert
  (equal (head (insert a X))
         (cond ((empty X) a)
               ((<< a (head X)) a)
               (t (head X)))))

(defthmd tail-insert
  (equal (tail (insert a X))
         (cond ((empty X) (sfix X))
               ((<< a (head X)) (sfix X))
               ((equal a (head X)) (tail X))
               (t (insert a (tail X))))))

(defthmd head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthmd head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

(deftheory order-reasoning
  '(; <<-type ; see comment above about svn 1015
    <<-irreflexive
    <<-transitive
    <<-asymmetric
    <<-trichotomy
    (:induction insert)
    head-insert
    tail-insert
    head-tail-order
    head-tail-order-contrapositive))

; -------------------------------------------------------------------
; cons-reasoning

(defthmd cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X)))))

(defthmd cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a)))

(defthmd cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X))))

(defthmd cons-to-insert-nonempty
  (implies (and (setp X)
                (<< a (head X)))
           (equal (cons a X) (insert a X))))

(defthmd cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))

(deftheory cons-reasoning
  '(cons-set
    cons-head
    cons-to-insert-empty
    cons-to-insert-nonempty
    cons-in))

