; ACL2 books using the bdd hints
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann
; email:       Matt_Kaufmann@aus.edsr.eds.com
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(set-verify-guards-eagerness 2)

(encapsulate
 ()

; This macro is really just implies, as shown by the local theorem below, but
; it is handy for bdd processing when we want to avoid building bdds for the
; hypotheses of an implies, but rather only want to use those hypotheses in
; order to guarantee that certain variables are Boolean.

(defmacro implies* (x y)
  `(if ,y t (not ,x)))

(local (defthm implies*-is-implies
         (equal (implies a b) (implies* a b))))
)

(defun firstn (n l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp l)
                              (integerp n)
                              (<= 0 n))))
  (cond ((endp l) nil)
        ((zp n) nil)
        (t (cons (car l)
                 (firstn (1- n) (cdr l))))))

(defthm firstn-0
  (equal (firstn 0 rest)
         nil))

(defthm firstn-cons
  (equal (firstn n (cons a rest))
         (if (zp n) nil (cons a (firstn (1- n) rest)))))

(defun restn (n l)
  (declare (xargs :guard (and (true-listp l)
                              (integerp n)
                              (<= 0 n))))
  (if (endp l)
      l
    (if (zp n)
        l
      (restn (1- n) (cdr l)))))

(defthm restn-0
  (equal (restn 0 rest)
         rest))

(defthm restn-cons
  (equal (restn n (cons a rest))
         (if (zp n) (cons a rest) (restn (1- n) rest))))

(defun tree-size (tree)
  (if (atom tree)
      1
    (+ (tree-size (car tree))
       (tree-size (cdr tree)))))

(defthm tree-size-step
  (equal (tree-size (cons a b))
         (+ (tree-size a)
            (tree-size b))))

(defthm tree-size-base
  (equal (tree-size 0)
         1))

(defun tfirstn (list tree)
  (declare (xargs :guard (and (consp tree)
                              (true-listp list))))
  (firstn (tree-size (car tree)) list))

(defun trestn (list tree)
  (declare (xargs :guard (and (consp tree)
                              (true-listp list))))
  (restn (tree-size (car tree)) list))

(defun t-carry (c prop gen)
  (or (and c prop) gen))

(defthm append-cons
  (equal (append (cons a x) y)
         (cons a (append x y))))

(defthm append-nil
  (equal (append nil y)
         y))

; The following macros are handy for reducing the amount of editing necessary
; for translating Nqthm forms into ACL2.

(progn

(defmacro sub1 (x)
  `(1- ,x))

(defmacro nlistp (x)
  `(atom ,x))

(defmacro caddddr (x)
  `(car (cddddr ,x)))

(defmacro cdddddr (x)
  `(cdr (cddddr ,x)))

(defmacro cadddddr (x)
  `(car (cdddddr ,x)))

(defmacro cddddddr (x)
  `(cdr (cdddddr ,x)))

(defmacro caddddddr (x)
  `(car (cddddddr ,x)))

(defmacro cdddddddr (x)
  `(cdr (cddddddr ,x)))

(defmacro quotient (x y)
  `(nonnegative-integer-quotient ,x ,y))

(defmacro remainder (x y)
  `(rem ,x ,y))

(defmacro boolp (x)
  `(booleanp ,x))

(defmacro bvp (x)
  `(boolean-listp ,x))
)

(defun b-buf (x)                 (if x t nil))
(defun b-not (x)                 (not x))
(defun b-nand  (a b)             (not (and a b)))
(defun b-nand3 (a b c)           (not (and a b c)))
(defun b-nand4 (a b c d)         (not (and a b c d)))
(defun b-xor  (a b)              (if a (if b nil t) (if b t nil)))
(defun b-xor3 (a b c)            (b-xor (b-xor a b) c))
(defun b-equv (x y)              (if x (if y t nil) (if y nil t)))
(defun b-equv3 (a b c)           (b-equv a (b-xor b c)))
(defun b-and  (a b)              (and a b))
(defun b-and3 (a b c)            (and a b c))
(defun b-or   (a b)              (or a b))
(defun b-or3  (a b c)            (or a b c))
(defun b-nor  (a b)              (not (or a b)))
(defun b-nor3 (a b c)            (not (or a b c)))
(defun b-if (c a b)              (if c (if a t nil) (if b t nil)))

#| Unfortunately, b-and is not commutative the way it is defined above.
(defthm b-and-comm
  (equal (b-and a b) (b-and b a)))
|#

(defthm b-nand-comm
  (equal (b-nand a b) (b-nand b a)))

(defthm b-xor-comm
  (equal (b-xor a b) (b-xor b a)))

(defthm b-equv-comm
  (equal (b-equv a b) (b-equv b a)))

(defthm b-nor-comm
  (equal (b-nor a b) (b-nor b a)))

(defun v-if (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (nlistp a)
      nil
    (cons (if (if c (car a) (car b)) t nil)
          (v-if c (cdr a) (cdr b)))))

(defthm v-if-base
  (equal (v-if c nil nil)
         nil))

(defthm v-if-step
  (let ((a (cons a0 a1))
        (b (cons b0 b1)))
    (equal (v-if c a b)
           (cons (if c
                     (if a0 t nil)
                   (if b0 t nil))
                 (v-if c a1 b1)))))

(defun v-buf (x)
  (if (nlistp x)
      nil
    (cons (b-buf (car x))
          (v-buf (cdr x)))))

(defthm v-buf-base
  (equal (v-buf nil)
         nil))

(defthm v-buf-step
  (let ((a (cons a0 a1)))
    (equal (v-buf a)
           (cons (b-buf a0)
                 (v-buf a1)))))

(defun boolfix (x)
  (if x t nil))

(defun v-nzerop (x)
  (if (nlistp x)
      nil
      (or (car x)
          (v-nzerop (cdr x)))))

(defthm v-nzerop-base
  (equal (v-nzerop nil)
         nil))

(defthm v-nzerop-step
  (let ((a (cons a0 a1)))
    (equal (v-nzerop a)
           (or a0 (v-nzerop a1)))))

(defun v-zerop (x)
  (not (v-nzerop x)))

(defun nat-to-v (x n)

#|
  (declare (xargs :guard (and (integerp n)
                              (not (< n 0))
                              (rationalp x))))
|#

; Too much trouble at this point.

  (declare (xargs :verify-guards nil))
  (if (zp n)
      nil
    (cons (not (zp (remainder x 2)))
          (nat-to-v (quotient x 2) (sub1 n)))))

(defun make-nils (n)
  (declare (xargs :guard (and (integerp n)
                              (not (< n 0)))))
  (if (zp n)
      nil
    (cons nil (make-nils (1- n)))))

(defthm nat-to-v-0
  (equal (nat-to-v 0 n)
         (make-nils n)))

(defthm fold-plus
  (implies (and (syntaxp (quotep i))
                (syntaxp (quotep j)))
           (equal (+ i j x)
                  (+ (+ i j) x))))

#| We don't really need this any more.
(defthm make-nils-add1
  (equal (make-nils (+ 1 n))
         (if* (zp (+ 1 n))
              nil
              (cons nil (make-nils n))))
  :hints (("Goal" :expand (make-nils (+ 1 n)))))
|#

(defun v-not (x)
  (if (nlistp x)
      nil
    (cons (b-not (car x))
          (v-not (cdr x)))))

(defthm v-not-base
  (equal (v-not nil) nil))

(defthm v-not-step
  (let ((a (cons a0 a1)))
    (equal (v-not a)
           (cons (b-not a0)
                 (v-not a1)))))

(defun v-xor (x y)
  (declare (xargs :guard (true-listp y)))
  (if (nlistp x)
      nil
    (cons (b-xor (car x) (car y))
          (v-xor (cdr x) (cdr y)))))

(defthm v-xor-base
  (equal (v-xor nil x)
         nil))

(defthm v-xor-step
  (let ((a (cons a0 a1))
        (b (cons b0 b1)))
    (equal (v-xor a b)
           (cons (b-xor a0 b0)
                 (v-xor a1 b1)))))

(defun v-or (x y)
  (declare (xargs :guard (true-listp y)))
  (if (nlistp x)
      nil
    (cons (b-or (car x) (car y))
          (v-or (cdr x) (cdr y)))))

(defthm v-or-base
  (equal (v-or nil x)
         nil))

(defthm v-or-step
  (let ((a (cons a0 a1))
        (b (cons b0 b1)))
    (equal (v-or a b)
           (cons (b-or a0 b0)
                 (v-or a1 b1)))))

(defun v-and (x y)
  (declare (xargs :guard (true-listp y)))
  (if (nlistp x)
      nil
    (cons (b-and (car x) (car y))
          (v-and (cdr x) (cdr y)))))

(defthm v-and-base
  (equal (v-and nil x)
         nil))

(defthm v-and-step
  (let ((a (cons a0 a1))
        (b (cons b0 b1)))
    (equal (v-and a b)
           (cons (b-and a0 b0)
                 (v-and a1 b1)))))

(defthm consp-cons
  (equal (consp (cons x y)) t))

(defthm nth-cons
  (equal (nth n (cons a x))
         (if* (zp n)
              a
              (nth (- n 1) x))))

(defthm len-cons
  (equal (len (cons a x))
         (+ 1 (len x))))

(defthm len-nil
  (equal (len nil) 0))

(defthm if*-hide
  (implies (equal x y)
           (equal x (if* test y (hide x))))
  :hints (("Goal" :expand (hide x)))
  :rule-classes nil)

(defun v-equal (x y)
  (if (nlistp x)
      (and (equal x nil) (equal y nil))
    (and (consp y)
         (equal (car x) (car y))
         (v-equal (cdr x) (cdr y)))))

(defthm v-equal-base
  (equal (v-equal nil x)
         (equal x nil)))

(defthm v-equal-step
  (let ((a (cons a0 a1))
        (b (cons b0 b1)))
    (equal (v-equal a b)
           (and (equal a0 b0)
                (v-equal a1 b1)))))

(defun vcond-macro (clauses)

; From ACL2 cond-macro.

  (declare (xargs :guard (cond-clausesp clauses)))
  (if (consp clauses)
      (if (eq (car (car clauses)) t)
          (if (cdr (car clauses))
              (car (cdr (car clauses)))
            (car (car clauses)))
        (list 'v-if (car (car clauses))
              (if (cdr (car clauses))
                  (car (cdr (car clauses)))
                (car (car clauses)))
              (vcond-macro (cdr clauses))))
    nil))

(defmacro vcond (&rest clauses)
  (declare (xargs :guard (cond-clausesp clauses)))
  (vcond-macro clauses))

(defun bv2p (a b)
  (and (bvp a)
       (bvp b)
       (equal (len a) (len b))))

(defun v-trunc (x n)
  (declare (xargs :guard (and (bvp x)
                              (integerp n)
                              (not (< n 0)))))
  (if (zp n)
      nil
    (cons (boolfix (car x))
          (v-trunc (cdr x) (1- n)))))

(defthm v-trunc-0
  (equal (v-trunc x 0)
         nil))

(defthm v-trunc-cons
  (equal (v-trunc (cons a x) n)
         (if (zp n)
             nil
           (cons (boolfix a)
                 (v-trunc x (1- n))))))

(defthm len-v-trunc
  (equal (len (v-trunc x y))
         (nfix y)))

(defthm nfix-len
  (equal (nfix (len x))
         (len x)))

(defthm v-trunc-v-buf
  (implies (equal n (len a))
           (equal (v-trunc (v-buf a) n)
                  (v-buf a))))

(defthm len-nat-to-v
  (equal (len (nat-to-v i n))
         (nfix n)))

(defthm len-v-not
  (equal (len (v-not v))
         (len v)))

(defun v-shift-right (a si)
  (if (nlistp a)
      nil
    (append (v-buf (cdr a))
            (cons (boolfix si) nil))))

(encapsulate
 ()

 (local
  (defthm v-trunc-v-shift-right-lemma
    (equal (v-trunc (v-shift-right a c) (len a))
           (v-shift-right a c))))

 (defthm v-trunc-v-shift-right
   (implies (equal n (len a))
            (equal (v-trunc (v-shift-right a c) n)
                   (v-shift-right a c)))
   :hints (("Goal" :in-theory (disable v-shift-right))))
 )

(defthm v-trunc-v-xor
  (implies (equal n (len a))
           (equal (v-trunc (v-xor a b) n)
                  (v-xor a b))))

(encapsulate
 ()

 (local
  (defthm v-trunc-v-or-lemma
    (implies (bv2p a b)
             (equal (v-trunc (v-or a b) (len a))
                    (v-or a b)))))

 (defthm v-trunc-v-or
   (implies (and (bv2p a b)
                 (equal n (len a)))
            (equal (v-trunc (v-or a b) n)
                   (v-or a b)))))

(defthm v-trunc-v-not
  (implies (equal n (len a))
           (equal (v-trunc (v-not a) n)
                  (v-not a))))

(defthm len-v-buf
  (equal (len (v-buf v))
         (len v)))

(defthm len-v-xor
  (equal (len (v-xor a b))
         (len a)))

(defthm len-v-and
  (equal (len (v-and a b))
         (len a)))

(defthm len-v-or
  (equal (len (v-or a b))
         (len a)))

; We probably don't need to prove any lemmas about make-tree; we expect to use
; it applied to specific n.

(defun make-tree (n)
  (declare (xargs :guard (and (integerp n)
                              (not (< n 0)))))
  (if (zp n)
      0
    (if (= n 1)
        0
      (cons (make-tree (quotient n 2))
            (make-tree (- n (quotient n 2)))))))

