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

; Here we verify propagate-generate adders of various widths using OBDDs, based
; on Nqthm definitions given to us by Warren Hunt.

(include-book "bdd-primitives")

(set-verify-guards-eagerness 2)

(defun v-propagate (a b)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b)
                              (equal (length a) (length b)))))
  (if (endp a)
      t
    (and (or (car a) (car b))
         (v-propagate (cdr a) (cdr b)))))

(defthm v-propagate-step
  (equal (v-propagate (cons a0 a1) (cons b0 b1))
         (and (or a0 b0)
              (v-propagate a1 b1))))

(defthm v-propagate-base
  (equal (v-propagate nil nil)
         t))

(defun v-generate (a b)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b)
                              (equal (length a) (length b)))))
  (if (endp a)
      nil
    (or (v-generate (cdr a) (cdr b))
        (and (car a) (car b) (v-propagate (cdr a) (cdr b))))))

(defthm v-generate-step
  (equal (v-generate (cons a0 a1) (cons b0 b1))
         (or (v-generate a1 b1)
             (and a0 b0 (v-propagate a1 b1)))))

(defthm v-generate-base
  (equal (v-generate nil nil)
         nil))

(defun tv-adder (c a b tree)
  (declare (xargs :verify-guards nil))
  (if (atom tree)
      (list (or (car a) (car b))
            (and (car a) (car b))
            (b-xor (car a) (b-xor (car b) c)))
    (let ((lhs (tv-adder c
                         (tfirstn a tree)
                         (tfirstn b tree)
                         (car tree))))
      (let ((lhs-p (car lhs))
            (lhs-g (cadr lhs))
            (lhs-sum (cddr lhs)))
        (let ((rhs-c (t-carry c lhs-p lhs-g)))
          (let ((rhs (tv-adder rhs-c
                               (trestn a tree)
                               (trestn b tree)
                               (cdr tree))))
            (let ((rhs-p (car rhs))
                  (rhs-g (cadr rhs))
                  (rhs-sum (cddr rhs)))
              (let ((p (and lhs-p rhs-p))
                    (g (t-carry lhs-g rhs-p rhs-g)))
                (cons p (cons g (append lhs-sum rhs-sum)))))))))))

(defthm tv-adder-step
  (let ((tree (cons left right)))
    (equal (tv-adder c a b tree)
           (let ((lhs (tv-adder c
                                (tfirstn a tree)
                                (tfirstn b tree)
                                (car tree))))
             (let ((lhs-p (car lhs))
                   (lhs-g (cadr lhs))
                   (lhs-sum (cddr lhs)))
               (let ((rhs-c (t-carry c lhs-p lhs-g)))
                 (let ((rhs (tv-adder rhs-c
                                      (trestn a tree)
                                      (trestn b tree)
                                      (cdr tree))))
                   (let ((rhs-p (car rhs))
                         (rhs-g (cadr rhs))
                         (rhs-sum (cddr rhs)))
                     (let ((p (and lhs-p rhs-p))
                           (g (t-carry lhs-g rhs-p rhs-g)))
                       (cons p (cons g (append lhs-sum rhs-sum))))))))))))

(defthm tv-adder-base
  (equal (tv-adder c a b 0)
         (list (or (car a) (car b))
               (and (car a) (car b))
               (b-xor (car a) (b-xor (car b) c)))))

(defun v-sum (c a b)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b)
                              (equal (length a) (length b)))))
  (if (endp a)
      nil
    (cons (b-xor c (b-xor (car a) (car b)))
          (v-sum (or (and (car a) (car b))
                     (and (car a) c)
                     (and (car b) c))
                 (cdr a)
                 (cdr b)))))

(defthm v-sum-step
  (equal (v-sum c (cons a0 a1) (cons b0 b1))
         (cons (b-xor c (b-xor a0 b0))
               (v-sum (or (and a0 b0)
                          (and a0 c)
                          (and b0 c))
                      a1 b1))))

(defthm v-sum-base
  (equal (v-sum c nil nil)
         nil))

;;; Run some tests

(local (encapsulate ()

(defthm tv-adder-correct-8
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7))
         (tree4 '((0 . 0) . (0 . 0)))
         (tree8 (cons tree4 tree4)))
    (implies* (and (boolean-listp a)
                   (boolean-listp b)
                   (booleanp c))
              (equal (tv-adder c a b tree8)
                     (cons (v-propagate a b)
                           (cons (v-generate a b)
                                 (v-sum c a b))))))
  :hints (("Goal" :bdd
           (:vars (c a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7))))
  :rule-classes nil)

(defthm tv-adder-correct-16
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a10 a11 a12 a13 a14 a15 a16 a17))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b10 b11 b12 b13 b14 b15 b16 b17))
         (tree4 '((0 . 0) . (0 . 0)))
         (tree8 (cons tree4 tree4))
         (tree16 (cons tree8 tree8)))
    (implies* (and (boolean-listp a)
                   (boolean-listp b)
                   (booleanp c))
              (equal (tv-adder c a b tree16)
                     (cons (v-propagate a b)
                           (cons (v-generate a b)
                                 (v-sum c a b))))))
  :hints (("Goal" :bdd
           (:vars (c a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
                     a10 b10 a11 b11 a12 b12 a13 b13 a14 b14 a15 b15 a16 b16
                     a17 b17))))
  :rule-classes nil)

(defthm tv-adder-correct-32
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a10 a11 a12 a13 a14 a15 a16 a17
                  a20 a21 a22 a23 a24 a25 a26 a27
                  a30 a31 a32 a33 a34 a35 a36 a37))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b10 b11 b12 b13 b14 b15 b16 b17
                  b20 b21 b22 b23 b24 b25 b26 b27
                  b30 b31 b32 b33 b34 b35 b36 b37))
         (tree4 '((0 . 0) . (0 . 0)))
         (tree8 (cons tree4 tree4))
         (tree16 (cons tree8 tree8))
         (tree32 (cons tree16 tree16)))
    (implies* (and (boolean-listp a)
                   (boolean-listp b)
                   (booleanp c))
              (equal (tv-adder c a b tree32)
                     (cons (v-propagate a b)
                           (cons (v-generate a b)
                                 (v-sum c a b))))))
  :hints (("Goal" :bdd
           (:vars (c a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
                     a10 b10 a11 b11 a12 b12 a13 b13 a14 b14 a15 b15 a16 b16
                     a17 b17
                     a20 b20 a21 b21 a22 b22 a23 b23 a24 b24 a25 b25 a26 b26
                     a27 b27
                     a30 b30 a31 b31 a32 b32 a33 b33 a34 b34 a35 b35 a36 b36
                     a37 b37))))
  :rule-classes nil)

(defthm tv-adder-correct-64
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a10 a11 a12 a13 a14 a15 a16 a17
                  a20 a21 a22 a23 a24 a25 a26 a27
                  a30 a31 a32 a33 a34 a35 a36 a37
                  a40 a41 a42 a43 a44 a45 a46 a47
                  a50 a51 a52 a53 a54 a55 a56 a57
                  a60 a61 a62 a63 a64 a65 a66 a67
                  a70 a71 a72 a73 a74 a75 a76 a77))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b10 b11 b12 b13 b14 b15 b16 b17
                  b20 b21 b22 b23 b24 b25 b26 b27
                  b30 b31 b32 b33 b34 b35 b36 b37
                  b40 b41 b42 b43 b44 b45 b46 b47
                  b50 b51 b52 b53 b54 b55 b56 b57
                  b60 b61 b62 b63 b64 b65 b66 b67
                  b70 b71 b72 b73 b74 b75 b76 b77))
         (tree4 '((0 . 0) . (0 . 0)))
         (tree8 (cons tree4 tree4))
         (tree16 (cons tree8 tree8))
         (tree32 (cons tree16 tree16))
         (tree64 (cons tree32 tree32)))
    (implies* (and (boolean-listp a)
                   (boolean-listp b)
                   (booleanp c))
              (equal (tv-adder c a b tree64)
                     (cons (v-propagate a b)
                           (cons (v-generate a b)
                                 (v-sum c a b))))))
  :hints (("Goal" :bdd
           (:vars (c a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
                     a10 b10 a11 b11 a12 b12 a13 b13 a14 b14 a15 b15 a16 b16
                     a17 b17
                     a20 b20 a21 b21 a22 b22 a23 b23 a24 b24 a25 b25 a26 b26
                     a27 b27
                     a30 b30 a31 b31 a32 b32 a33 b33 a34 b34 a35 b35 a36 b36
                     a37 b37
                     a40 b40 a41 b41 a42 b42 a43 b43 a44 b44 a45 b45 a46 b46
                     a47 b47
                     a50 b50 a51 b51 a52 b52 a53 b53 a54 b54 a55 b55 a56 b56
                     a57 b57
                     a60 b60 a61 b61 a62 b62 a63 b63 a64 b64 a65 b65 a66 b66
                     a67 b67
                     a70 b70 a71 b71 a72 b72 a73 b73 a74 b74 a75 b75 a76 b76
                     a77 b77))))
  :rule-classes nil)
))
