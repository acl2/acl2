; ACL2 books using the bdd hints
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann
; email:       Matt_Kaufmann@aus.edsr.eds.com
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(include-book "alu")

(defthm tv-alu-help-base
  (equal (tv-alu-help c a b mpg 0)
         (alu-cell c (car a) (car b) mpg)))

(defthm tv-alu-help-step
  (let ((tree (cons tree1 tree2)))
    (equal (tv-alu-help c a b mpg tree)
           (let ((a-car (tfirstn a tree))
                 (b-car (tfirstn b tree))
                 (a-cdr (trestn  a tree))
                 (b-cdr (trestn  b tree)))
             (let ((lhs (tv-alu-help c a-car b-car mpg (car tree))))
               (let ((p-car (car lhs))
                     (g-car (cadr lhs))
                     (sum-car (cddr lhs)))
                 (let ((c-car (t-carry c p-car g-car)))
                   (let ((rhs (tv-alu-help c-car a-cdr b-cdr mpg (cdr tree))))
                     (let ((p-cdr (car rhs))
                           (g-cdr (cadr rhs))
                           (sum-cdr (cddr rhs)))
                       (cons (b-and p-car p-cdr)
                             (cons (t-carry g-car p-cdr g-cdr)
                                   (append sum-car sum-cdr)))))))))))
  :hints (("Goal" :in-theory *s-prop-theory*
           :expand (tv-alu-help c a b mpg (cons tree1 tree2)))))

(defthm v-adder-base
  (equal (v-adder c nil b)
         (cons (boolfix c) nil)))

(defthm v-adder-step
  (let ((a (cons a0 a1))
        (b (cons b0 b1)))
    (equal (v-adder c a b)
           (cons (b-xor3 c a0 b0)
                 (v-adder (b-or (b-and a0 b0)
                                (b-or (b-and a0 c)
                                      (b-and b0 c)))
                          a1 b1)))))

(defun v-alu1 (c a b op)
  (vcond ((v-equal op '(nil nil nil nil)) (cvzbv nil nil (v-buf a)))
         ((v-equal op '(  t nil nil nil)) (cvzbv-inc a))
         ((v-equal op '(nil   t nil nil)) (cvzbv-v-adder c a b))
         ((v-equal op '(  t   t nil nil)) (cvzbv-v-adder nil a b))
         ((v-equal op '(nil nil   t nil)) (cvzbv-neg a))
         ((v-equal op '(t   nil   t nil)) (cvzbv-dec a))
         ((v-equal op '(nil   t   t nil)) (cvzbv-v-subtracter c a b))
         ((v-equal op '(t     t   t nil)) (cvzbv-v-subtracter nil a b))
         ((v-equal op '(nil nil nil   t)) (cvzbv-v-ror c a))
         ((v-equal op '(  t nil nil   t)) (cvzbv-v-asr a))
         ((v-equal op '(nil   t nil   t)) (cvzbv-v-lsr a))
         ((v-equal op '(  t   t nil   t)) (cvzbv nil nil (v-xor a b)))
         ((v-equal op '(nil nil   t   t)) (cvzbv nil nil (v-or  a b)))
         ((v-equal op '(  t nil   t   t)) (cvzbv nil nil (v-and a b)))
         ((v-equal op '(nil   t   t   t)) (cvzbv-v-not a))
         (t                 (cvzbv nil nil (v-buf a)))))

(local

(encapsulate
 ()

(defthm v-equal-is-equal
  (equal (v-equal x0 x1)
         (and (true-listp x1)
              (equal x0 x1))))

(defthm v-if-is-if
  (equal (v-if x y z)
         (if x
             (v-trunc y (len y))
           (v-trunc z (len y)))))

(defthm len-cvzbv
  (equal (len (cvzbv x y z))
         (+ 3 (len z))))

(defthm v-trunc-v-adder-output
  (implies (equal n (len a))
           (equal (v-trunc (v-adder-output c a b) n)
                  (v-adder-output c a b))))

(defthm v-trunc-cvzbv-v-adder
  (implies (equal n (+ 3 (len a)))
           (equal (v-trunc (cvzbv-v-adder c a b) n)
                  (cvzbv-v-adder c a b)))
  :hints (("Goal" :in-theory (disable v-adder-output))))

(defthm v-trunc-v-subtracter-output
  (implies (equal n (len a))
           (equal (v-trunc (v-subtracter-output c a b) n)
                  (v-subtracter-output c a b)))
  :hints (("Goal" :in-theory (disable v-adder-output))))

(defthm v-trunc-cvzbv-v-subtracter
  (implies (equal n (+ 3 (len a)))
           (equal (v-trunc (cvzbv-v-subtracter c a b) n)
                  (cvzbv-v-subtracter c a b)))
  :hints (("Goal" :in-theory (disable v-adder-output))))

(defthm v-trunc-cvzbv-v-ror
  (implies (and (boolp c)
                (bvp a)
                (equal n (+ 3 (len a))))
           (equal (v-trunc (cvzbv-v-ror c a) n)
                  (cvzbv-v-ror c a)))
  :hints (("Goal" :in-theory (disable v-shift-right))))

(defthm v-trunc-cvzbv-v-lsr
  (implies (and (bvp a)
                (equal n (+ 3 (len a))))
           (equal (v-trunc (cvzbv-v-lsr a) n)
                  (cvzbv-v-lsr a)))
  :hints (("Goal" :in-theory (disable v-shift-right))))

(defthm v-trunc-cvzbv-v-asr
  (implies (and (bvp a)
                (equal n (+ 3 (len a))))
           (equal (v-trunc (cvzbv-v-asr a) n)
                  (cvzbv-v-asr a)))
  :hints (("Goal" :in-theory (disable v-shift-right))))

(encapsulate
 ()

 (local
  (defthm v-trunc-v-and-lemma
    (implies (bv2p a b)
             (equal (v-trunc (v-and a b) (len a))
                    (v-and a b)))))

 (defthm v-trunc-v-and
   (implies (and (bv2p a b)
                 (equal n (len a)))
            (equal (v-trunc (v-and a b) n)
                   (v-and a b))))
 )

(defthm v-trunc-cvzbv-v-not
  (implies (equal n (+ 3 (len a)))
           (equal (v-trunc (cvzbv-v-not a) n)
                  (cvzbv-v-not a))))

(defthm len-v-adder-output
  (equal (len (v-adder-output c a b))
         (len a)))

(defthm len-cvzbv-v-adder
  (equal (len (cvzbv-v-adder c a b))
         (+ 3 (len a))))

(defthm len-cvzbv-v-subtracter
  (equal (len (cvzbv-v-subtracter c a b))
         (+ 3 (len a)))
  :hints (("Goal" :in-theory (disable v-adder-output))))

(defthm len-cvzbv-v-ror
  (equal (len (cvzbv-v-ror c a))
         (+ 3 (len a))))

(defthm len-cvzbv-v-lsr
  (equal (len (cvzbv-v-lsr a))
         (+ 3 (len a))))

(defthm len-cvzbv-v-asr
  (equal (len (cvzbv-v-asr a))
         (+ 3 (len a))))

(defthm len-cvzbv-v-not
  (equal (len (cvzbv-v-not x))
         (+ 3 (len x))))

))

(defthm v-alu-is-v-alu1
  (implies (and (bv2p a b)
                (boolp c))
           (equal (v-alu c a b op)
                  (v-alu1 c a b op)))
  :hints (("Goal" :in-theory
           (disable ;;cvzbv
                    ;;cvzbv-inc
                    cvzbv-v-adder
                    ;;cvzbv-neg
                    ;;cvzbv-dec
                    cvzbv-v-subtracter
                    cvzbv-v-ror
                    cvzbv-v-asr
                    cvzbv-v-lsr
                    v-xor
                    v-or
                    v-and
                    cvzbv-v-not
                    v-buf
                    v-equal v-equal-step
                    nat-to-v-0))))

(defthm v-alu-is-v-alu1-unconditional
  (equal (v-alu c a b op)
         (if* (and (bv2p a b)
                   (boolp c))
              (v-alu1 c a b op)
              (hide (v-alu c a b op))))
  :hints (("Goal" :in-theory (disable v-alu1 v-alu bv2p)
           :expand (hide (v-alu c a b op)))))

(in-theory (disable v-alu-is-v-alu1))

(local (in-theory (disable v-if-is-if)))

(defthm core-alu-is-v-alu-2

; Try proving this without :bdd hint!!

  (let* ((a (list a0 a1))
         (b (list b0 b1))
         (tree '(0 . 0))
         (op (list op0 op1 op2 op3))
         (zero nil)
         (mpg (mpg (cons zero (cons nil op)))))
    (implies* ;note: implies works too
     (and (boolp a0) (boolp a1) (boolp b0) (boolp b1) (boolp c)
          (bvp op))
     (equal (core-alu (carry-in-help (cons c (cons nil op)))
                      a b zero mpg op tree)
            (v-alu c a b op))))
  :hints (("Goal" :bdd (:vars t)))
  :rule-classes nil)

#| A useful utility in creating :vars entries below.
(defun shuffle (lst1 lst2)
  (declare (xargs :verify-guards nil))
  (cond
   ((atom lst1) nil)
   (t (list* (car lst1) (car lst2) (shuffle (cdr lst1) (cdr lst2))))))
|#

(defthm core-alu-is-v-alu-8

; Based on core-alu-is-v-alu.

  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7))
         (op (list op0 op1 op2 op3))
         (zero nil)
         (mpg (mpg (cons zero (cons nil op)))))
    (implies* (and (bvp a) (bvp b) (bvp op) (boolp c))
              (equal (core-alu (carry-in-help (cons c (cons nil op)))
                               a b zero mpg op (make-tree 8))
                     (v-alu c a b op))))
  :hints (("Goal" :bdd
           (:vars (op0 op1 op2 op3 c
                       b7 a7 b6 a6 b5 a5 b4 a4 b3 a3 b2 a2 b1 a1 b0 a0))))
  :rule-classes nil)

(defthm core-alu-is-v-alu-16
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a10 a11 a12 a13 a14 a15 a16 a17))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b10 b11 b12 b13 b14 b15 b16 b17))
         (op (list op0 op1 op2 op3))
         (zero nil)
         (mpg (mpg (cons zero (cons nil op)))))
    (implies* (and (bvp a) (bvp b) (bvp op) (boolp c))
              (equal (core-alu (carry-in-help (cons c (cons nil op)))
                               a b zero mpg op (make-tree 16))
                     (v-alu c a b op))))
  :hints (("Goal" :bdd
           (:vars (op0 op1 op2 op3 c
                       b17 a17 b16 a16 b15 a15 b14 a14 b13 a13 b12 a12 b11 a11
                       b10 a10 b7 a7 b6 a6 b5 a5 b4 a4 b3 a3 b2 a2 b1 a1 b0
                       a0))))
  :rule-classes nil)

(defthm core-alu-is-v-alu-32
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a10 a11 a12 a13 a14 a15 a16 a17
                  a20 a21 a22 a23 a24 a25 a26 a27
                  a30 a31 a32 a33 a34 a35 a36 a37))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b10 b11 b12 b13 b14 b15 b16 b17
                  b20 b21 b22 b23 b24 b25 b26 b27
                  b30 b31 b32 b33 b34 b35 b36 b37))
         (op (list op0 op1 op2 op3))
         (zero nil)
         (mpg (mpg (cons zero (cons nil op)))))
    (implies* (and (bvp a) (bvp b) (bvp op) (boolp c))
              (equal (core-alu (carry-in-help (cons c (cons nil op)))
                               a b zero mpg op (make-tree 32))
                     (v-alu c a b op))))
  :hints (("Goal" :bdd
           (:vars (op0 op1 op2 op3 c
                       b37 a37 b36 a36 b35 a35 b34 a34 b33 a33 b32 a32 b31 a31
                       b30 a30
                       b27 a27 b26 a26 b25 a25 b24 a24 b23 a23 b22 a22 b21 a21
                       b20 a20
                       b17 a17 b16 a16 b15 a15 b14 a14 b13 a13 b12 a12 b11 a11
                       b10 a10
                       b7 a7 b6 a6 b5 a5 b4 a4 b3 a3 b2 a2 b1 a1 b0 a0))))
  :rule-classes nil)

#|

The next two events are just the equivalence problem for wider and wider word
sizes, namely 64 and 128.  These events require prodigious amounts of virtual
memory.  The 64-bit problem has been successfully done on a machine with 64 MB
of RAM but has failed on a machine with 50 MB of virtual memory.  The 128-bit
event has succeeded on a 128MB RAM machine but failed on a 64MB machine.

In addition, our Allegro image at CLI cannot handle the space requirements
generated by 128-bit event.  Here is the error message produced by Allegro:

 7493032 bytes have been tenured, next gc will be global.
 See the documentation for variable EXCL:*GLOBAL-GC-BEHAVIOR* for more information.
 Error: An explicit gc call caused a need for 16515072 more bytes of
        heap.  This would exceed the image size limit set at the initial
        build.
   [condition type: STORAGE-CONDITION]


(defthm core-alu-is-v-alu-64
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
         (op (list op0 op1 op2 op3))
         (zero nil)
         (mpg (mpg (cons zero (cons nil op)))))
    (implies* (and (bvp a) (bvp b) (bvp op) (boolp c))
              (equal (core-alu (carry-in-help (cons c (cons nil op)))
                               a b zero mpg op (make-tree 64))
                     (v-alu c a b op))))
  :hints (("Goal" :bdd
           (:vars (op0 op1 op2 op3 c
                       b77 a77 b76 a76
                       b75 a75 b74 a74 b73 a73 b72 a72 b71 a71
                       b70 a70 b67 a67 b66 a66 b65 a65 b64 a64
                       b63 a63 b62 a62 b61 a61 b60 a60 b57 a57
                       b56 a56 b55 a55 b54 a54 b53 a53 b52 a52
                       b51 a51 b50 a50 b47 a47 b46 a46 b45 a45
                       b44 a44 b43 a43 b42 a42 b41 a41 b40 a40
                       b37 a37 b36 a36 b35 a35 b34 a34 b33 a33
                       b32 a32 b31 a31 b30 a30 b27 a27 b26 a26
                       b25 a25 b24 a24 b23 a23 b22 a22 b21 a21
                       b20 a20 b17 a17 b16 a16 b15 a15 b14 a14
                       b13 a13 b12 a12 b11 a11 b10 a10 b7 a7 b6
                       a6 b5 a5 b4 a4 b3 a3 b2 a2 b1 a1 b0 a0))))
  :rule-classes nil)

(defthm core-alu-is-v-alu-128
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a10 a11 a12 a13 a14 a15 a16 a17
                  a20 a21 a22 a23 a24 a25 a26 a27
                  a30 a31 a32 a33 a34 a35 a36 a37
                  a40 a41 a42 a43 a44 a45 a46 a47
                  a50 a51 a52 a53 a54 a55 a56 a57
                  a60 a61 a62 a63 a64 a65 a66 a67
                  a70 a71 a72 a73 a74 a75 a76 a77
                  c0 c1 c2 c3 c4 c5 c6 c7
                  c10 c11 c12 c13 c14 c15 c16 c17
                  c20 c21 c22 c23 c24 c25 c26 c27
                  c30 c31 c32 c33 c34 c35 c36 c37
                  c40 c41 c42 c43 c44 c45 c46 c47
                  c50 c51 c52 c53 c54 c55 c56 c57
                  c60 c61 c62 c63 c64 c65 c66 c67
                  c70 c71 c72 c73 c74 c75 c76 c77))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b10 b11 b12 b13 b14 b15 b16 b17
                  b20 b21 b22 b23 b24 b25 b26 b27
                  b30 b31 b32 b33 b34 b35 b36 b37
                  b40 b41 b42 b43 b44 b45 b46 b47
                  b50 b51 b52 b53 b54 b55 b56 b57
                  b60 b61 b62 b63 b64 b65 b66 b67
                  b70 b71 b72 b73 b74 b75 b76 b77
                  d0 d1 d2 d3 d4 d5 d6 d7
                  d10 d11 d12 d13 d14 d15 d16 d17
                  d20 d21 d22 d23 d24 d25 d26 d27
                  d30 d31 d32 d33 d34 d35 d36 d37
                  d40 d41 d42 d43 d44 d45 d46 d47
                  d50 d51 d52 d53 d54 d55 d56 d57
                  d60 d61 d62 d63 d64 d65 d66 d67
                  d70 d71 d72 d73 d74 d75 d76 d77))
         (op (list op0 op1 op2 op3))
         (zero nil)
         (mpg (mpg (cons zero (cons nil op)))))
    (implies* (and (bvp a) (bvp b) (bvp op) (boolp c))
              (equal (core-alu (carry-in-help (cons c (cons nil op)))
                               a b zero mpg op (make-tree 128))
                     (v-alu c a b op))))
  :hints (("Goal" :bdd
           (:vars (op0 op1 op2 op3 c
                       d77 c77 d76 c76 d75 c75 d74 c74
                       d73 c73 d72 c72 d71 c71 d70 c70 d67 c67
                       d66 c66 d65 c65 d64 c64 d63 c63 d62 c62
                       d61 c61 d60 c60 d57 c57 d56 c56 d55 c55
                       d54 c54 d53 c53 d52 c52 d51 c51 d50 c50
                       d47 c47 d46 c46 d45 c45 d44 c44 d43 c43
                       d42 c42 d41 c41 d40 c40 d37 c37 d36 c36
                       d35 c35 d34 c34 d33 c33 d32 c32 d31 c31
                       d30 c30 d27 c27 d26 c26 d25 c25 d24 c24
                       d23 c23 d22 c22 d21 c21 d20 c20 d17 c17
                       d16 c16 d15 c15 d14 c14 d13 c13 d12 c12
                       d11 c11 d10 c10 d7 c7 d6 c6 d5 c5 d4 c4
                       d3 c3 d2 c2 d1 c1 d0 c0 b77 a77 b76 a76
                       b75 a75 b74 a74 b73 a73 b72 a72 b71 a71
                       b70 a70 b67 a67 b66 a66 b65 a65 b64 a64
                       b63 a63 b62 a62 b61 a61 b60 a60 b57 a57
                       b56 a56 b55 a55 b54 a54 b53 a53 b52 a52
                       b51 a51 b50 a50 b47 a47 b46 a46 b45 a45
                       b44 a44 b43 a43 b42 a42 b41 a41 b40 a40
                       b37 a37 b36 a36 b35 a35 b34 a34 b33 a33
                       b32 a32 b31 a31 b30 a30 b27 a27 b26 a26
                       b25 a25 b24 a24 b23 a23 b22 a22 b21 a21
                       b20 a20 b17 a17 b16 a16 b15 a15 b14 a14
                       b13 a13 b12 a12 b11 a11 b10 a10 b7 a7 b6
                       a6 b5 a5 b4 a4 b3 a3 b2 a2 b1 a1 b0 a0))))
  :rule-classes nil)

|#
