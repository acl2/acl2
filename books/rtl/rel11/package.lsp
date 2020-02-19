; Copyright (C) 2015, ForrestHunt, Inc.
; Written by Matt Kaufmann, March, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defpkg "RTL"
  (union-eq
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   STD::*std-exports*
   '(defxdoc defsection
      rtl ; simplifies dealing with this xdoc topic name
      *default-step-limit* ; should perhaps be in *acl2-exports*
      binary-logand binary-logior binary-logxor binary-logeqv ; used in lib/log.lisp
      b*
      def-gl-rule
      def-gl-thm
      find-lemmas
      nonlinearp-default-hint
      nonlinearp-default-hint++
      proof-by-arith
      a b c d e f g h i j k l m n o p q r s t u v w x y z
      a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1
      n1 o1 p1 q1 r1 s1 t1 u1 v1 w1 x1 y1 z1
      a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2
      n2 o2 p2 q2 r2 s2 t2 u2 v2 w2 x2 y2 z2)))
