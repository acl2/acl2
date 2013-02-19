; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

(include-book "centaur/bitops/ihsext-basics" :dir :system)


(defthm b-xor-lemma1
  (equal
   (B-XOR
    a
    (B-NOT
     (B-XOR
      b a)))
   (b-not b))
  :hints(("Goal" :in-theory (enable b-xor b-not))))

(defthm b-xor-lemma2
  (equal (B-XOR
          (B-NOT a)
          (B-XOR
           a b))
         (b-not b))
  :hints(("Goal" :in-theory (enable b-xor b-not))))

(defthm b-xor-lemma3
  (equal (B-XOR
          a
          (B-XOR
           b a))
         (bfix b))
  :hints(("Goal" :in-theory (enable b-xor))))

(defthm b-xor-lemma4
  (equal (B-XOR
          (B-XOR a b)
          (B-XOR a c))
         (b-xor b c))
  :hints(("Goal" :in-theory (enable b-xor))))

(table invisible-fns-table 'acl2::bfix$inline '(acl2::b-not$inline))

(defthm associativity-of-b-xor
  (equal (b-xor (b-xor a b) c)
         (b-xor a (b-xor b c)))
  :hints(("Goal" :in-theory (enable b-xor b-not))))

(defthm commutativity-2-of-b-xor
  (equal (b-xor a (b-xor b c))
         (b-xor b (b-xor a c)))
  :hints(("Goal" :in-theory (enable b-xor b-not)))
  :rule-classes ((:rewrite :loop-stopper ((a b acl2::bfix$inline)))))

