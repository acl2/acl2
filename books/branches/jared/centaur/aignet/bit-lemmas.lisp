; AIGNET - And-Inverter Graph Networks
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

(defthm b-xor-same-2
  (equal (b-xor a (b-xor a b))
         (bfix b))
  :hints(("Goal" :in-theory (enable b-xor))))
