; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "MILAWA")
(include-book "expt")
(include-book "dividesp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(local (in-theory (enable definition-of-bitwise-and)))


(defthm natp-of-bitwise-and
  (equal (natp (bitwise-and a b))
         t))

(defthm bitwise-and-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (bitwise-and a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm bitwise-and-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (bitwise-and a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm |(bitwise-and 0 a)|
  (equal (bitwise-and 0 a)
         0))

(defthm |(bitwise-and a 0)|
  (equal (bitwise-and a 0)
         0))

;; (defthm |(bitwise-and 1 a)|
;;   (equal (bitwise-and 1 a)
;;          (not (dividesp 2 a)))
;;   :hints(("Goal" :in-theory (enable dividesp))))





(defthm natp-of-bitwise-or
  (equal (natp (bitwise-or a b))
         t)
  :hints(("Goal" :in-theory (enable definition-of-bitwise-or))))

(defthm natp-of-bitwise-xor
  (equal (natp (bitwise-xor a b))
         t)
  :hints(("Goal" :in-theory (enable definition-of-bitwise-xor))))

(defthm booleanp-of-bitwise-nth
  (equal (booleanp (bitwise-nth a b))
         t)
  :hints(("Goal" :in-theory (enable definition-of-bitwise-nth))))

