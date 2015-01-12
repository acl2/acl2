; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

(in-package "ACL2")

;bzo many of the rules below suggest analogous logbitp rules.  Someone should
;try to add those rules to logbitp.lisp.  And vice-versa!

(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic"))
;(include-book "ash")

(defthm logbit-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logbit pos i)
                  0))
  :hints
  (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-zero
  (equal (logbit pos 0)
         0)
  :hints (("Goal" :in-theory (enable logbit))))

;go the other way too?
(defthm logbitp-forward-to-logbit-one
  (implies (logbitp n x)
           (equal 1 (logbit n x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbitp-forward-to-logbit-zero
  (implies (not (logbitp n x))
           (equal 0 (logbit n x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-when-i-is-non-positive
  (implies (<= i 0)
           (equal (logbit i j)
                  (logcar j)))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-logbit
  (equal (logbit pos1 (logbit pos2 i))
         (if (zp pos1)
             (logbit pos2 i)
           0))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-one
  (equal (logbit pos 1)
         (if (zp pos)
             1
           0))
  :hints (("Goal" :cases ((zp pos))
           :in-theory (enable logbit))))

(defthm unsigned-byte-p-of-logbit
  (implies (< 0 n)
           (equal (unsigned-byte-p n (logbit pos i))
                  (integerp n)))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm unsigned-byte-p-of-logbit-fw
  (unsigned-byte-p 1 (logbit pos i))
  :rule-classes ((:forward-chaining :trigger-terms ((logbit pos i)))))